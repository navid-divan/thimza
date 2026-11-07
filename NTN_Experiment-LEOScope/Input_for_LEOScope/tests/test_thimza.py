import os
import sys
import unittest
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from thimza.params import THIMZA
from thimza.schemes.thimza_scheme import Thimza, Abort
from thimza.ring import hi_bits
from thimza.prf import uniform_rq, prf_uniform
from thimza.masking import antisymmetric_mask
from thimza.shamir import reconstruct

U64 = np.uint64
P = THIMZA[128]


def sign_all(S, T, msg, cmts_override=None):
    tok, cm = {}, {}
    for i in T:
        tok[i], cm[i] = S.round1(i, msg)
    cmts = [cm[j] for j in T]
    wb = {i: S.round2(tok[i], T, cmts if cmts_override is None else cmts_override.get(i, cmts)) for i in T}
    zs = []
    for i in T:
        cv = cmts if cmts_override is None else cmts_override.get(i, cmts)
        zi, c, w, _ = S.round3(tok[i], T, cv, [wb[j] for j in T])
        zs.append(zi)
    return S.combine(T, msg, zs, c, w)


def negacyclic(a, b, q):
    """Schoolbook product in Z_q[X]/(X^n + 1) with Python integers, independent of the NTT."""
    n = len(a)
    full = np.convolve(np.array([int(x) for x in a], dtype=object), np.array([int(x) for x in b], dtype=object))
    res = [0] * n
    for i, v in enumerate(full):
        if i < n:
            res[i] += v
        else:
            res[i - n] -= v
    return [x % q for x in res]


def independent_verify(S, msg, sig):
    """Raccoon verification written with schoolbook arithmetic and no shared ring code."""
    C = S.C
    q, n = C.q, C.phi
    c, z, h = sig
    # the matrix is expanded in the NTT domain; bring it to coefficients once, then use
    # schoolbook arithmetic only
    A = C.R.intt(C.A_hat)
    _, t_pk, vkb = S.vk
    base = []
    for r in range(C.k):
        acc = [0] * n
        for col in range(C.ell):
            prod = negacyclic(A[r, col], z[col], q)
            acc = [(x + y) % q for x, y in zip(acc, prod)]
        tfull = [(int(v) << C.nu_t) % q for v in t_pk[r]]
        ct = negacyclic(c, tfull, q)
        base.append([(x - y) % q for x, y in zip(acc, ct)])
    qw = q >> C.nu_w
    w = [[((x + (1 << (C.nu_w - 1))) >> C.nu_w) % qw for x in row] for row in base]
    w = [[(wv + int(hv)) % qw for wv, hv in zip(wr, hr)] for wr, hr in zip(w, h)]
    c2 = C.challenge(vkb, np.array(w, dtype=U64), msg)
    if not np.array_equal(c, c2):
        return False
    zc = [((int(v) + q // 2) % q) - q // 2 for v in np.asarray(z).reshape(-1)]
    hc = [int(v) * (1 << C.nu_w) for v in np.asarray(h).reshape(-1)]
    norm = (sum(x * x for x in zc) + sum(x * x for x in hc)) ** 0.5
    return norm <= C.signature_bound()


class TestThimza(unittest.TestCase):

    def test_correctness(self):
        for (t, n) in [(1, 1), (2, 3), (3, 5), (4, 6), (5, 8), (7, 10)]:
            S = Thimza(P, seed=1000 + 17 * t + n)
            S.keygen(t, n)
            T = list(range(n - t + 1, n + 1))
            sig = sign_all(S, T, b'msg-%d-%d' % (t, n))
            self.assertTrue(S.verify(b'msg-%d-%d' % (t, n), sig), (t, n))

    def test_independent_verifier(self):
        S = Thimza(P, seed=7)
        S.keygen(3, 5)
        T = [1, 3, 5]
        sig = sign_all(S, T, b'interchangeable')
        self.assertTrue(independent_verify(S, b'interchangeable', sig))
        self.assertFalse(independent_verify(S, b'other message', sig))

    def test_reconstruction(self):
        S = Thimza(P, seed=8)
        S.keygen(4, 7)
        for T in ([1, 2, 3, 4], [2, 4, 6, 7], [4, 5, 6, 7]):
            s = reconstruct(T, S.sk['shares'], S.q)
            self.assertTrue(np.array_equal(s, S.sk['s']))

    def test_masks_cancel_on_common_view(self):
        S = Thimza(P, seed=9)
        S.keygen(5, 9)
        T = [1, 3, 4, 7, 9]
        view = b'common-view'
        tot = np.zeros((S.C.ell, S.C.phi), dtype=np.int64)
        for i in T:
            m, calls = antisymmetric_mask(i, T, S.sk['seeds'], view, (S.C.ell, S.C.phi), S.q)
            self.assertEqual(calls, len(T) - 1)
            tot = (tot + m.astype(np.int64)) % S.q
        self.assertFalse(tot.any())

    def test_inconsistent_views_give_invalid_signature(self):
        S = Thimza(P, seed=10)
        S.keygen(3, 4)
        T = [1, 2, 3]
        msg = b'split view'
        tok, cm = {}, {}
        for i in T:
            tok[i], cm[i] = S.round1(i, msg)
        cmts = [cm[j] for j in T]
        # party 3 plays the corrupted signer and equivocates: two valid openings are impossible,
        # so it shows the honest parties two different commitments of its own.
        tok3b, cm3b = S.round1(3, msg)
        view_a = cmts
        view_b = [cm[1], cm[2], cm3b]
        wb1 = S.round2(tok[1], T, view_a)
        wb2 = S.round2(tok[2], T, view_b)
        wb3 = S.round2(tok[3], T, view_a)
        wb3b = S.round2(tok3b, T, view_b)
        z1, c1, w1, _ = S.round3(tok[1], T, view_a, [wb1, wb2, wb3])
        z2, c2, w2, _ = S.round3(tok[2], T, view_b, [wb1, wb2, wb3b])
        z3, _, _, _ = S.round3(tok[3], T, view_a, [wb1, wb2, wb3])
        sig = S.combine(T, msg, [z1, z2, z3], c1, w1)
        self.assertFalse(S.verify(msg, sig))

    def test_opening_must_match_commitment(self):
        S = Thimza(P, seed=11)
        S.keygen(2, 3)
        T = [1, 2]
        tok1, c1 = S.round1(1, b'm')
        tok2, c2 = S.round1(2, b'm')
        S.round2(tok1, T, [c1, c2])
        wb2 = S.round2(tok2, T, [c1, c2])
        bad = wb2.copy()
        bad[0, 0] ^= U64(1)
        with self.assertRaises(Abort):
            S.round3(tok1, T, [c1, c2], [tok1.wbar, bad])

    def test_request_must_match_round_two(self):
        S = Thimza(P, seed=12)
        S.keygen(2, 3)
        tok1, c1 = S.round1(1, b'm')
        tok2, c2 = S.round1(2, b'm')
        tok3, c3 = S.round1(3, b'm')
        S.round2(tok1, [1, 2], [c1, c2])
        wb3 = S.round2(tok3, [1, 3], [c1, c3])
        with self.assertRaises(Abort):
            S.round3(tok1, [1, 3], [c1, c3], [tok1.wbar, wb3])

    def test_token_is_single_use(self):
        S = Thimza(P, seed=13)
        S.keygen(2, 2)
        T = [1, 2]
        tok1, c1 = S.round1(1, b'm')
        tok2, c2 = S.round1(2, b'm')
        wb1 = S.round2(tok1, T, [c1, c2])
        wb2 = S.round2(tok2, T, [c1, c2])
        with self.assertRaises(Abort):
            S.round2(tok1, T, [c1, c2])
        S.round3(tok1, T, [c1, c2], [wb1, wb2])
        with self.assertRaises(Abort):
            S.round3(tok1, T, [c1, c2], [wb1, wb2])
        self.assertIsNone(tok1.r)

    def test_own_commitment_required(self):
        S = Thimza(P, seed=14)
        S.keygen(2, 3)
        tok1, c1 = S.round1(1, b'm')
        tok2, c2 = S.round1(2, b'm')
        fake, _ = S.round1(1, b'm')
        with self.assertRaises(Abort):
            S.round2(tok1, [1, 2], [fake.cmt, c2])

    def test_round_one_is_free_of_signer_set(self):
        S = Thimza(P, seed=15)
        S.keygen(2, 4)
        tok1, c1 = S.round1(1, b'm')
        tok2, c2 = S.round1(2, b'm')
        tok3, c3 = S.round1(3, b'm')
        # the signer set is chosen only after the first round has been sent
        T = [1, 3]
        wb1 = S.round2(tok1, T, [c1, c3])
        wb3 = S.round2(tok3, T, [c1, c3])
        z1, c, w, _ = S.round3(tok1, T, [c1, c3], [wb1, wb3])
        z3, _, _, _ = S.round3(tok3, T, [c1, c3], [wb1, wb3])
        self.assertTrue(S.verify(b'm', S.combine(T, b'm', [z1, z3], c, w)))

    def test_uniform_sampler_range_and_balance(self):
        q = THIMZA[128] and Thimza(P, seed=16).q
        v = uniform_rq(b'seed', (40000,), q)
        self.assertTrue(np.all(v < U64(q)))
        frac = float(np.mean(v < U64(q // 2)))
        self.assertAlmostEqual(frac, 0.5, delta=0.02)
        w = prf_uniform(b'k' * 32, b'x', (4, 512), q)
        self.assertTrue(np.all(w < U64(q)))


if __name__ == '__main__':
    unittest.main(verbosity=2)
