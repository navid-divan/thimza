"""Thimza: a three-round threshold signature whose signatures are Raccoon signatures.

Round 1 is free of the signer set: it commits to the truncated commitment.
Round 2 binds the signer set and the first round commitments that the signer received,
          stores their digest in the token, and opens the truncated commitment.
Round 3 checks the openings against the stored digest and the commitments, derives the
          challenge and the view-derived antisymmetric mask, responds, and erases the token.
Combine and Verify are the Raccoon combiner and verifier.
"""
import numpy as np
from ..ring import hi_bits
from ..core import RaccoonCore
from ..prf import xof, pack_bits
from ..masking import gen_seeds_pairwise, antisymmetric_mask
from ..shamir import share, lagrange, scalar_mul

U64 = np.uint64


class Abort(Exception):
    """Raised when an honest signer refuses a request."""


class Token:
    """Session-bounded state of one signer: created in round 1, erased after round 3."""
    __slots__ = ('i', 'msg', 'r', 'wbar', 'cmt', 'digest', 'T', 'phase')

    def __init__(self, i, msg, r, wbar, cmt):
        self.i, self.msg, self.r, self.wbar, self.cmt = i, msg, r, wbar, cmt
        self.digest, self.T, self.phase = None, None, 1

    def erase(self):
        self.r = None
        self.wbar = None
        self.digest = None
        self.phase = 0


class Thimza:
    name = 'Thimza'
    rounds = 3
    online_rounds = 3
    assumption = 'MLWE + SelfTargetMSIS'
    interchangeable = True

    def __init__(self, P, seed=None):
        self.P = P
        self.C = RaccoonCore(P, seed)
        self.nu_c = P['nu_c']
        self.q = self.C.q
        self.R = self.C.R
        self.hbytes = P.get('n_H', 640) // 8
        self.seed_bytes = P.get('seed_bytes', 32)
        self.wbits = int((self.q >> self.nu_c)).bit_length()

    # ------------------------------------------------------------------ keys
    def keygen(self, t, n):
        C = self.C
        C.setup()
        s = C.smp.gaussian((C.ell, C.phi), C.sigma_t)
        e = C.smp.gaussian((C.k, C.phi), C.sigma_t)
        t_pk = C.pk_from_secret(C.R.ntt(s), e)
        shares = share(s, t, n, self.q, C.smp)
        seeds = gen_seeds_pairwise(n, C.smp.rng, self.seed_bytes)
        vk_bytes = xof('thimza/vk', C.Ahat_seed, t_pk, outlen=self.hbytes)
        self.vk = (C.Ahat_seed, t_pk, vk_bytes)
        # The full secret is kept only by this test harness for the correctness checks;
        # signers use their own share and seeds.
        self.sk = dict(shares=shares, seeds=seeds, s=s, e=e)
        self.t_thr = t
        self.n_parties = n
        return self.vk, self.sk

    # --------------------------------------------------------------- hashing
    def _enc_w(self, wbar):
        # injective canonical hash input: coefficients of q_nu_c < 2^16 as little-endian 16-bit words
        dt = np.uint16 if self.wbits <= 16 else np.uint32
        return np.ascontiguousarray(wbar).astype(dt).tobytes()

    def H0(self, msg, j, wbar):
        return xof('thimza/H0', self.vk[2], msg, int(j), self._enc_w(wbar), outlen=self.hbytes)

    def H1(self, msg, T, cmts):
        return xof('thimza/H1', self.vk[2], msg, [int(j) for j in T], b''.join(cmts), outlen=self.hbytes)

    # ---------------------------------------------------------------- rounds
    def round1(self, i, msg):
        """Sign_1(sk_i, msg): fresh token, commitment to the truncated commitment."""
        C = self.C
        r = C.smp.gaussian((C.ell, C.phi), C.sigma_w)
        ep = C.smp.gaussian((C.k, C.phi), C.sigma_w)
        w = C.R.add(C.R.intt(C.R.matmul(C.A_hat, C.R.ntt(r))), ep)
        wbar = hi_bits(w, self.nu_c, self.q)
        cmt = self.H0(msg, i, wbar)
        return Token(i, msg, r, wbar, cmt), cmt

    def round2(self, tok, T, cmts):
        """Sign_2(st_i, T, (cmt_j)_{j in T}): bind the request and open."""
        T = list(T)
        if tok.phase != 1:
            raise Abort('token not in round 1')
        if len(T) != self.t_thr or len(set(T)) != len(T) or any(j < 1 or j > self.n_parties for j in T):
            raise Abort('malformed signer set')
        if tok.i not in T:
            raise Abort('signer not in T')
        if cmts[T.index(tok.i)] != tok.cmt:
            raise Abort('own commitment missing')
        tok.digest = self.H1(tok.msg, T, cmts)
        tok.T = T
        tok.phase = 2
        return tok.wbar

    def round3(self, tok, T, cmts, wbars):
        """Sign_3: check the request and the openings, respond, erase the token."""
        T = list(T)
        C = self.C
        if tok.phase != 2:
            raise Abort('token not in round 2')
        if T != tok.T or self.H1(tok.msg, T, cmts) != tok.digest:
            raise Abort('request differs from round 2')
        for idx, j in enumerate(T):
            if self.H0(tok.msg, j, wbars[idx]) != cmts[idx]:
                raise Abort('opening does not match its commitment')
        if not np.array_equal(np.asarray(wbars[T.index(tok.i)], dtype=U64), tok.wbar):
            raise Abort('own opening altered')
        W = np.zeros((C.k, C.phi), dtype=np.int64)
        sh = np.int64(1 << self.nu_c)
        for wb in wbars:
            W = (W + np.asarray(wb, dtype=np.int64) * sh) % np.int64(self.q)
        qw = self.q >> C.nu_w
        w_agg = hi_bits(W.astype(U64), C.nu_w, self.q) % U64(qw)
        c = C.challenge(self.vk[2], w_agg, tok.msg)
        lam = lagrange(T, tok.i, self.q)
        si = self.sk['shares'][tok.i]
        cs = C.R.intt(C.R.mul(np.broadcast_to(C.R.ntt(c), (C.ell, C.phi)), C.R.ntt(si)))
        zi = C.R.add(scalar_mul(lam, cs, self.q), tok.r)
        M, calls = antisymmetric_mask(tok.i, T, self.sk['seeds'], tok.digest, (C.ell, C.phi), self.q)
        zi = C.R.add(zi, M)
        tok.erase()
        return zi, c, w_agg, calls

    # ------------------------------------------------------- combine, verify
    def combine(self, T, msg, zs, c, w_agg):
        C = self.C
        z = np.zeros((C.ell, C.phi), dtype=np.int64)
        for zi in zs:
            z = (z + np.asarray(zi, dtype=np.int64)) % np.int64(self.q)
        z = z.astype(U64)
        _, t_pk, vkb = self.vk
        Az = C.R.intt(C.R.matmul(C.A_hat, C.R.ntt(z)))
        t_full = ((np.asarray(t_pk, dtype=np.int64) * np.int64(1 << C.nu_t)) % np.int64(self.q)).astype(U64)
        ct = C.R.intt(C.R.mul(np.broadcast_to(C.R.ntt(c), (C.k, C.phi)), C.R.ntt(t_full)))
        base = C.R.sub(Az, ct)
        qw = self.q >> C.nu_w
        hb = hi_bits(base, C.nu_w, self.q) % U64(qw)
        h = (np.asarray(w_agg, dtype=np.int64) - hb.astype(np.int64)) % np.int64(qw)
        h = np.where(h > (qw >> 1), h - np.int64(qw), h)
        return (c, z, h)

    def verify(self, msg, sig, t=None):
        _, t_pk, vkb = self.vk
        return self.C.verify(vkb, t_pk, msg, sig, self.C.signature_bound())

    # ----------------------------------------------------------------- sizes
    def sizes(self, t):
        C = self.C
        lq = self.P['logq']
        r1 = float(self.hbytes)
        r2 = C.k * C.phi * (lq - self.nu_c) / 8.0
        r3 = C.ell * C.phi * lq / 8.0
        return dict(vk=C.size_vk(), sig=C.size_sig(t), r1=r1, r2=r2, r3=r3,
                    total=r1 + r2 + r3, online=r1 + r2 + r3,
                    sk=self.seed_bytes + C.ell * C.phi * lq / 8.0 + self.seed_bytes * (self.n_parties - 1))
