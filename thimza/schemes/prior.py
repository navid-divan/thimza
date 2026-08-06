import math
import numpy as np
from ..ring import hi_bits, find_ntt_prime, Rq
from ..core import RaccoonCore, bits_gauss
from ..prf import xof, uniform_rq, hash_gaussian, hash_monomials, hash_challenge
from ..masking import gen_seeds_ordered, gen_seeds_pairwise, row_column_masks, antisymmetric_mask
from ..shamir import share, lagrange, scalar_mul
from ..sampling import Sampler

U64 = np.uint64


class TRaccoon:
    name = 'TRaccoon'
    rounds = 3
    online_rounds = 3
    assumption = 'MLWE + SelfTargetMSIS'
    interchangeable = True

    def __init__(self, P, seed=0):
        self.P = P
        self.C = RaccoonCore(P, seed)
        self.q = self.C.q

    def keygen(self, t, n):
        C = self.C
        C.setup()
        s = C.smp.gaussian((C.ell, C.phi), C.sigma_t)
        e = C.smp.gaussian((C.k, C.phi), C.sigma_t)
        t_pk = C.pk_from_secret(C.R.ntt(s), e)
        shares = share(s, t, n, self.q, C.smp)
        seeds = gen_seeds_ordered(n, C.smp.rng)
        mac = {(i, j): C.smp.rng.bytes(32) for i in range(1, n + 1) for j in range(1, n + 1)}
        vkb = xof('vk', C.Ahat_seed, t_pk)
        self.vk = (C.Ahat_seed, t_pk, vkb)
        self.sk = dict(shares=shares, seeds=seeds, mac=mac, s=s, e=e)
        self.n_parties = n
        return self.vk, self.sk

    def round1(self, i, msg, T, sid):
        C = self.C
        r = C.smp.gaussian((C.ell, C.phi), C.sigma_w)
        ep = C.smp.gaussian((C.k, C.phi), C.sigma_w)
        w = C.R.add(C.R.intt(C.R.matmul(C.A_hat, C.R.ntt(r))), ep)
        cmt = xof('cmt', self.vk[2], sid, list(T), msg, w)
        row = np.zeros((C.ell, C.phi), dtype=np.int64)
        for j in T:
            from ..prf import prf_uniform
            row = (row + prf_uniform(self.sk['seeds'][(i, j)], sid, (C.ell, C.phi), self.q).astype(np.int64)) % self.q
        return (r, w), (cmt, row.astype(U64))

    def round2(self, i, state, T, msg, sid, contrib1):
        digest = xof('view1', sid, msg, *[c for c, _ in contrib1])
        tags = [xof('mac', self.sk['mac'][(i, j)], digest) for j in T]
        return (state[1], tags)

    def round3(self, i, state, T, msg, sid, ws):
        C = self.C
        r, w_own = state
        W = np.zeros((C.k, C.phi), dtype=np.int64)
        for w in ws:
            W = (W + np.asarray(w, dtype=np.int64)) % np.int64(self.q)
        qw = self.q >> C.nu_w
        w_agg = hi_bits(W.astype(U64), C.nu_w, self.q) % U64(qw)
        c = C.challenge(self.vk[2], w_agg, msg)
        lam = lagrange(T, i, self.q)
        si = self.sk['shares'][i]
        cs = C.R.intt(C.R.mul(np.broadcast_to(C.R.ntt(c), (C.ell, C.phi)), C.R.ntt(si)))
        _, col, calls = row_column_masks(i, T, self.sk['seeds'], sid, (C.ell, C.phi), self.q)
        zi = C.R.add(C.R.add(scalar_mul(lam, cs, self.q), r), col)
        return zi, c, w_agg, calls

    def combine(self, T, msg, zs, rows, c, w_agg):
        C = self.C
        z = np.zeros((C.ell, C.phi), dtype=np.int64)
        for zi in zs:
            z = (z + np.asarray(zi, dtype=np.int64)) % np.int64(self.q)
        for rw in rows:
            z = (z - np.asarray(rw, dtype=np.int64)) % np.int64(self.q)
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

    def verify(self, msg, sig, t):
        _, t_pk, vkb = self.vk
        return self.C.verify(vkb, t_pk, msg, sig, self.C.signature_bound() * 1.05)

    def sizes(self, t):
        C = self.C
        lq = self.P['logq']
        r1 = 32.0 + C.ell * C.phi * lq / 8.0
        r2 = C.k * C.phi * lq / 8.0 + 16.0 * t
        r3 = C.ell * C.phi * lq / 8.0
        return dict(vk=C.size_vk(), sig=C.size_sig(), r1=r1, r2=r2, r3=r3,
                    total=r1 + r2 + r3, online=r1 + r2 + r3,
                    sk=32 + C.ell * C.phi * lq / 8.0 + 64 * self.n_parties)


class Ringtail:
    name = 'Ringtail'
    rounds = 2
    online_rounds = 1
    assumption = 'MLWE + SelfTargetMSIS'
    interchangeable = True

    def __init__(self, P, seed=0):
        self.P = P
        self.C = RaccoonCore(P, seed)
        self.q = self.C.q
        self.dbar = P['dbar']
        self.sigma_u = 2.0 ** P['log_sigma_u']
        self.sigma_E = 2.0 ** P['log_sigma_e']

    def keygen(self, t, n):
        C = self.C
        C.setup()
        s = C.smp.gaussian((C.ell, C.phi), self.sigma_E)
        e = C.smp.gaussian((C.k, C.phi), self.sigma_E)
        t_pk = C.pk_from_secret(C.R.ntt(s), e)
        shares = share(s, t, n, self.q, C.smp)
        seeds = gen_seeds_ordered(n, C.smp.rng)
        mac = {(i, j): C.smp.rng.bytes(32) for i in range(1, n + 1) for j in range(1, n + 1)}
        vkb = xof('vk', C.Ahat_seed, t_pk)
        self.vk = (C.Ahat_seed, t_pk, vkb)
        self.sk = dict(shares=shares, seeds=seeds, mac=mac, s=s, e=e)
        self.n_parties = n
        return self.vk, self.sk

    def sign1(self, i):
        C = self.C
        d = self.dbar + 1
        R = np.concatenate([C.smp.gaussian((C.ell, 1, C.phi), C.sigma_w),
                            C.smp.gaussian((C.ell, self.dbar, C.phi), self.sigma_E)], axis=1)
        E = np.concatenate([C.smp.gaussian((C.k, 1, C.phi), C.sigma_w),
                            C.smp.gaussian((C.k, self.dbar, C.phi), self.sigma_E)], axis=1)
        D = C.R.add(C.R.intt(C.R.matmul(C.A_hat, C.R.ntt(R))), E)
        return (R, D), D

    def rank_check(self, D):
        C = self.C
        from ..ring import mulmod, submod
        q = self.q
        M = np.array(C.R.ntt(D[:, 1:, :]), dtype=U64).transpose(2, 0, 1)
        rows, cols = M.shape[1], M.shape[2]
        piv = 0
        for r in range(rows):
            for cix in range(piv, cols):
                col = M[:, r, cix]
                if np.all(col == 0):
                    continue
                inv = np.array([pow(int(v), q - 2, q) if v else 0 for v in col], dtype=U64)
                M[:, r, :] = mulmod(M[:, r, :], np.broadcast_to(inv.reshape(-1, 1), M[:, r, :].shape), q)
                for r2 in range(r + 1, rows):
                    f = M[:, r2, cix].copy()
                    M[:, r2, :] = submod(M[:, r2, :],
                                         mulmod(M[:, r, :], np.broadcast_to(f.reshape(-1, 1), M[:, r, :].shape), q), q)
                piv = cix + 1
                break
        return piv

    def sign2(self, i, state, T, msg, Ds):
        C = self.C
        R, Dself = state
        seed = xof('Hu', self.vk[2], list(T), msg, *[np.ascontiguousarray(D) for D in Ds])
        u = hash_gaussian(seed, (self.dbar, C.phi), self.sigma_u, self.q)
        D = np.zeros(Dself.shape, dtype=np.int64)
        for Dj in Ds:
            D = (D + np.asarray(Dj, dtype=np.int64)) % np.int64(self.q)
        self.rank_check(D.astype(U64))
        uu = np.concatenate([np.zeros((1, C.phi), dtype=U64), u], axis=0)
        uu[0, 0] = U64(1)
        uhat = C.R.ntt(uu)
        h = C.R.intt(C.R.matmul(C.R.ntt(D.astype(U64)), uhat))
        qw = self.q >> C.nu_w
        w_agg = hi_bits(h, C.nu_w, self.q) % U64(qw)
        c = C.challenge(self.vk[2], w_agg, msg)
        lam = lagrange(T, i, self.q)
        si = self.sk['shares'][i]
        cs = C.R.intt(C.R.mul(np.broadcast_to(C.R.ntt(c), (C.ell, C.phi)), C.R.ntt(si)))
        Ru = C.R.intt(C.R.matmul(C.R.ntt(R), uhat))
        zi = C.R.add(scalar_mul(lam, cs, self.q), Ru)
        row, col, calls = row_column_masks(i, T, self.sk['seeds'], seed, (C.ell, C.phi), self.q)
        zi = C.R.sub(C.R.add(zi, col), row)
        return zi, c, w_agg, calls

    def combine(self, T, msg, zs, c, w_agg):
        return TRaccoon.combine(self, T, msg, zs, [], c, w_agg)

    def verify(self, msg, sig, t):
        _, t_pk, vkb = self.vk
        return self.C.verify(vkb, t_pk, msg, sig, self.C.signature_bound() * 1.05)

    def sizes(self, t):
        C = self.C
        lq = self.P['logq']
        off = C.k * (self.dbar + 1) * C.phi * lq / 8.0
        on = C.ell * C.phi * lq / 8.0 + 16.0 * t
        return dict(vk=C.size_vk(), sig=C.size_sig(), r1=off, r2=on, r3=0.0,
                    total=off + on, online=on,
                    sk=32 + C.ell * C.phi * lq / 8.0 + 64 * self.n_parties)


class Tanuki:
    name = 'Tanuki/EKT'
    rounds = 2
    online_rounds = 1
    assumption = 'AOM-MLWE (MLWE+MSIS via AOM-MISIS)'
    interchangeable = True

    def __init__(self, P, seed=0):
        self.P = P
        self.C = RaccoonCore(P, seed)
        self.q = self.C.q
        self.rep = P['rep']

    def keygen(self, t, n):
        C = self.C
        C.setup()
        s = C.smp.gaussian((C.ell, C.phi), C.sigma_t)
        e = C.smp.gaussian((C.k, C.phi), C.sigma_t)
        t_pk = C.pk_from_secret(C.R.ntt(s), e)
        shares = share(s, t, n, self.q, C.smp)
        seeds = gen_seeds_ordered(n, C.smp.rng)
        vkb = xof('vk', C.Ahat_seed, t_pk)
        self.vk = (C.Ahat_seed, t_pk, vkb)
        self.sk = dict(shares=shares, seeds=seeds, s=s, e=e)
        self.n_parties = n
        return self.vk, self.sk

    def sign1(self, i):
        C = self.C
        R = C.smp.gaussian((C.ell, self.rep, C.phi), C.sigma_w)
        E = C.smp.gaussian((C.k, self.rep, C.phi), C.sigma_w)
        W = C.R.add(C.R.intt(C.R.matmul(C.A_hat, C.R.ntt(R))), E)
        return (R, W), W

    def sign2(self, i, state, T, msg, Ws):
        C = self.C
        R, Wself = state
        seed = xof('G', self.vk[2], list(T), msg, *[np.ascontiguousarray(W) for W in Ws])
        b = hash_monomials(seed, self.rep, C.phi, self.q)
        W = np.zeros(Wself.shape, dtype=np.int64)
        for Wj in Ws:
            W = (W + np.asarray(Wj, dtype=np.int64)) % np.int64(self.q)
        bhat = C.R.ntt(b)
        wv = C.R.intt(C.R.matmul(C.R.ntt(W.astype(U64)), bhat))
        qw = self.q >> C.nu_w
        w_agg = hi_bits(wv, C.nu_w, self.q) % U64(qw)
        c = C.challenge(self.vk[2], w_agg, msg)
        lam = lagrange(T, i, self.q)
        si = self.sk['shares'][i]
        cs = C.R.intt(C.R.mul(np.broadcast_to(C.R.ntt(c), (C.ell, C.phi)), C.R.ntt(si)))
        Rb = C.R.intt(C.R.matmul(C.R.ntt(R), bhat))
        zi = C.R.add(scalar_mul(lam, cs, self.q), Rb)
        row, col, calls = row_column_masks(i, T, self.sk['seeds'], seed, (C.ell, C.phi), self.q)
        zi = C.R.sub(C.R.add(zi, col), row)
        return zi, c, w_agg, calls

    def combine(self, T, msg, zs, c, w_agg):
        return TRaccoon.combine(self, T, msg, zs, [], c, w_agg)

    def verify(self, msg, sig, t):
        _, t_pk, vkb = self.vk
        return self.C.verify(vkb, t_pk, msg, sig, self.C.signature_bound() * 1.05)

    def sizes(self, t):
        C = self.C
        lq = self.P['logq']
        off = C.k * self.rep * C.phi * lq / 8.0
        on = C.ell * C.phi * lq / 8.0
        return dict(vk=C.size_vk(), sig=C.size_sig(), r1=off, r2=on, r3=0.0,
                    total=off + on, online=on,
                    sk=32 + C.ell * C.phi * lq / 8.0 + 64 * self.n_parties)
