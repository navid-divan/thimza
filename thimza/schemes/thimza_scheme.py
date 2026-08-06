import math
import time
import numpy as np
from ..ring import hi_bits
from ..core import RaccoonCore, bits_gauss
from ..prf import xof, uniform_rq
from ..masking import gen_seeds_pairwise, antisymmetric_mask
from ..shamir import share, lagrange, scalar_mul

U64 = np.uint64


class Thimza:
    name = 'Thimza'
    rounds = 3
    online_rounds = 3
    assumption = 'MLWE + SelfTargetMSIS'
    interchangeable = True

    def __init__(self, P, seed=0):
        self.P = P
        self.C = RaccoonCore(P, seed)
        self.nu_c = P['nu_c']
        self.q = self.C.q
        self.R = self.C.R

    def keygen(self, t, n):
        C = self.C
        C.setup()
        s = C.smp.gaussian((C.ell, C.phi), C.sigma_t)
        e = C.smp.gaussian((C.k, C.phi), C.sigma_t)
        s_hat = C.R.ntt(s)
        t_pk = C.pk_from_secret(s_hat, e)
        shares = share(s, t, n, self.q, C.smp)
        seeds = gen_seeds_pairwise(n, C.smp.rng)
        vk_bytes = xof('vk', C.Ahat_seed, t_pk)
        self.vk = (C.Ahat_seed, t_pk, vk_bytes)
        self.sk = dict(shares=shares, seeds=seeds, s=s, e=e)
        self.t_thr = t
        self.n_parties = n
        return self.vk, self.sk

    def _commit(self, msg):
        C = self.C
        r = C.smp.gaussian((C.ell, C.phi), C.sigma_w)
        ep = C.smp.gaussian((C.k, C.phi), C.sigma_w)
        w = C.R.add(C.R.intt(C.R.matmul(C.A_hat, C.R.ntt(r))), ep)
        wbar = hi_bits(w, self.nu_c, self.q)
        return r, wbar

    def round1(self, i, msg):
        r, wbar = self._commit(msg)
        cmt = xof('cmt', self.vk[2], msg, i, wbar)
        return (r, wbar), (cmt,)

    def round2(self, state):
        return (state[1],)

    def round3(self, i, state, T, msg, cmts, wbars):
        C = self.C
        r, wbar = state
        view = xof('view', self.vk[2], msg, list(T), *(list(cmts) + [w for w in wbars]))
        W = np.zeros((C.k, C.phi), dtype=np.int64)
        sh = np.int64(1 << self.nu_c)
        for wb in wbars:
            W = (W + np.asarray(wb, dtype=np.int64) * sh) % np.int64(self.q)
        qw = self.q >> C.nu_w
        w_agg = hi_bits(W.astype(U64), C.nu_w, self.q) % U64(qw)
        c = C.challenge(self.vk[2], w_agg, msg)
        lam = lagrange(T, i, self.q)
        si = self.sk['shares'][i]
        cs = C.R.intt(C.R.mul(np.broadcast_to(C.R.ntt(c), (C.ell, C.phi)), C.R.ntt(si)))
        zi = C.R.add(scalar_mul(lam, cs, self.q), r)
        M, calls = antisymmetric_mask(i, T, self.sk['seeds'], view, (C.ell, C.phi), self.q)
        zi = C.R.add(zi, M)
        return zi, c, w_agg, calls

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

    def verify(self, msg, sig, t):
        _, t_pk, vkb = self.vk
        return self.C.verify(vkb, t_pk, msg, sig, self.C.signature_bound(t) * 1.05)

    def sizes(self, t):
        C = self.C
        lq = self.P['logq']
        r1 = 32.0
        r2 = C.k * C.phi * (lq - self.nu_c) / 8.0
        r3 = C.ell * C.phi * lq / 8.0
        return dict(vk=C.size_vk(), sig=C.size_sig(t), r1=r1, r2=r2, r3=r3,
                    total=r1 + r2 + r3, online=r1 + r2 + r3,
                    sk=32 + C.ell * C.phi * lq / 8.0 + 32 * (self.n_parties - 1))
