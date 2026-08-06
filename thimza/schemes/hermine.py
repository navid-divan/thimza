import math
import numpy as np
from ..ring import hi_bits
from ..core import RaccoonCore, bits_gauss
from ..prf import xof, hash_monomials
from ..vandermonde import vand_share, vand_recover

U64 = np.uint64


class Hermine:
    name = 'Hermine'
    rounds = 2
    online_rounds = 1
    assumption = 'AOM-MISIS (MLWE + MSIS)'
    interchangeable = True

    def __init__(self, P, seed=0):
        self.P = P
        self.C = RaccoonCore(P, seed)
        self.q = self.C.q
        self.rep = P['rep']
        self.nu_wp = P['nu_wp']
        self.sigma_s = 2.0 ** P['log_sigma_s']

    def keygen(self, t, n):
        C = self.C
        C.setup()
        s = C.smp.gaussian((C.ell, C.phi), self.sigma_s)
        e = C.smp.gaussian((C.k, C.phi), self.sigma_s)
        t_pk = self._pk(s, e)
        se = np.concatenate([s, e], axis=0)
        shr = vand_share(se, list(range(1, n + 1)), t, '', {}, C.smp, self.sigma_s, self.q)
        vkb = xof('vk', C.Ahat_seed, t_pk)
        self.vk = (C.Ahat_seed, t_pk, vkb)
        self.sk = dict(shares=shr, s=s, e=e)
        self.t_thr = t
        self.n_parties = n
        self.share_slots = max(len(v) for v in shr.values())
        return self.vk, self.sk

    def _pk(self, s, e):
        C = self.C
        As = C.R.intt(C.R.matmul(C.A_hat, C.R.ntt(s)))
        b = C.R.add(As, e)
        b2 = C.R.add(b, b)
        return hi_bits(b2, C.nu_t, self.q) % U64(self.q >> C.nu_t)

    def sign1(self, i):
        C = self.C
        R = C.smp.gaussian((C.ell, self.rep, C.phi), C.sigma_w)
        E = C.smp.gaussian((C.k, self.rep, C.phi), C.sigma_w)
        W = C.R.add(C.R.intt(C.R.matmul(C.A_hat, C.R.ntt(R))), E)
        Wt = hi_bits(W, self.nu_wp, self.q)
        return (R, E, Wt), Wt

    def sign2(self, i, state, T, msg, Ws):
        C = self.C
        R, E, _ = state
        seed = xof('Hbeta', self.vk[2], list(T), msg, *[np.ascontiguousarray(W) for W in Ws])
        beta = hash_monomials(seed, self.rep, C.phi, self.q)
        sh = np.int64(1 << self.nu_wp)
        Wsum = np.zeros((C.k, self.rep, C.phi), dtype=np.int64)
        for Wj in Ws:
            Wsum = (Wsum + np.asarray(Wj, dtype=np.int64) * sh) % np.int64(self.q)
        bhat = C.R.ntt(beta)
        wv = C.R.intt(C.R.matmul(C.R.ntt(Wsum.astype(U64)), bhat))
        qw = self.q >> C.nu_w
        w_agg = hi_bits(wv, C.nu_w, self.q) % U64(qw)
        c = C.challenge(self.vk[2], w_agg, msg)
        idx = vand_recover(list(range(1, self.n_parties + 1)), list(T), '', {})
        se_i = self.sk['shares'][i][idx[i]]
        chat = C.R.ntt(c)
        cs = C.R.intt(C.R.mul(np.broadcast_to(chat, (C.ell + C.k, C.phi)), C.R.ntt(se_i)))
        cs2 = C.R.add(cs, cs)
        RE = np.concatenate([R, E], axis=0)
        Rb = C.R.intt(C.R.matmul(C.R.ntt(RE), bhat))
        zi = C.R.add(cs2, Rb)
        return zi, c, w_agg, 0

    def combine(self, T, msg, zs, c, w_agg):
        C = self.C
        acc = np.zeros((C.ell + C.k, C.phi), dtype=np.int64)
        for zi in zs:
            acc = (acc + np.asarray(zi, dtype=np.int64)) % np.int64(self.q)
        zfull = acc.astype(U64)
        z = zfull[:C.ell]
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
        off = C.k * self.rep * C.phi * (lq - self.nu_wp) / 8.0
        sig_agg = C.sigma_w * math.sqrt(self.rep * min(t, self.P['Tmax']))
        on = (C.ell + C.k) * C.phi * bits_gauss(C.sigma_w * math.sqrt(self.rep)) / 8.0
        sig = 32 + C.ell * C.phi * bits_gauss(sig_agg) / 8.0
        sig += C.k * C.phi * max(2, lq - C.nu_w) / 8.0
        vk = 32 + C.k * C.phi * (lq - C.nu_t) / 8.0
        return dict(vk=vk, sig=sig, r1=off, r2=on, r3=0.0, total=off + on,
                    online=on, sk=32 + self.share_slots * (C.ell + C.k) * C.phi *
                    bits_gauss(self.sigma_s * math.sqrt(math.log2(max(self.n_parties, 2)))) / 8.0)
