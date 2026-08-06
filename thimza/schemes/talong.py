import math
import numpy as np
from ..ring import Rq, find_ntt_prime, hi_bits
from ..prf import xof, uniform_rq, hash_challenge
from ..sampling import Sampler
from ..masking import gen_seeds_ordered, row_column_masks
from ..shamir import share, lagrange, scalar_mul
from ..core import bits_gauss

U64 = np.uint64


class TalonG:
    name = 'TalonG'
    rounds = 2
    online_rounds = 2
    assumption = 'RLWE + RSIS + NTRU'
    interchangeable = False

    def __init__(self, P, seed=0):
        self.P = P
        self.phi = P['phi']
        self.q = find_ntt_prime(P['logq'], self.phi)
        self.R = Rq(self.phi, self.q)
        self.omega = P['omega']
        self.s1 = 2.0 ** P['log_sigma_1']
        self.s2 = 2.0 ** P['log_sigma_2']
        self.sr = 2.0 ** P['log_sigma_r']
        self.p1 = P['p1']
        self.p2 = P['p2']
        self.Tmax = P['Tmax']
        self.smp = Sampler(self.q, seed)

    def keygen(self, t, n):
        self.a = uniform_rq(self.smp.rng.bytes(32), (1, self.phi), self.q)
        s = self.smp.gaussian((1, self.phi), self.s2)
        e = self.smp.gaussian((1, self.phi), self.s2)
        b = self.R.add(self.R.intt(self.R.mul(self.R.ntt(self.a), self.R.ntt(s))), e)
        self.s, self.e, self.b = s, e, b
        self.sh_s = share(s, t, n, self.q, self.smp)
        self.sh_e = share(e, t, n, self.q, self.smp)
        self.seeds = gen_seeds_ordered(n, self.smp.rng)
        self.vkb = xof('vk', self.a, b)
        self.n_parties = n
        self.vk = (self.a, b, self.vkb)
        return self.vk, dict(s=s, e=e)

    def sign1(self, i, msg):
        y = self.smp.gaussian((1, self.phi), self.s1)
        ep = self.smp.gaussian((1, self.phi), self.s1)
        w = self.R.add(self.R.intt(self.R.mul(self.R.ntt(self.a), self.R.ntt(y))), ep)
        h = uniform_rq(xof('H1', self.vkb, msg), (1, self.phi), self.q)
        r1 = self.smp.gaussian((1, self.phi), self.sr)
        r2 = self.smp.gaussian((1, self.phi), self.sr)
        hr2 = self.R.intt(self.R.mul(self.R.ntt(h), self.R.ntt(r2)))
        wt = self.R.add(self.R.add(w, r1), hr2)
        return (y, ep, r1, r2, h), wt

    def sign2(self, i, state, T, msg, wts):
        y, ep, r1, r2, h = state
        W = np.zeros((1, self.phi), dtype=np.int64)
        for wt in wts:
            W = (W + np.asarray(wt, dtype=np.int64)) % np.int64(self.q)
        qp = self.q >> self.p1
        wr = hi_bits(W.astype(U64), self.p1, self.q) % U64(qp)
        c = hash_challenge(xof('H2', self.vkb, wr, msg), self.phi, self.omega, self.q)
        lam = lagrange(T, i, self.q)
        chat = self.R.ntt(c)
        cs = self.R.intt(self.R.mul(np.broadcast_to(chat, (1, self.phi)), self.R.ntt(self.sh_s[i])))
        ce = self.R.intt(self.R.mul(np.broadcast_to(chat, (1, self.phi)), self.R.ntt(self.sh_e[i])))
        lbl = xof('ssid', self.vkb, list(T), msg, *[np.ascontiguousarray(w) for w in wts])
        rowz, colz, calls = row_column_masks(i, T, self.seeds, lbl + b'z', (1, self.phi), self.q)
        rowd, cold, _ = row_column_masks(i, T, self.seeds, lbl + b'd', (1, self.phi), self.q)
        zi = self.R.sub(self.R.add(self.R.add(y, scalar_mul(lam, cs, self.q)), colz), rowz)
        di = self.R.sub(self.R.add(self.R.add(ep, scalar_mul(lam, ce, self.q)), cold), rowd)
        return (zi, di, r1, r2), c, wr, 2 * calls

    def combine(self, T, msg, parts, c, wr):
        acc = [np.zeros((1, self.phi), dtype=np.int64) for _ in range(4)]
        for p in parts:
            for idx in range(4):
                acc[idx] = (acc[idx] + np.asarray(p[idx], dtype=np.int64)) % np.int64(self.q)
        z, dl, r1, r2 = [a.astype(U64) for a in acc]
        h = uniform_rq(xof('H1', self.vkb, msg), (1, self.phi), self.q)
        az = self.R.intt(self.R.mul(self.R.ntt(self.a), self.R.ntt(z)))
        bc = self.R.intt(self.R.mul(self.R.ntt(self.b), self.R.ntt(c).reshape(1, -1)))
        hr2 = self.R.intt(self.R.mul(self.R.ntt(h), self.R.ntt(r2)))
        base = self.R.add(self.R.sub(az, bc), hr2)
        qp = self.q >> self.p1
        hb = hi_bits(base, self.p1, self.q) % U64(qp)
        dt = (np.asarray(wr, dtype=np.int64) - hb.astype(np.int64)) % np.int64(qp)
        dt = np.where(dt > (qp >> 1), dt - np.int64(qp), dt)
        return (c, z, r2, dt)

    def verify(self, msg, sig, t):
        c, z, r2, dt = sig
        h = uniform_rq(xof('H1', self.vkb, msg), (1, self.phi), self.q)
        az = self.R.intt(self.R.mul(self.R.ntt(self.a), self.R.ntt(z)))
        bc = self.R.intt(self.R.mul(self.R.ntt(self.b), self.R.ntt(c).reshape(1, -1)))
        hr2 = self.R.intt(self.R.mul(self.R.ntt(h), self.R.ntt(r2)))
        base = self.R.add(self.R.sub(az, bc), hr2)
        qp = self.q >> self.p1
        hb = hi_bits(base, self.p1, self.q) % U64(qp)
        wr = (hb.astype(np.int64) + np.asarray(dt, dtype=np.int64)) % np.int64(qp)
        c2 = hash_challenge(xof('H2', self.vkb, wr.astype(U64), msg), self.phi, self.omega, self.q)
        if not np.array_equal(c, c2):
            return False
        bz = self.R.l2(z)
        br = self.R.l2(r2)
        return bz <= 2.0 ** 47.0 and br <= 2.0 ** 36.0

    def sizes(self, t):
        lq = self.P['logq']
        phi = self.phi
        sig = 32 + phi * bits_gauss(self.s1 * math.sqrt(self.Tmax)) / 8.0
        sig += phi * bits_gauss(self.sr * math.sqrt(self.Tmax)) / 8.0
        sig += phi * max(2, lq - self.p1) / 8.0
        vk = 32 + phi * (lq - self.p2) / 8.0
        r1 = phi * lq / 8.0
        r2 = 2 * phi * lq / 8.0 + 2 * phi * bits_gauss(self.sr) / 8.0
        return dict(vk=vk, sig=sig, r1=r1, r2=r2, r3=0.0, total=r1 + r2,
                    online=r1 + r2, sk=32 + 2 * phi * lq / 8.0 + 64 * self.n_parties)
