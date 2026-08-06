import math
import numpy as np
from .ring import Rq, find_ntt_prime, hi_bits
from .sampling import Sampler
from .prf import xof, hash_challenge, uniform_rq

U64 = np.uint64


def bits_gauss(sigma):
    return max(2, int(math.ceil(math.log2(max(float(sigma), 1.0)) + 2.6)))


def bits_uniform(q):
    return int(q).bit_length()


class RaccoonCore:
    def __init__(self, P, seed=0):
        self.P = P
        self.phi = P['phi']
        self.q = find_ntt_prime(P['logq'], self.phi)
        self.R = Rq(self.phi, self.q)
        self.ell = P['ell']
        self.k = P['k']
        self.omega = P['omega']
        self.nu_t = P.get('nu_t', 0)
        self.nu_w = P.get('nu_w', 0)
        self.sigma_t = 2.0 ** P.get('log_sigma_t', P.get('log_sigma_e', 0.0))
        self.sigma_w = 2.0 ** P['log_sigma_w']
        self.Tmax = P['Tmax']
        self.smp = Sampler(self.q, seed)
        self.A_hat = None
        self.Ahat_seed = None

    def setup(self):
        self.Ahat_seed = self.smp.rng.bytes(32)
        A = uniform_rq(self.Ahat_seed, (self.k, self.ell, self.phi), self.q)
        self.A_hat = A
        return self.Ahat_seed

    def pk_from_secret(self, s_hat, e):
        As = self.R.matmul(self.A_hat, s_hat)
        b = self.R.add(self.R.intt(As), e)
        return hi_bits(b, self.nu_t, self.q) % U64(self.q >> self.nu_t)

    def challenge(self, vk_bytes, w, msg):
        seed = xof('Hc', vk_bytes, w, msg)
        return hash_challenge(seed, self.phi, self.omega, self.q)

    def verify(self, vk_bytes, t_pk, msg, sig, bound_l2):
        c, z, h = sig
        c_hat = self.R.ntt(c)
        z_hat = self.R.ntt(z)
        Az = self.R.intt(self.R.matmul(self.A_hat, z_hat))
        tq = np.asarray(t_pk, dtype=U64)
        t_full = (tq.astype(np.int64) * np.int64(1 << self.nu_t)) % np.int64(self.q)
        ct = self.R.intt(self.R.mul(np.broadcast_to(c_hat, (self.k, self.phi)),
                                    self.R.ntt(t_full.astype(U64))))
        base = self.R.sub(Az, ct)
        w_rec = (hi_bits(base, self.nu_w, self.q).astype(np.int64) + np.asarray(h, dtype=np.int64))
        qw = self.q >> self.nu_w
        w_rec = w_rec % np.int64(qw)
        c2 = self.challenge(vk_bytes, w_rec.astype(U64), msg)
        if not np.array_equal(c, c2):
            return False
        nz = self.R.l2(z)
        nh = float(np.sqrt(np.sum((np.asarray(h, dtype=np.int64).astype(np.float64) *
                                   (1 << self.nu_w)) ** 2)))
        return math.sqrt(nz * nz + nh * nh) <= bound_l2

    def signature_bound(self, t=None, lam=128):
        T = self.Tmax if t is None else max(t, 1)
        T = self.Tmax
        dim = (self.ell + self.k) * self.phi
        kk = 2.0
        for _ in range(200):
            f = kk * kk - math.log(kk * kk) - 1 - 2 * lam * math.log(2) / dim
            fp = 2 * kk - 2 / kk
            kk = kk - f / fp
        main = kk * self.sigma_w * math.sqrt(T * dim)
        slack = (1 << (self.nu_w + 1)) * math.sqrt(self.k * self.phi)
        return main + slack

    def size_vk(self):
        return 32 + self.k * self.phi * (self.P['logq'] - self.nu_t) / 8.0

    def size_sig(self, t=None):
        sagg = self.sigma_w * math.sqrt(self.Tmax)
        z = self.ell * self.phi * bits_gauss(sagg) / 8.0
        h = self.k * self.phi * bits_gauss(max(sagg / 2.0 ** self.nu_w, 1.0)) / 8.0
        return 32 + z + h
