import hashlib
import os
import numpy as np

U64 = np.uint64


class Drbg:
    """SHAKE256 based deterministic random bit generator.

    The seed is taken from os.urandom unless a seed is given explicitly, which is
    only meant for known answer tests and reproducible benchmarks.
    """

    def __init__(self, seed=None):
        if seed is None:
            key = os.urandom(32)
        elif isinstance(seed, (bytes, bytearray)):
            key = bytes(seed)
        else:
            key = int(seed).to_bytes(16, 'little', signed=True)
        self._key = hashlib.shake_256(b'thimza-drbg|' + key).digest(32)
        self._ctr = 0

    def bytes(self, n):
        out = hashlib.shake_256(self._key + self._ctr.to_bytes(8, 'little')).digest(n)
        self._ctr += 1
        return out

    def u64(self, count):
        return np.frombuffer(self.bytes(8 * count), dtype=U64).copy()

    def below(self, bound, count):
        bits = int(bound - 1).bit_length()
        mask = U64((1 << bits) - 1) if bits < 64 else U64(0xFFFFFFFFFFFFFFFF)
        out = np.empty(0, dtype=U64)
        while out.size < count:
            m = count - out.size
            v = self.u64(m + (m >> 6) + 32) & mask
            out = np.concatenate([out, v[v < U64(bound)]])
        return out[:count]

    def unit(self, count):
        return (self.u64(count) >> U64(11)).astype(np.float64) / float(1 << 53)


class Sampler:
    def __init__(self, q, seed=None):
        self.q = q
        self.rng = Drbg(seed)

    def uniform(self, shape):
        n = int(np.prod(shape))
        return self.rng.below(self.q, n).reshape(shape)

    def gaussian(self, shape, sigma):
        if sigma <= 0:
            return np.zeros(shape, dtype=U64)
        n = int(np.prod(shape))
        if sigma < 8.0:
            z = self._cdt(n, sigma)
        else:
            u1 = np.clip(self.rng.unit(n), 2.0 ** -60, 1.0)
            u2 = self.rng.unit(n)
            z = np.rint(np.sqrt(-2.0 * np.log(u1)) * np.cos(2.0 * np.pi * u2) * sigma).astype(np.int64)
        return (z.reshape(shape) % np.int64(self.q)).astype(U64)

    def _cdt(self, n, sigma):
        bound = int(np.ceil(12 * sigma)) + 1
        xs = np.arange(-bound, bound + 1)
        w = np.exp(-np.pi * (xs / sigma) ** 2)
        cdf = np.cumsum(w / w.sum())
        u = self.rng.unit(n)
        idx = np.searchsorted(cdf, u, side='right')
        return xs[np.minimum(idx, xs.size - 1)].astype(np.int64)

    def challenge(self, phi, kappa):
        idx = []
        seen = set()
        while len(idx) < kappa:
            j = int(self.rng.below(phi, 1)[0])
            if j not in seen:
                seen.add(j)
                idx.append(j)
        sgn = self.rng.below(2, kappa)
        c = np.zeros(phi, dtype=U64)
        for i, s in zip(idx, sgn):
            c[i] = U64(1) if int(s) == 0 else U64(self.q - 1)
        return c

    def monomials(self, rep, phi):
        out = np.zeros((rep, phi), dtype=U64)
        out[0, 0] = U64(1)
        for b in range(1, rep):
            i = int(self.rng.below(phi, 1)[0])
            s = int(self.rng.below(2, 1)[0])
            out[b, i] = U64(1) if s == 0 else U64(self.q - 1)
        return out


def gaussian_l2_bound(sigma, dim, tail=1.05):
    return tail * sigma * np.sqrt(dim)
