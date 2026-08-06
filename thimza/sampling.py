import numpy as np

U64 = np.uint64


class Sampler:
    def __init__(self, q, seed=0):
        self.q = q
        self.rng = np.random.default_rng(seed)

    def uniform(self, shape):
        return self.rng.integers(0, self.q, size=shape, dtype=np.int64).astype(U64)

    def gaussian(self, shape, sigma):
        if sigma <= 0:
            return np.zeros(shape, dtype=U64)
        if sigma < 8.0:
            z = self._small_gaussian(shape, sigma)
        else:
            z = np.rint(self.rng.normal(0.0, sigma, size=shape)).astype(np.int64)
        return (z % np.int64(self.q)).astype(U64)

    def _small_gaussian(self, shape, sigma):
        bound = int(np.ceil(10 * sigma))
        xs = np.arange(-bound, bound + 1)
        w = np.exp(-np.pi * (xs / sigma) ** 2)
        w = w / w.sum()
        return self.rng.choice(xs, size=shape, p=w).astype(np.int64)

    def challenge(self, phi, kappa):
        idx = self.rng.choice(phi, size=kappa, replace=False)
        sgn = self.rng.integers(0, 2, size=kappa)
        c = np.zeros(phi, dtype=U64)
        for i, s in zip(idx, sgn):
            c[i] = U64(1) if s == 0 else U64(self.q - 1)
        return c

    def monomials(self, rep, phi):
        out = np.zeros((rep, phi), dtype=U64)
        out[0, 0] = U64(1)
        for b in range(1, rep):
            i = int(self.rng.integers(0, phi))
            s = int(self.rng.integers(0, 2))
            out[b, i] = U64(1) if s == 0 else U64(self.q - 1)
        return out


def gaussian_l2_bound(sigma, dim, tail=1.05):
    return tail * sigma * np.sqrt(dim)
