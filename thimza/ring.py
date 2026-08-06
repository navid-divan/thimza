import numpy as np

U64 = np.uint64


def _is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def find_ntt_prime(bits, phi):
    step = 2 * phi
    cand = ((1 << bits) // step) * step + 1
    while cand > (1 << (bits - 2)):
        if _is_prime(cand):
            return cand
        cand -= step
    raise ValueError('no prime found')


def _primitive_root(q):
    fac = []
    n = q - 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            fac.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fac.append(n)
    g = 2
    while True:
        if all(pow(g, (q - 1) // f, q) != 1 for f in fac):
            return g
        g += 1


def mulmod(a, b, q):
    af = a.astype(np.float64)
    bf = b.astype(np.float64)
    quo = np.floor(af * bf / float(q)).astype(U64)
    r = a.astype(U64) * b.astype(U64) - quo * U64(q)
    r = np.where(r > U64(1 << 63), r + U64(q), r)
    r = np.where(r >= U64(q), r - U64(q), r)
    r = np.where(r >= U64(q), r - U64(q), r)
    return r


def addmod(a, b, q):
    r = a.astype(U64) + b.astype(U64)
    return np.where(r >= U64(q), r - U64(q), r)


def submod(a, b, q):
    r = a.astype(U64) + U64(q) - b.astype(U64)
    return np.where(r >= U64(q), r - U64(q), r)


class Rq:
    def __init__(self, phi, q):
        assert phi & (phi - 1) == 0
        assert (q - 1) % (2 * phi) == 0
        assert q < (1 << 51)
        self.phi = phi
        self.q = q
        self.logq = q.bit_length()
        g = _primitive_root(q)
        self.psi = pow(g, (q - 1) // (2 * phi), q)
        self.psi_inv = pow(self.psi, q - 2, q)
        self.phi_inv = U64(pow(phi, q - 2, q))
        self.fwd = self._table(self.psi)
        self.inv = self._table(self.psi_inv)

    def _table(self, root):
        phi = self.phi
        lg = phi.bit_length() - 1
        tab = np.zeros(phi, dtype=U64)
        for i in range(phi):
            r = int('{:0{w}b}'.format(i, w=lg)[::-1], 2) if lg > 0 else 0
            tab[i] = pow(root, r, self.q)
        return tab

    def zeros(self, *shape):
        return np.zeros(tuple(shape) + (self.phi,), dtype=U64)

    def ntt(self, a):
        q = self.q
        x = np.array(a, dtype=U64, copy=True)
        shp = x.shape
        x = x.reshape(-1, self.phi)
        B = x.shape[0]
        n = self.phi
        t = n
        m = 1
        while m < n:
            t //= 2
            y = x.reshape(B, m, 2 * t)
            lo = y[:, :, :t]
            hi = y[:, :, t:]
            S = self.fwd[m:2 * m].reshape(1, m, 1)
            V = mulmod(hi, np.broadcast_to(S, hi.shape), q)
            s = addmod(lo, V, q)
            d = submod(lo, V, q)
            x = np.concatenate([s, d], axis=2).reshape(B, n)
            m *= 2
        return x.reshape(shp)

    def intt(self, a):
        q = self.q
        x = np.array(a, dtype=U64, copy=True)
        shp = x.shape
        x = x.reshape(-1, self.phi)
        B = x.shape[0]
        n = self.phi
        t = 1
        m = n
        while m > 1:
            h = m // 2
            y = x.reshape(B, h, 2 * t)
            lo = y[:, :, :t]
            hi = y[:, :, t:]
            S = self.inv[h:2 * h].reshape(1, h, 1)
            s = addmod(lo, hi, q)
            d = mulmod(submod(lo, hi, q), np.broadcast_to(S, hi.shape), q)
            x = np.concatenate([s, d], axis=2).reshape(B, n)
            t *= 2
            m = h
        x = mulmod(x, np.full(x.shape, self.phi_inv, dtype=U64), q)
        return x.reshape(shp)

    def mul(self, a, b):
        return mulmod(np.asarray(a, dtype=U64), np.asarray(b, dtype=U64), self.q)

    def add(self, a, b):
        return addmod(np.asarray(a, dtype=U64), np.asarray(b, dtype=U64), self.q)

    def sub(self, a, b):
        return submod(np.asarray(a, dtype=U64), np.asarray(b, dtype=U64), self.q)

    def neg(self, a):
        return submod(self.zeros(*np.asarray(a).shape[:-1]), np.asarray(a, dtype=U64), self.q)

    def matmul(self, A, X):
        q = self.q
        A = np.asarray(A, dtype=U64)
        X = np.asarray(X, dtype=U64)
        k, l = A.shape[0], A.shape[1]
        if X.ndim == 2:
            out = np.zeros((k, self.phi), dtype=U64)
            for i in range(k):
                acc = np.zeros(self.phi, dtype=U64)
                for j in range(l):
                    acc = addmod(acc, mulmod(A[i, j], X[j], q), q)
                out[i] = acc
            return out
        r = X.shape[1]
        out = np.zeros((k, r, self.phi), dtype=U64)
        for i in range(k):
            for j in range(l):
                aij = np.broadcast_to(A[i, j], (r, self.phi))
                out[i] = addmod(out[i], mulmod(aij, X[j], q), q)
        return out

    def center(self, a):
        q = self.q
        x = np.asarray(a, dtype=U64).astype(np.int64)
        return np.where(x > (q >> 1), x - np.int64(q), x)

    def linf(self, a):
        c = self.center(a)
        return int(np.max(np.abs(c))) if c.size else 0

    def l2(self, a):
        c = self.center(a).astype(np.float64)
        return float(np.sqrt(np.sum(c * c)))


def hi_bits(a, nu, q):
    x = np.asarray(a, dtype=U64)
    return (x + U64(1 << (nu - 1))) >> U64(nu)


def hi_bits_mod(a, nu, q, qnu):
    return hi_bits(a, nu, q) % U64(qnu)


def mulmod_scalar(a, lam, q):
    lam = int(lam) % q
    b = np.full(np.asarray(a).shape, U64(lam), dtype=U64)
    return mulmod(np.asarray(a, dtype=U64), b, q)
