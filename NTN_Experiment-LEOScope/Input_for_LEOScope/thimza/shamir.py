import numpy as np
from .ring import mulmod_scalar

U64 = np.uint64


def eval_points(n_parties, q):
    return [i + 1 for i in range(n_parties)]


def share(secret, t, n_parties, q, sampler):
    shape = secret.shape
    coeffs = [secret]
    for _ in range(t - 1):
        coeffs.append(sampler.uniform(shape))
    alphas = eval_points(n_parties, q)
    shares = {}
    for i, a in enumerate(alphas):
        acc = np.zeros(shape, dtype=np.int64)
        p = 1
        for k in range(t):
            acc = (acc + mulmod_scalar(coeffs[k], p, q).astype(np.int64)) % q
            p = (p * a) % q
        shares[i + 1] = acc.astype(U64)
    return shares


def lagrange(T, i, q):
    num = 1
    den = 1
    for j in T:
        if j == i:
            continue
        num = (num * j) % q
        den = (den * ((j - i) % q)) % q
    return (num * pow(den, q - 2, q)) % q


def scalar_mul(lam, x, q):
    return mulmod_scalar(x, lam, q)


def reconstruct(T, shares, q):
    acc = None
    for i in T:
        lam = lagrange(T, i, q)
        term = scalar_mul(lam, shares[i], q)
        acc = term.astype(np.int64) if acc is None else (acc + term.astype(np.int64)) % q
    return (acc % q).astype(U64)
