import numpy as np
from .prf import prf_uniform

U64 = np.uint64


def pair_key(i, j):
    return (min(i, j), max(i, j))


def gen_seeds_pairwise(n_parties, rng):
    seeds = {}
    for i in range(1, n_parties + 1):
        for j in range(i + 1, n_parties + 1):
            seeds[(i, j)] = rng.bytes(32)
    return seeds


def gen_seeds_ordered(n_parties, rng):
    seeds = {}
    for i in range(1, n_parties + 1):
        for j in range(1, n_parties + 1):
            seeds[(i, j)] = rng.bytes(32)
    return seeds


def antisymmetric_mask(i, T, seeds, view, shape, q):
    acc = np.zeros(shape, dtype=np.int64)
    calls = 0
    for j in T:
        if j == i:
            continue
        v = prf_uniform(seeds[pair_key(i, j)], view, shape, q).astype(np.int64)
        if i < j:
            acc = (acc + v) % q
        else:
            acc = (acc - v) % q
        calls += 1
    return acc.astype(U64), calls


def row_column_masks(i, T, seeds, label, shape, q):
    row = np.zeros(shape, dtype=np.int64)
    col = np.zeros(shape, dtype=np.int64)
    calls = 0
    for j in T:
        row = (row + prf_uniform(seeds[(i, j)], label, shape, q).astype(np.int64)) % q
        col = (col + prf_uniform(seeds[(j, i)], label, shape, q).astype(np.int64)) % q
        calls += 2
    return row.astype(U64), col.astype(U64), calls
