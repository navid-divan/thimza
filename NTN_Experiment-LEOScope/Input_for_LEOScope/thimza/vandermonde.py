import numpy as np

U64 = np.uint64


def vand_share(x, P, T, idx, shr, sampler, sigma, q):
    if T == 1:
        for i in P:
            shr.setdefault(i, {})[idx] = x
        return shr
    N = len(P)
    b = N // 2
    PL, PR = P[:b], P[b:]
    lo = max(0, T - (N - b))
    hi = min(T, b)
    for k in range(lo, hi + 1):
        idxL = idx + ':L:' + str(k)
        idxR = idx + ':R:' + str(T - k)
        if k == 0:
            shr = vand_share(x, PR, T, idxR, shr, sampler, sigma, q)
        elif k == T:
            shr = vand_share(x, PL, T, idxL, shr, sampler, sigma, q)
        else:
            xL = sampler.gaussian(x.shape, sigma)
            xR = ((x.astype(np.int64) - xL.astype(np.int64)) % np.int64(q)).astype(U64)
            shr = vand_share(xL, PL, k, idxL, shr, sampler, sigma, q)
            shr = vand_share(xR, PR, T - k, idxR, shr, sampler, sigma, q)
    return shr


def vand_recover(P, act, idx, out):
    N = len(P)
    T = len(act)
    if T == 1:
        for i in act:
            out[i] = idx
        return out
    b = N // 2
    PL, PR = P[:b], P[b:]
    actL = [i for i in act if i in PL]
    actR = [i for i in act if i in PR]
    k = len(actL)
    idxL = idx + ':L:' + str(k)
    idxR = idx + ':R:' + str(T - k)
    if k == 0:
        return vand_recover(PR, actR, idxR, out)
    if k == T:
        return vand_recover(PL, actL, idxL, out)
    out = vand_recover(PL, actL, idxL, out)
    out = vand_recover(PR, actR, idxR, out)
    return out


def share_count(N, T):
    shr = {}

    class _S:
        def gaussian(self, shape, sigma):
            return np.zeros(shape, dtype=U64)

    vand_share(np.zeros((1, 1), dtype=U64), list(range(1, N + 1)), T, '', shr, _S(), 1.0, 3)
    return max(len(v) for v in shr.values())
