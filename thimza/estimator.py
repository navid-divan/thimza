import math


def delta_bkz(beta):
    if beta <= 2:
        return 1.0219
    return ((math.pi * beta) ** (1.0 / beta) * beta / (2 * math.pi * math.e)) ** (1.0 / (2.0 * (beta - 1)))


def core_svp_classical(beta):
    return 0.292 * beta + 16.4


def core_svp_quantum(beta):
    return 0.257 * beta + 16.4


def lwe_primal_beta(n, q, sigma, m_max):
    best = None
    for beta in range(50, 1400):
        d_lo = n + 1
        d_hi = n + m_max + 1
        ok = False
        for d in range(max(d_lo, beta), d_hi + 1):
            lhs = math.sqrt(beta) * sigma
            rhs = delta_bkz(beta) ** (2 * beta - d - 1) * q ** ((d - n - 1) / d)
            if lhs <= rhs:
                ok = True
                break
        if ok:
            best = beta
            break
    return best


def lwe_bits(n, q, sigma, m_max=None, quantum=False):
    if m_max is None:
        m_max = n
    beta = lwe_primal_beta(n, q, sigma, m_max)
    if beta is None:
        return float('inf'), None
    return (core_svp_quantum(beta) if quantum else core_svp_classical(beta)), beta


def sis_beta(n, q, m, bound):
    if bound >= q:
        return None
    best = None
    for beta in range(50, 1400):
        d_opt = int(math.sqrt(n * math.log(q) / math.log(delta_bkz(beta))))
        for d in sorted({min(m, d_opt), min(m, d_opt + 1), min(m, max(d_opt - 1, beta)), m}):
            if d < beta or d <= n:
                continue
            val = delta_bkz(beta) ** d * q ** (n / d)
            if val <= bound:
                best = beta
                break
        if best is not None:
            break
    return best


def sis_bits(n, q, m, bound, quantum=False):
    beta = sis_beta(n, q, m, bound)
    if beta is None:
        return 0.0, None
    return (core_svp_quantum(beta) if quantum else core_svp_classical(beta)), beta


def smoothing(dim, eps=2.0 ** -128):
    return math.sqrt(math.log(2 * dim * (1 + 1 / eps)) / math.pi)


def gaussian_tail_factor(dim, lam=128):
    k = 2.0
    for _ in range(200):
        f = k * k - math.log(k * k) - 1 - 2 * lam * math.log(2) / dim
        fp = 2 * k - 2 / k
        k = k - f / fp
    return k
