import math
from .estimator import lwe_bits, smoothing, gaussian_tail_factor

LOG2 = math.log(2.0)
ETA_ALPHA = 1.30
FLOOD_FACTOR = 2.87
SIGMA_TD = 20.0
SMAX_C = 1.1
SMAX_ADD = 4.7


def eta(dim, lam=128):
    return smoothing(dim, 2.0 ** (-lam))


def challenge_weight(phi, lam=128):
    for kappa in range(2, 200):
        bits = kappa + sum(math.log2((phi - i) / (i + 1)) for i in range(kappa))
        if bits >= lam:
            return kappa
    raise ValueError


def sigma_gadget(b, k, lam=128):
    return 2.0 * b * math.sqrt(math.log(2 * k * (1 + 2.0 ** lam)) / math.pi)


def smax_trapdoor(sigma_td, m, k, phi):
    return SMAX_C * sigma_td * (math.sqrt(2 * m * phi) + math.sqrt(m * k * phi) + SMAX_ADD)


def derive(phi, n, m, logq, base_bits, t_max=1024, lam=128, logQ=60, sigma_td=SIGMA_TD):
    q = 1 << logq
    k = max(1, math.ceil(logq / base_bits))
    b = 2.0 ** base_bits
    dbar = 2 * m + m * k
    d = dbar + 1
    kappa = challenge_weight(phi, lam)
    sg = sigma_gadget(b, k, lam)
    smx = smax_trapdoor(sigma_td, m, k, phi)
    sigma_u = math.sqrt((sg * sg + 1) * smx * smx + eta(dbar * phi) ** 2)
    Bu = sigma_u ** 2 * 2 * phi * (phi * LOG2 + lam)
    star1 = FLOOD_FACTOR * math.sqrt(Bu)
    Bc = (kappa ** 2) * (2.0 ** logQ)
    star2 = FLOOD_FACTOR * math.sqrt(Bc)
    sigma_star = max(star1, star2)
    kcorr = gaussian_tail_factor((n + m) * phi, lam)
    B2 = kcorr * sigma_star * math.sqrt(t_max * (n + m) * phi)
    return dict(phi=phi, n=n, m=m, logq=logq, q=q, base_bits=base_bits, k=k, dbar=dbar, d=d,
                kappa=kappa, sigma_e=eta(m * phi), sigma_E=eta(dbar * phi), sigma_td=sigma_td,
                sigma_g=sg, smax=smx, sigma_u=sigma_u, sigma_star=sigma_star,
                star1=star1, star2=star2, B2=B2, t_max=t_max, logQ=logQ, lam=lam)


def bits_for_gaussian(sigma):
    return max(2, math.ceil(math.log2(max(sigma, 1.0)) + 2.6))


def sizes(P, nu, xi):
    phi, n, m, logq = P['phi'], P['n'], P['m'], P['logq']
    sigma_agg = P['sigma_star'] * math.sqrt(P['t_max'])
    vk = 32 + m * phi * (logq - xi) / 8.0
    sig = 32 + n * phi * bits_for_gaussian(sigma_agg) / 8.0
    sig += m * phi * bits_for_gaussian(sigma_agg / 2.0 ** nu) / 8.0
    off = m * P['d'] * phi * logq / 8.0
    on = n * phi * logq / 8.0
    sk = 32 + n * phi * logq / 8.0
    return dict(vk=vk, sig=sig, offline=off, online=on, total=off + on, sk=sk)


def security(P, nu, xi):
    phi, n, m, q = P['phi'], P['n'], P['m'], P['q']
    sigma_key = max(P['sigma_e'], 2.0 ** xi / math.sqrt(12))
    lwe_key = lwe_bits(n * phi, q, sigma_key, m * phi)
    lwe_td = lwe_bits(m * phi, q, P['sigma_td'], m * phi)
    return dict(lwe_key=lwe_key, lwe_td=lwe_td)
