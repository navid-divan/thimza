"""Numerical check of the verification bound B.

For every level and threshold t the script draws honest signatures from their exact distribution
and records the largest value of ||(z, 2^nu_w h)||_2 / B. The masks cancel and the Lagrange
combination of the shares equals s, so z = c s + sum_j r_j and the hint is computed from the
aggregate of the truncated commitments exactly as in Combine; the signature is then checked by
the Raccoon verifier. The empirical coordinate variance of 2^nu_w h is compared with the value v
used by raccoon_B in thimza/params.py.
"""
import json
import math
import os
import sys
import time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from thimza.params import THIMZA
from thimza.core import RaccoonCore
from thimza.ring import hi_bits
from thimza.prf import xof

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'results')
U64 = np.uint64


def model_variance(P):
    T = P['Tmax']
    sw, st = 2.0 ** P['log_sigma_w'], 2.0 ** P['log_sigma_t']
    return (T * sw * sw + P['omega'] * st * st + P['omega'] * 4.0 ** P['nu_t'] / 12.0
            + T * 4.0 ** P['nu_c'] / 12.0 + 4.0 ** P['nu_w'] / 6.0)


def centred(x, q):
    x = np.asarray(x, dtype=np.int64)
    return np.where(x > q // 2, x - q, x)


def honest_signature(C, nu_c, s, t, msg):
    """One honest signature for a signer set of size t, drawn from its exact distribution."""
    R, q = C.R, C.q
    W = np.zeros((C.k, C.phi), dtype=np.int64)
    rsum = np.zeros((C.ell, C.phi), dtype=np.int64)
    sh = np.int64(1 << nu_c)
    for _ in range(t):
        r = C.smp.gaussian((C.ell, C.phi), C.sigma_w)
        ep = C.smp.gaussian((C.k, C.phi), C.sigma_w)
        w = R.add(R.intt(R.matmul(C.A_hat, R.ntt(r))), ep)
        wbar = hi_bits(w, nu_c, q) % U64(q >> nu_c)
        W = (W + wbar.astype(np.int64) * sh) % np.int64(q)
        rsum = (rsum + r.astype(np.int64)) % np.int64(q)
    qw = q >> C.nu_w
    w_agg = hi_bits(W.astype(U64), C.nu_w, q) % U64(qw)
    c = C.challenge(C.vkb, w_agg, msg)
    cs = R.intt(R.mul(np.broadcast_to(R.ntt(c), (C.ell, C.phi)), R.ntt(s)))
    z = R.add(cs, rsum.astype(U64))
    Az = R.intt(R.matmul(C.A_hat, R.ntt(z)))
    t_full = ((np.asarray(C.t_pk, dtype=np.int64) * np.int64(1 << C.nu_t)) % np.int64(q)).astype(U64)
    ct = R.intt(R.mul(np.broadcast_to(R.ntt(c), (C.k, C.phi)), R.ntt(t_full)))
    hb = hi_bits(R.sub(Az, ct), C.nu_w, q) % U64(qw)
    h = (w_agg.astype(np.int64) - hb.astype(np.int64)) % np.int64(qw)
    h = np.where(h > (qw >> 1), h - np.int64(qw), h)
    return (c, z, h)


def run_level(level, plan):
    P = THIMZA[level]
    C = RaccoonCore(P, seed=4000 + level)
    C.setup()
    s = C.smp.gaussian((C.ell, C.phi), C.sigma_t)
    e = C.smp.gaussian((C.k, C.phi), C.sigma_t)
    C.t_pk = C.pk_from_secret(C.R.ntt(s), e)
    C.vkb = xof('thimza/vk', C.Ahat_seed, C.t_pk, outlen=P['n_H'] // 8)
    B = C.signature_bound()
    v_model = model_variance(P)
    rows = []
    for t, trials in plan:
        worst, acc, cnt, ok = 0.0, 0.0, 0, True
        t0 = time.time()
        for j in range(trials):
            msg = b'corr-%d-%d-%d' % (level, t, j)
            c, z, h = honest_signature(C, P['nu_c'], s, t, msg)
            ok = ok and C.verify(C.vkb, C.t_pk, msg, (c, z, h), B)
            zc = centred(z, C.q).astype(np.float64)
            hs = h.astype(np.float64) * float(1 << C.nu_w)
            nrm = math.sqrt(float(np.sum(zc * zc)) + float(np.sum(hs * hs)))
            worst = max(worst, nrm)
            acc += float(np.sum(hs * hs))
            cnt += hs.size
        v_emp = acc / cnt
        v_t = v_model - (P['Tmax'] - t) * (2.0 ** (2 * P['log_sigma_w']) + 4.0 ** P['nu_c'] / 12.0)
        rows.append(dict(level=level, t=t, trials=trials, worst=worst, bound=B, ratio=worst / B,
                         all_verified=bool(ok), var_h_empirical=v_emp, var_h_model=v_t,
                         seconds=round(time.time() - t0, 1)))
        print('level %3d t=%5d trials=%4d  max/B=%.4f  verified=%s  var(2^nu h): emp/model=%.4f  (%.0fs)'
              % (level, t, trials, worst / B, ok, v_emp / v_t, time.time() - t0), flush=True)
    return rows


def main():
    plans = {128: [(2, 200), (16, 200), (128, 100), (1024, 40)],
             192: [(2, 100), (128, 50), (1024, 20)],
             256: [(2, 100), (128, 50), (1024, 20)]}
    rows = []
    for level, plan in plans.items():
        rows += run_level(level, plan)
    with open(os.path.join(OUT, 'correctness_bound.json'), 'w') as f:
        json.dump(rows, f, indent=1)


if __name__ == '__main__':
    main()
