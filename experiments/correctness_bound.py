import json
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from thimza.params import THIMZA
from thimza.core import RaccoonCore

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'results')


def run(level=128, trials=200):
    P = THIMZA[level]
    C = RaccoonCore(P, seed=1)
    phi, k, ell = C.phi, C.k, C.ell
    sw = C.sigma_w
    B = C.signature_bound()
    rows = []
    rng = np.random.default_rng(2024)
    for t in (4, 16, 64, 256, 1024):
        worst = 0.0
        for _ in range(trials):
            z = rng.normal(0.0, sw * math.sqrt(t), size=ell * phi)
            e = rng.normal(0.0, sw * math.sqrt(t), size=k * phi)
            d = rng.uniform(-0.5, 0.5, size=(t, k * phi)).sum(axis=0) * (2.0 ** P['nu_c'])
            cr = rng.uniform(-0.5, 0.5, size=k * phi) * (2.0 ** P['nu_t']) * P['omega'] / math.sqrt(3)
            tot = math.sqrt(float(np.sum(z * z)) + float(np.sum((e + d + cr) ** 2)))
            worst = max(worst, tot)
        rows.append(dict(t=t, worst=worst, bound=B, ratio=worst / B,
                         delta_std=(2.0 ** P['nu_c']) * math.sqrt(t / 12.0),
                         noise_std=sw * math.sqrt(t)))
    return rows


def main():
    rows = run()
    for r in rows:
        print('t=%5d  max||(z,2^nu h)||=%.4e  B=%.4e  ratio=%.3f  delta/noise=%.4f'
              % (r['t'], r['worst'], r['bound'], r['ratio'], r['delta_std'] / r['noise_std']))
    with open(os.path.join(OUT, 'correctness_bound.json'), 'w') as f:
        json.dump(rows, f, indent=1)


if __name__ == '__main__':
    main()
