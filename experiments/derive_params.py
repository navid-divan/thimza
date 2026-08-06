import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from thimza.derive import derive, sizes, challenge_weight
from thimza.estimator import lwe_bits, sis_bits
from thimza.params import THIMZA

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'results')
os.makedirs(OUT, exist_ok=True)

VALIDATION = [
    ('Kyber-512', 512, 3329, 1.22, 512, 118),
    ('Kyber-768', 768, 3329, 1.00, 768, 183),
    ('Kyber-1024', 1024, 3329, 1.00, 1024, 256),
    ('Dilithium-2', 1024, 8380417, 1.22, 1024, 123),
    ('Dilithium-3', 1280, 8380417, 0.82, 1536, None),
]


def validate_estimator():
    rows = []
    for name, n, q, sig, m, pub in VALIDATION:
        bits, beta = lwe_bits(n, q, sig, m)
        rows.append(dict(name=name, n=n, logq=int(q).bit_length(), beta=beta,
                         core_svp=round(0.292 * beta, 1), published=pub))
    return rows


def reproduce_ringtail():
    P = derive(256, 7, 8, 48, 12)
    nu = int(math.floor(math.log2(P['sigma_u']))) + 2
    S = sizes(P, nu, nu + 1)
    return dict(kappa=P['kappa'], published_kappa=23,
                log_sigma_u=round(math.log2(P['sigma_u']), 2), published_log_sigma_u=27.2,
                log_sigma_star=round(math.log2(P['sigma_star']), 2), published_log_sigma_star=37.3,
                log_B2=round(math.log2(P['B2']), 2), published_log_B2=48.6,
                nu=nu, xi=nu + 1, published_nu=29, published_xi=30,
                offline=round(S['offline']), published_offline=602112,
                online=round(S['online']), published_online=10752)


def two_round_design_space():
    rows = []
    for phi, n, m, bb in [(256, 7, 8, 12), (1024, 2, 3, 8), (2048, 1, 1, 6), (2048, 1, 1, 10)]:
        best = None
        for logq in range(40, 52):
            P = derive(phi, n, m, logq, bb)
            need = math.log2(P['sigma_star'] * math.sqrt(P['t_max']) * 1.16) + 5.4
            if logq < need or logq > need + 1.0:
                continue
            nu = int(math.floor(math.log2(P['sigma_u']))) + 2
            if nu >= logq - 2:
                continue
            S = sizes(P, nu, nu + 1)
            best = dict(phi=phi, ell=n, k=m, dbar=P['dbar'], logq=logq,
                        offline=round(S['offline']), online=round(S['online']),
                        sig=round(S['sig']))
            break
        if best:
            rows.append(best)
    return rows


def thimza_summary():
    out = {}
    for lev, P in THIMZA.items():
        sigma_w = 2.0 ** P['log_sigma_w']
        out[lev] = dict(phi=P['phi'], logq=P['logq'], ell=P['ell'], k=P['k'], omega=P['omega'],
                        log_sigma_w_agg=round(math.log2(sigma_w * math.sqrt(P['Tmax'])), 1),
                        nu_t=P['nu_t'], nu_w=P['nu_w'], nu_c=P['nu_c'],
                        nu_c_rule=int(math.floor(P['log_sigma_w'])) - 1,
                        delta_ratio=round(2.0 ** P['nu_c'] / (sigma_w * math.sqrt(12.0)), 4))
    return out


def main():
    res = dict(estimator=validate_estimator(), ringtail=reproduce_ringtail(),
               design_space=two_round_design_space(), thimza=thimza_summary())
    print('--- estimator validation (classical core-SVP) ---')
    for r in res['estimator']:
        print('%-12s n=%5d logq=%2d beta=%4d ours=%6.1f published=%s'
              % (r['name'], r['n'], r['logq'], r['beta'], r['core_svp'], r['published']))
    print()
    print('--- re-derivation of the Ringtail level I parameter set ---')
    for k, v in res['ringtail'].items():
        print('  %-24s %s' % (k, v))
    print()
    print('--- two-round design space ---')
    for r in res['design_space']:
        print('  phi=%4d (l,k)=(%d,%d) dbar=%2d logq=%2d offline=%7d online=%6d sig=%6d'
              % (r['phi'], r['ell'], r['k'], r['dbar'], r['logq'], r['offline'], r['online'], r['sig']))
    print()
    print('--- Thimza parameter sets ---')
    for lev, v in res['thimza'].items():
        print('  level %3d: %s' % (lev, v))
    with open(os.path.join(OUT, 'params.json'), 'w') as f:
        json.dump(res, f, indent=1)


if __name__ == '__main__':
    main()
