import json
import os
import sys
import math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from thimza.models import PUBLISHED

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RES = os.path.join(BASE, 'results')
FIG = os.path.join(BASE, 'figures')
os.makedirs(FIG, exist_ok=True)

plt.rcParams.update({'font.size': 8, 'axes.labelsize': 8, 'legend.fontsize': 7,
                     'xtick.labelsize': 7, 'ytick.labelsize': 7, 'figure.dpi': 200,
                     'axes.grid': True, 'grid.alpha': 0.3, 'grid.linewidth': 0.4})

ORDER = ['Thimza', 'TRaccoon', 'TalonG', 'Hermine', 'Tanuki', 'Ringtail']
STYLE = {'Thimza': ('o-', '#1f77b4'), 'TRaccoon': ('s--', '#ff7f0e'),
         'Ringtail': ('^-.', '#2ca02c'), 'Tanuki': ('v:', '#d62728'),
         'TalonG': ('D--', '#9467bd'), 'Hermine': ('*-', '#8c564b')}
LABEL = {'Thimza': r'\textsc{Thimza} (this work)', 'TRaccoon': 'TRaccoon [EC\'24]',
         'Ringtail': 'Ringtail [S\\&P\'25]', 'Tanuki': 'EKT/Tanuki [C\'24]',
         'TalonG': 'TalonG [EC\'26]'}
PLAIN = {'Thimza': 'Thimza (this work)', 'TRaccoon': 'TRaccoon (EC 2024)',
         'Ringtail': 'Ringtail (S&P 2025)', 'Tanuki': 'EKT/Tanuki (CRYPTO 2024)',
         'TalonG': 'TalonG (EC 2026)', 'Hermine': 'Hermine (2026)'}
SHORT = {'Thimza': 'Thimza', 'TRaccoon': 'TRaccoon', 'Ringtail': 'Ringtail',
         'Tanuki': 'EKT', 'TalonG': 'TalonG', 'Hermine': 'Hermine'}
HALF = (1.70, 1.52)
FULL = (3.35, 2.25)


def halfstyle():
    plt.rcParams.update({'font.size': 6, 'axes.labelsize': 6, 'legend.fontsize': 4.6,
                         'xtick.labelsize': 5.2, 'ytick.labelsize': 5.2,
                         'axes.linewidth': 0.5, 'lines.linewidth': 0.8,
                         'xtick.major.size': 2, 'ytick.major.size': 2})


def fullstyle():
    plt.rcParams.update({'font.size': 8, 'axes.labelsize': 8, 'legend.fontsize': 7,
                         'xtick.labelsize': 7, 'ytick.labelsize': 7,
                         'axes.linewidth': 0.8, 'lines.linewidth': 1.1,
                         'xtick.major.size': 3.5, 'ytick.major.size': 3.5})


def save(fig, name):
    p = os.path.join(FIG, name + '.eps')
    fig.savefig(p, format='eps', bbox_inches='tight', pad_inches=0.02)
    plt.close(fig)
    return p


def fig_time(bench):
    halfstyle()
    fig, ax = plt.subplots(figsize=HALF)
    for k in ORDER:
        ts = [r['t'] for r in bench[k]]
        ys = [r['sign'] for r in bench[k]]
        st, col = STYLE[k]
        ax.loglog(ts, ys, st, color=col, ms=2.0, label=SHORT[k])
    ax.set_xlabel('threshold $t$')
    ax.set_ylabel('signing time (ms)')
    ax.set_xticks([2, 8, 32, 128, 512])
    ax.set_xticklabels(['2', '8', '32', '128', '512'])
    ax.legend(loc='upper left', frameon=False)
    return save(fig, 'fig_time_vs_t')


def fig_comm(bench):
    halfstyle()
    fig, ax = plt.subplots(figsize=HALF)
    for k in ORDER:
        ts = [r['t'] for r in bench[k]]
        ys = [r['sizes']['total'] / 1024.0 for r in bench[k]]
        st, col = STYLE[k]
        ax.loglog(ts, ys, st, color=col, ms=2.0, label=SHORT[k])
    ax.set_xlabel('threshold $t$')
    ax.set_ylabel('communication (KiB)')
    ax.set_xticks([2, 8, 32, 128, 512])
    ax.set_xticklabels(['2', '8', '32', '128', '512'])
    ax.legend(loc='center left', frameon=False)
    return save(fig, 'fig_comm_vs_t')


def fig_breakdown(bench):
    halfstyle()
    fig, ax = plt.subplots(figsize=HALF)
    names = ORDER
    r1 = [bench[k][-1]['sizes']['r1'] / 1024 for k in names]
    r2 = [bench[k][-1]['sizes']['r2'] / 1024 for k in names]
    r3 = [bench[k][-1]['sizes']['r3'] / 1024 for k in names]
    x = np.arange(len(names))
    ax.bar(x, r1, 0.55, label='round 1', color='#4c78a8')
    ax.bar(x, r2, 0.55, bottom=r1, label='round 2', color='#f58518')
    ax.bar(x, r3, 0.55, bottom=np.array(r1) + np.array(r2), label='round 3', color='#54a24b')
    ax.set_yscale('log')
    ax.set_xticks(x)
    ax.set_xticklabels([SHORT[x] for x in names], rotation=32, ha='right')
    ax.set_ylabel('KiB per signer, $t=1024$')
    ax.legend(frameon=False, ncol=3, loc='upper center', fontsize=4.4,
              columnspacing=0.8, handlelength=1.1)
    ax.set_ylim(1e-2, 3e3)
    return save(fig, 'fig_breakdown')


def fig_pareto(bench):
    halfstyle()
    fig, ax = plt.subplots(figsize=HALF)
    for k in ORDER:
        s = bench[k][-1]['sizes']
        st, col = STYLE[k]
        ax.scatter(s['total'] / 1024.0, s['sig'] / 1024.0, s=16, color=col, marker=st[0],
                   edgecolors='k', linewidths=0.3, zorder=3, label=SHORT[k])
    for p in PUBLISHED:
        if p['maxT'] >= 1024 or p['key'] in ('CTZ24', 'GKS24', 'dPN25'):
            ax.scatter(p['trans'], p['sig'], s=8, color='0.55', marker='x', zorder=2)
            ax.annotate(p['key'], (p['trans'], p['sig']), fontsize=4.0, color='0.35',
                        xytext=(1.5, 1.5), textcoords='offset points')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.set_xlabel('communication (KiB)')
    ax.set_ylabel('signature size (KiB)')
    ax.legend(frameon=False, loc='upper left', fontsize=4.4, handletextpad=0.3)
    return save(fig, 'fig_pareto')


def fig_mask(bench):
    fullstyle()
    fig, ax = plt.subplots(figsize=FULL)
    ts = np.array([2, 4, 8, 16, 32, 64, 128, 256, 512, 1024])
    unit = 4 * 512 * 49 / 8.0 / 1024.0
    ax.loglog(ts, 2 * ts * unit, 's--', color='#ff7f0e', ms=3.2, lw=1.1,
              label='ordered pairs (TRaccoon, EKT, Ringtail)')
    ax.loglog(ts, (ts - 1) * unit, 'o-', color='#1f77b4', ms=3.2, lw=1.1,
              label='antisymmetric (Thimza)')
    ax.loglog(ts, (ts - 1) * unit, 'k:', lw=0.9, label='lower bound (Thm.~4.4)')
    ax.set_xlabel('threshold $t$')
    ax.set_ylabel('pseudorandom material / signer (KiB)')
    ax.legend(frameon=False, loc='upper left', fontsize=6.2)
    return save(fig, 'fig_mask')


def fig_wan(bench):
    fullstyle()
    fig, ax = plt.subplots(figsize=FULL)
    rtt = 170.0
    bw = 183.23e6 / 8.0
    names = ORDER
    onl = []
    tot = []
    for k in names:
        row = [r for r in bench[k] if r['t'] == 64][0]
        s = row['sizes']
        ors = {'Thimza': 3, 'TRaccoon': 3, 'Ringtail': 1, 'Tanuki': 1, 'TalonG': 2,
               'Hermine': 1}[k]
        online_bytes = {'Thimza': s['total'], 'TRaccoon': s['total'], 'Ringtail': s['r2'],
                        'Tanuki': s['r2'], 'TalonG': s['total'], 'Hermine': s['r2']}[k]
        onl.append(ors * rtt + 1000.0 * online_bytes / bw + row['sign'])
        tot.append({'Thimza': 3, 'TRaccoon': 3, 'Ringtail': 2, 'Tanuki': 2, 'TalonG': 2,
                    'Hermine': 2}[k] * rtt + 1000.0 * s['total'] / bw + row['sign'])
    x = np.arange(len(names))
    ax.bar(x - 0.2, onl, 0.38, label='online phase', color='#4c78a8')
    ax.bar(x + 0.2, tot, 0.38, label='offline + online', color='#e45756')
    ax.set_xticks(x)
    ax.set_xticklabels([SHORT[x] for x in names], rotation=15, ha='right')
    ax.set_ylabel('modelled WAN latency (ms), $t=64$')
    ax.set_yscale('log')
    ax.legend(frameon=False, fontsize=6.5)
    return save(fig, 'fig_wan')


def fig_complexity():
    fullstyle()
    fig, ax = plt.subplots(figsize=FULL)
    ts = np.logspace(0, 3, 60)
    phi, ell, k = 512, 4, 5
    logphi = math.log2(phi)
    thim = (k + ell) * phi * logphi + ts * ell * phi
    trac = 2 * (k + ell) * phi * logphi + 3 * ts * ell * phi
    ring = 8 * (7 + 1) * 49 * 256 * math.log2(256) / 4 + 2 * ts * 7 * 256
    ringv = np.full_like(ts, 0.0) + 8 * 49 * (7 + 1) * 256 * math.log2(256) + 2 * ts * 7 * 256 + 256 * 64 * 48
    tan = 11 * 9 * 15 * 256 * math.log2(256) + 2 * ts * 9 * 256
    herm = 4 * 4 * 13 * 512 * math.log2(512) + ts * 8 * 512
    th64 = ts[ts <= 64]
    ax.loglog(th64, (4 * 4 * 13 * 512 * math.log2(512) + th64 * 8 * 512) / 1e6, '-',
              color='#8c564b', lw=1.2, label='Hermine (t<=64)')
    ax.loglog(ts, thim / 1e6, '-', color='#1f77b4', lw=1.2, label='Thimza')
    ax.loglog(ts, trac / 1e6, '--', color='#ff7f0e', lw=1.2, label='TRaccoon')
    ax.loglog(ts, ringv / 1e6, '-.', color='#2ca02c', lw=1.2, label='Ringtail')
    ax.loglog(ts, tan / 1e6, ':', color='#d62728', lw=1.2, label='EKT/Tanuki')
    ax.set_xlabel('threshold $t$')
    ax.set_ylabel(r'modelled $R_q$-operations ($\times 10^6$)')
    ax.legend(frameon=False, loc='upper left', fontsize=6.5)
    return save(fig, 'fig_complexity')




def fig_speedup(bench):
    halfstyle()
    fig, ax = plt.subplots(figsize=HALF)
    ts = [r['t'] for r in bench['Thimza']]
    base = [r['sign'] for r in bench['Thimza']]
    for k in ['TalonG', 'TRaccoon', 'Tanuki', 'Ringtail']:
        ys = [r['sign'] / b for r, b in zip(bench[k], base)]
        st, col = STYLE[k]
        ax.semilogx(ts, ys, st, color=col, ms=2.0, label=SHORT[k])
    ax.axhline(1.0, color='k', lw=0.8, ls=':')
    ax.set_xlabel('threshold $t$')
    ax.set_ylabel('time relative to Thimza')
    ax.set_xticks([2, 8, 32, 128, 512])
    ax.set_xticklabels(['2', '8', '32', '128', '512'])
    ax.legend(frameon=False, fontsize=4.6, loc='upper left', handletextpad=0.3)
    return save(fig, 'fig_speedup')


def fig_levels():
    import json as _json
    halfstyle()
    p = os.path.join(RES, 'sizes_levels.json')
    d = _json.load(open(p))
    fig, ax = plt.subplots(figsize=HALF)
    labels = ['I', 'III', 'V']
    keys = ['128', '192', '256']
    x = np.arange(3)
    w = 0.17
    for idx, nm in enumerate(['Thimza', 'TRaccoon', 'EKT', 'Ringtail', 'TalonG']):
        vals = []
        for kk in keys:
            vals.append(d[kk][nm]['total'] / 1024.0 if nm in d[kk] else 0.0)
        ax.bar(x + (idx - 2) * w, vals, w, label=nm)
    ax.set_yscale('log')
    ax.set_xticks(x)
    ax.set_xticklabels(['level I', 'level III', 'level V'])
    ax.set_ylabel('communication (KiB)')
    ax.legend(frameon=False, fontsize=4.4, ncol=2, columnspacing=0.7, handlelength=1.0)
    return save(fig, 'fig_levels')


def main():
    bench = json.load(open(os.path.join(RES, 'bench.json')))
    outs = [fig_time(bench), fig_comm(bench), fig_breakdown(bench), fig_pareto(bench),
            fig_mask(bench), fig_wan(bench), fig_complexity(), fig_speedup(bench), fig_levels()]
    for o in outs:
        print('wrote', o)


if __name__ == '__main__':
    main()
