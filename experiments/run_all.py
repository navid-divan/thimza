import json
import os
import sys
import time
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from thimza.params import THIMZA, TRACCOON, RINGTAIL, TANUKI, TALONG, HERMINE
from thimza.schemes.thimza_scheme import Thimza
from thimza.schemes.prior import TRaccoon, Ringtail, Tanuki
from thimza.schemes.talong import TalonG
from thimza.schemes.hermine import Hermine

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'results')
os.makedirs(OUT, exist_ok=True)
REP = 3


def timeit(fn, rep=REP):
    best = float('inf')
    out = None
    for _ in range(rep):
        t0 = time.perf_counter()
        out = fn()
        dt = time.perf_counter() - t0
        best = min(best, dt)
    return best * 1000.0, out


def correctness():
    res = {}
    for name, cls, P in [('Thimza', Thimza, THIMZA[128]), ('TRaccoon', TRaccoon, TRACCOON[128]),
                         ('Ringtail', Ringtail, RINGTAIL[128]), ('Tanuki', Tanuki, TANUKI[128]),
                         ('TalonG', TalonG, TALONG[128]), ('Hermine', Hermine, HERMINE[128])]:
        ok = []
        for (t, n) in [(2, 3), (3, 5), (4, 6), (5, 8), (7, 10)]:
            S = cls(P, seed=t * 17 + n)
            S.keygen(t, n)
            T = list(range(1, t + 1))
            msg = b'thimza-kat-%d-%d' % (t, n)
            ok.append(bool(run_protocol(S, name, T, msg, t)))
        res[name] = ok
    return res


def run_protocol(S, name, T, msg, t):
    if name == 'Thimza':
        st = {}
        cm = {}
        for i in T:
            st[i], (c,) = S.round1(i, msg)
            cm[i] = c
        wb = {i: S.round2(st[i])[0] for i in T}
        zs = []
        for i in T:
            zi, c, w, _ = S.round3(i, st[i], T, msg, [cm[j] for j in T], [wb[j] for j in T])
            zs.append(zi)
        sig = S.combine(T, msg, zs, c, w)
        return S.verify(msg, sig, t)
    if name == 'TRaccoon':
        sid = b'sid'
        st = {}
        c1 = {}
        for i in T:
            st[i], c1[i] = S.round1(i, msg, T, sid)
        for i in T:
            S.round2(i, st[i], T, msg, sid, [c1[j] for j in T])
        zs = []
        for i in T:
            zi, c, w, _ = S.round3(i, st[i], T, msg, sid, [st[j][1] for j in T])
            zs.append(zi)
        sig = S.combine(T, msg, zs, [c1[j][1] for j in T], c, w)
        return S.verify(msg, sig, t)
    if name in ('Ringtail', 'Tanuki', 'Hermine'):
        st = {}
        D = {}
        for i in T:
            st[i], D[i] = S.sign1(i)
        zs = []
        for i in T:
            zi, c, w, _ = S.sign2(i, st[i], T, msg, [D[j] for j in T])
            zs.append(zi)
        sig = S.combine(T, msg, zs, c, w)
        return S.verify(msg, sig, t)
    if name == 'TalonG':
        st = {}
        wt = {}
        for i in T:
            st[i], wt[i] = S.sign1(i, msg)
        ps = []
        for i in T:
            p, c, wr, _ = S.sign2(i, st[i], T, msg, [wt[j] for j in T])
            ps.append(p)
        sig = S.combine(T, msg, ps, c, wr)
        return S.verify(msg, sig, t)
    raise ValueError(name)


def bench_party(t_list=(2, 4, 8, 16, 32, 64, 128, 256, 512, 1024)):
    out = {}
    n = 1024
    msg = b'benchmark-message'
    for name, cls, P in [('Thimza', Thimza, THIMZA[128]), ('TRaccoon', TRaccoon, TRACCOON[128]),
                         ('Ringtail', Ringtail, RINGTAIL[128]), ('Tanuki', Tanuki, TANUKI[128]),
                         ('TalonG', TalonG, TALONG[128]), ('Hermine', Hermine, HERMINE[128])]:
        rows = []
        for t in t_list:
            if name == 'Hermine':
                if t > 64:
                    continue
                S3 = cls(P, seed=11)
                tk, _ = timeit(lambda: S3.keygen(t, t), rep=1)
                S4 = cls(P, seed=11)
                S4.keygen(t, t)
                rows.append(bench_one(S4, name, t, msg, tk))
                continue
            S = cls(P, seed=11)
            tk, _ = timeit(lambda: S.keygen(min(t, 8), max(t, 8) if t > 8 else 8), rep=1)
            S2 = cls(P, seed=11)
            S2.keygen(min(t, 8), max(t, 8))
            T = list(range(1, min(t, 8) + 1))
            Tfull = list(range(1, t + 1)) if t <= 8 else list(range(1, 9))
            rows.append(bench_one(S2, name, t, msg, tk))
        out[name] = rows
        print(name, 'done')
    return out


def synth_peers(S, name, t, own):
    if name in ('Ringtail', 'Tanuki'):
        return [own] * t
    if name == 'Thimza':
        return [own] * t
    if name == 'TRaccoon':
        return [own] * t
    if name == 'TalonG':
        return [own] * t
    raise ValueError(name)


def bench_one(S, name, t, msg, tk):
    Tsim = list(range(1, min(t, S.n_parties) + 1))
    Tbig = list(range(1, t + 1))
    seeds = getattr(S, 'sk', {}).get('seeds', None) if hasattr(S, 'sk') else None
    if name == 'Thimza':
        S.sk['seeds'] = _extend_pairwise(S.sk['seeds'], t)
        t1, st = timeit(lambda: S.round1(1, msg))
        state, (cmt,) = st
        wb = S.round2(state)[0]
        t2, _ = timeit(lambda: S.round2(state))
        cmts = [cmt] * t
        wbs = [wb] * t
        t3, r3 = timeit(lambda: S.round3(1, state, Tbig, msg, cmts, wbs))
        return dict(t=t, keygen=tk, r1=t1, r2=t2, r3=t3, sign=t1 + t2 + t3,
                    sizes=S.sizes(t))
    if name == 'TRaccoon':
        S.sk['seeds'] = _extend_ordered(S.sk['seeds'], t)
        S.sk['mac'] = _extend_ordered(S.sk['mac'], t)
        sid = b'sid'
        t1, st = timeit(lambda: S.round1(1, msg, Tbig, sid))
        state, c1 = st
        t2, _ = timeit(lambda: S.round2(1, state, Tbig, msg, sid, [c1] * t))
        ws = [state[1]] * t
        t3, _ = timeit(lambda: S.round3(1, state, Tbig, msg, sid, ws))
        return dict(t=t, keygen=tk, r1=t1, r2=t2, r3=t3, sign=t1 + t2 + t3, sizes=S.sizes(t))
    if name == 'Hermine':
        t1, st = timeit(lambda: S.sign1(1))
        state, D = st
        Tbig = list(range(1, t + 1))
        t2, _ = timeit(lambda: S.sign2(1, state, Tbig, msg, [D] * t))
        return dict(t=t, keygen=tk, r1=t1, r2=t2, r3=0.0, sign=t1 + t2, sizes=S.sizes(t))
    if name in ('Ringtail', 'Tanuki'):
        S.sk['seeds'] = _extend_ordered(S.sk['seeds'], t)
        t1, st = timeit(lambda: S.sign1(1))
        state, D = st
        t2, _ = timeit(lambda: S.sign2(1, state, Tbig, msg, [D] * t))
        return dict(t=t, keygen=tk, r1=t1, r2=t2, r3=0.0, sign=t1 + t2, sizes=S.sizes(t))
    if name == 'TalonG':
        S.seeds = _extend_ordered(S.seeds, t)
        t1, st = timeit(lambda: S.sign1(1, msg))
        state, wt = st
        t2, _ = timeit(lambda: S.sign2(1, state, Tbig, msg, [wt] * t))
        return dict(t=t, keygen=tk, r1=t1, r2=t2, r3=0.0, sign=t1 + t2, sizes=S.sizes(t))
    raise ValueError(name)


def _extend_pairwise(seeds, t):
    rng = np.random.default_rng(99)
    for i in range(1, t + 1):
        for j in range(i + 1, t + 1):
            if (i, j) not in seeds:
                seeds[(i, j)] = rng.bytes(32)
    return seeds


def _extend_ordered(seeds, t):
    rng = np.random.default_rng(98)
    for i in range(1, t + 1):
        for j in range(1, t + 1):
            if (i, j) not in seeds:
                seeds[(i, j)] = rng.bytes(32)
    return seeds


def main():
    print('correctness ...')
    corr = correctness()
    print(json.dumps(corr, indent=1))
    with open(os.path.join(OUT, 'correctness.json'), 'w') as f:
        json.dump(corr, f, indent=1)
    print('benchmarks ...')
    b = bench_party()
    with open(os.path.join(OUT, 'bench.json'), 'w') as f:
        json.dump(b, f, indent=1)
    print('written to', OUT)


if __name__ == '__main__':
    main()
