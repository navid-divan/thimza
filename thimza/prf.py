import hashlib
import numpy as np

U64 = np.uint64


def xof(domain, *parts, outlen=32):
    h = hashlib.shake_256()
    h.update(domain.encode())
    for p in parts:
        if isinstance(p, bytes):
            b = p
        elif isinstance(p, str):
            b = p.encode()
        elif isinstance(p, int):
            b = int(p).to_bytes(8, 'little', signed=True)
        elif isinstance(p, np.ndarray):
            b = np.ascontiguousarray(p, dtype=U64).tobytes()
        elif isinstance(p, (list, tuple)):
            b = b''.join(int(v).to_bytes(8, 'little', signed=True) for v in p)
        else:
            b = repr(p).encode()
        h.update(len(b).to_bytes(4, 'little'))
        h.update(b)
    return h.digest(outlen)


def stream_u64(seed_bytes, count):
    raw = hashlib.shake_256(seed_bytes).digest(8 * count)
    return np.frombuffer(raw, dtype=U64).copy()


def uniform_rq(seed_bytes, shape, q):
    n = int(np.prod(shape))
    v = stream_u64(seed_bytes, n)
    return (v % U64(q)).reshape(shape)


def prf_uniform(seed_bytes, label, shape, q):
    s = hashlib.shake_256(seed_bytes + b'|' + label).digest(32)
    return uniform_rq(s, shape, q)


def hash_challenge(rng_seed, phi, kappa, q):
    raw = hashlib.shake_256(rng_seed).digest(4 * 4 * kappa + 64)
    c = np.zeros(phi, dtype=U64)
    pos = 0
    picked = 0
    used = set()
    while picked < kappa:
        if pos + 5 > len(raw):
            raw = raw + hashlib.shake_256(raw).digest(256)
        idx = int.from_bytes(raw[pos:pos + 4], 'little') % phi
        sgn = raw[pos + 4] & 1
        pos += 5
        if idx in used:
            continue
        used.add(idx)
        c[idx] = U64(1) if sgn == 0 else U64(q - 1)
        picked += 1
    return c


def hash_monomials(seed_bytes, rep, phi, q):
    raw = hashlib.shake_256(seed_bytes).digest(5 * rep + 32)
    out = np.zeros((rep, phi), dtype=U64)
    out[0, 0] = U64(1)
    for b in range(1, rep):
        idx = int.from_bytes(raw[5 * b:5 * b + 4], 'little') % phi
        sgn = raw[5 * b + 4] & 1
        out[b, idx] = U64(1) if sgn == 0 else U64(q - 1)
    return out


def hash_gaussian(seed_bytes, shape, sigma, q):
    n = int(np.prod(shape))
    raw = hashlib.shake_256(seed_bytes).digest(8 * n)
    u = np.frombuffer(raw, dtype=U64).astype(np.float64) / float(1 << 64)
    u = np.clip(u, 1e-15, 1 - 1e-15)
    v = np.sqrt(2.0) * _erfinv(2 * u - 1) * sigma
    z = np.rint(v).astype(np.int64)
    return (z % np.int64(q)).astype(U64).reshape(shape)


def _erfinv(x):
    a = 0.147
    ln1 = np.log(np.maximum(1 - x * x, 1e-300))
    t1 = 2 / (np.pi * a) + ln1 / 2
    return np.sign(x) * np.sqrt(np.maximum(np.sqrt(t1 * t1 - ln1 / a) - t1, 0.0))
