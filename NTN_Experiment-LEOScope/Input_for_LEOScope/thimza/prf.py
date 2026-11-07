import hashlib
import numpy as np

U64 = np.uint64


def _ser(p):
    if isinstance(p, bytes):
        return p
    if isinstance(p, str):
        return p.encode()
    if isinstance(p, (int, np.integer)):
        return int(p).to_bytes(8, 'little', signed=True)
    if isinstance(p, np.ndarray):
        return np.ascontiguousarray(p, dtype=U64).tobytes()
    if isinstance(p, (list, tuple)):
        return b''.join(_ser(v) for v in p)
    return repr(p).encode()


def xof(domain, *parts, outlen=32):
    """Domain separated SHAKE256 with length prefixed inputs."""
    h = hashlib.shake_256()
    h.update(len(domain).to_bytes(2, 'little'))
    h.update(domain.encode())
    for p in parts:
        b = _ser(p)
        h.update(len(b).to_bytes(8, 'little'))
        h.update(b)
    return h.digest(outlen)


def pack_bits(a, bits):
    """Canonical little-endian bit packing of non-negative integers below 2**bits."""
    x = np.ascontiguousarray(a, dtype=U64).reshape(-1)
    sh = np.arange(bits, dtype=U64)
    m = ((x[:, None] >> sh[None, :]) & U64(1)).astype(np.uint8)
    return np.packbits(m.reshape(-1), bitorder='little').tobytes()


def stream_u64(seed_bytes, count):
    raw = hashlib.shake_256(seed_bytes).digest(8 * count)
    return np.frombuffer(raw, dtype=U64).copy()


def uniform_rq(seed_bytes, shape, q):
    """Exactly uniform coefficients in [0, q) by rejection sampling on ceil(log2 q) bit words."""
    n = int(np.prod(shape))
    bits = int(q - 1).bit_length()
    mask = U64((1 << bits) - 1)
    out = np.empty(0, dtype=U64)
    ctr = 0
    need = n
    while need > 0:
        draw = need + (need >> 6) + 32
        v = stream_u64(seed_bytes + b'|u|' + ctr.to_bytes(4, 'little'), draw) & mask
        v = v[v < U64(q)]
        out = np.concatenate([out, v[:need]])
        need = n - out.size
        ctr += 1
    return out.reshape(shape)


def prf_uniform(seed_bytes, label, shape, q):
    """PRF(sd, label) with outputs in R_q^l, expanded by SHAKE256 and rejection sampling."""
    s = hashlib.shake_256(b'thimza-prf|' + len(seed_bytes).to_bytes(2, 'little') + seed_bytes + b'|' + label).digest(64)
    return uniform_rq(s, shape, q)


def hash_challenge(rng_seed, phi, kappa, q):
    """Hash to the challenge set: ternary polynomials of Hamming weight kappa."""
    raw = hashlib.shake_256(b'thimza-chal|' + rng_seed).digest(5 * 4 * kappa + 64)
    c = np.zeros(phi, dtype=U64)
    pos = 0
    picked = 0
    used = set()
    ext = 0
    while picked < kappa:
        if pos + 5 > len(raw):
            ext += 1
            raw = raw + hashlib.shake_256(b'thimza-chal-ext|' + rng_seed + ext.to_bytes(4, 'little')).digest(512)
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
    raw = hashlib.shake_256(seed_bytes).digest(16 * n)
    u = np.frombuffer(raw, dtype=U64).astype(np.float64).reshape(2, n) / float(1 << 64)
    u1 = np.clip(u[0], 1e-300, 1.0)
    v = np.sqrt(-2.0 * np.log(u1)) * np.cos(2.0 * np.pi * u[1]) * sigma
    z = np.rint(v).astype(np.int64)
    return (z % np.int64(q)).astype(U64).reshape(shape)
