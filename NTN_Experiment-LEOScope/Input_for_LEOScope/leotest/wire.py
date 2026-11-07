"""Byte encodings of every Thimza object that crosses a network.

The vendored Thimza package computes message sizes from formulas. This module
produces the actual bytes, so that the link measurements carry real objects and
the space measurements count real objects. Nothing here changes the scheme:
encoders take the values produced by the unmodified implementation and decoders
return values that the unmodified verifier accepts.

Round messages and keys are fixed-width packings, whose sizes coincide with the
formulas of the paper. The signature (c, z, h) carries the 32-byte challenge
seed from which the implementation derives c, and z and h in a lossless
Golomb-Rice code whose length depends on the data.
"""
import math
import struct

import numpy as np

from thimza.prf import hash_challenge, pack_bits, xof

U64 = np.uint64
CHALLENGE_SEED_BYTES = 32


def unpack_bits(data, bits, count):
    """Inverse of thimza.prf.pack_bits: little-endian bit order, fixed width."""
    if bits == 0:
        return np.zeros(count, dtype=U64)
    raw = np.frombuffer(bytes(data), dtype=np.uint8)
    flat = np.unpackbits(raw, bitorder="little")
    if flat.size < count * bits:
        raise ValueError("buffer too short for %d values of %d bits" % (count, bits))
    matrix = flat[: count * bits].reshape(count, bits).astype(U64)
    weights = U64(1) << np.arange(bits, dtype=U64)
    return (matrix * weights).sum(axis=1, dtype=U64)


def packed_len(count, bits):
    return (count * bits + 7) // 8


class Layout:
    """Bit widths of one Thimza parameter set, derived from the implementation."""

    def __init__(self, scheme):
        P = scheme.P
        C = scheme.C
        self.level = int(P.get("lam", 128))
        self.q = int(scheme.q)
        self.phi = int(C.phi)
        self.ell = int(C.ell)
        self.k = int(C.k)
        self.omega = int(C.omega)
        self.nu_t = int(C.nu_t)
        self.nu_w = int(C.nu_w)
        self.nu_c = int(scheme.nu_c)
        self.hbytes = int(scheme.hbytes)
        self.seed_bytes = int(scheme.seed_bytes)
        self.bits_q = self.q.bit_length()
        self.bits_wbar = int(scheme.wbits)
        self.bits_t = int(self.q >> self.nu_t).bit_length()
        self.q_w = self.q >> self.nu_w
        self.bits_h_fixed = int(self.q_w).bit_length()

    def as_dict(self):
        return dict(self.__dict__)


# ---------------------------------------------------------------- round messages
def encode_cmt(cmt):
    return bytes(cmt)


def encode_wbar(layout, wbar):
    values = np.ascontiguousarray(wbar, dtype=U64).reshape(-1)
    if values.size != layout.k * layout.phi:
        raise ValueError("opening has %d coefficients" % values.size)
    if int(values.max()) >= (1 << layout.bits_wbar):
        raise ValueError("opening coefficient exceeds %d bits" % layout.bits_wbar)
    return pack_bits(values, layout.bits_wbar)


def decode_wbar(layout, data):
    values = unpack_bits(data, layout.bits_wbar, layout.k * layout.phi)
    return values.reshape(layout.k, layout.phi)


def encode_z(layout, z):
    values = np.ascontiguousarray(z, dtype=U64).reshape(-1)
    if values.size != layout.ell * layout.phi:
        raise ValueError("response has %d coefficients" % values.size)
    if int(values.max()) >= layout.q:
        raise ValueError("response coefficient is not reduced modulo q")
    return pack_bits(values, layout.bits_q)


def decode_z(layout, data):
    values = unpack_bits(data, layout.bits_q, layout.ell * layout.phi)
    return values.reshape(layout.ell, layout.phi)


def encode_request(layout, msg, signer_set, cmts):
    """The request V = (msg, T, (cmt_j)_{j in T}) that a signer receives before round two."""
    signer_set = [int(j) for j in signer_set]
    if len(cmts) != len(signer_set):
        raise ValueError("one commitment per member of T is required")
    head = struct.pack(">H", len(msg)) + bytes(msg) + struct.pack(">H", len(signer_set))
    head += b"".join(struct.pack(">H", j) for j in signer_set)
    return head + b"".join(bytes(c) for c in cmts)


def decode_request(layout, data):
    offset = 0
    (mlen,) = struct.unpack_from(">H", data, offset)
    offset += 2
    msg = bytes(data[offset : offset + mlen])
    offset += mlen
    (tcount,) = struct.unpack_from(">H", data, offset)
    offset += 2
    signer_set = list(struct.unpack_from(">%dH" % tcount, data, offset))
    offset += 2 * tcount
    cmts = []
    for _ in range(tcount):
        cmts.append(bytes(data[offset : offset + layout.hbytes]))
        offset += layout.hbytes
    if offset != len(data):
        raise ValueError("trailing bytes in request")
    return msg, signer_set, cmts


def request_len(layout, msg_len, t):
    return 2 + msg_len + 2 + 2 * t + t * layout.hbytes


def encode_openings(layout, wbars):
    """The openings (wbar_j)_{j in T} that a signer receives before round three."""
    return b"".join(encode_wbar(layout, w) for w in wbars)


def decode_openings(layout, data, t):
    size = packed_len(layout.k * layout.phi, layout.bits_wbar)
    if len(data) != t * size:
        raise ValueError("openings have %d bytes, expected %d" % (len(data), t * size))
    return [decode_wbar(layout, data[i * size : (i + 1) * size]) for i in range(t)]


def openings_len(layout, t):
    return t * packed_len(layout.k * layout.phi, layout.bits_wbar)


# ------------------------------------------------------------------------ keys
def encode_vk(layout, vk):
    a_seed, t_pk, _ = vk
    values = np.ascontiguousarray(t_pk, dtype=U64).reshape(-1)
    return bytes(a_seed) + pack_bits(values, layout.bits_t)


def sk_len(layout, n):
    return layout.seed_bytes + packed_len(layout.ell * layout.phi, layout.bits_q) + layout.seed_bytes * (n - 1)


# ------------------------------------------------------------------ the token
def token_bytes(layout, token):
    """Serialized size of the session state of one signer, by phase."""
    if token.phase == 0:
        return {"phase": 0, "bytes": 0}
    r = np.ascontiguousarray(token.r, dtype=U64).reshape(-1)
    size = 1 + 2 + 2 + len(token.msg)
    size += packed_len(r.size, layout.bits_q)
    size += packed_len(layout.k * layout.phi, layout.bits_wbar)
    size += len(token.cmt)
    if token.phase >= 2:
        size += len(token.digest) + 2 + 2 * len(token.T)
    in_memory = r.nbytes + np.asarray(token.wbar).nbytes + len(token.cmt) + len(token.msg)
    if token.phase >= 2:
        in_memory += len(token.digest) + 8 * len(token.T)
    return {"phase": int(token.phase), "bytes": int(size), "numpy_bytes": int(in_memory)}


# ----------------------------------------------------------------- Rice coding
def _bits_of(values, width):
    if width == 0:
        return np.zeros((values.size, 0), dtype=np.uint8)
    shifts = np.arange(width, dtype=U64)
    return ((values[:, None] >> shifts[None, :]) & U64(1)).astype(np.uint8)


def rice_encode(values):
    """Lossless signed Golomb-Rice code with the parameter that minimises the length.

    Layout: one byte L, then one sign bit per value, then the L low bits of every
    magnitude, then the high part of every magnitude in unary (ones closed by a
    zero), padded with zero bits to a whole byte.
    """
    v = np.asarray(values, dtype=np.int64).reshape(-1)
    mag = np.abs(v).astype(U64)
    mean = float(mag.mean()) if mag.size else 0.0
    centre = int(math.floor(math.log2(mean))) if mean >= 1.0 else 0
    best = None
    for width in range(max(0, centre - 3), min(62, centre + 4)):
        high = mag >> U64(width)
        length = v.size * (2 + width) + int(high.sum())
        if best is None or length < best[1]:
            best = (width, length)
    width = best[0]
    high = (mag >> U64(width)).astype(np.int64)
    low = mag & U64((1 << width) - 1) if width else np.zeros_like(mag)
    unary = np.ones(int(high.sum()) + v.size, dtype=np.uint8)
    unary[np.cumsum(high + 1) - 1] = 0
    stream = np.concatenate(
        [(v < 0).astype(np.uint8), _bits_of(low, width).reshape(-1), unary]
    )
    return bytes([width]) + np.packbits(stream, bitorder="little").tobytes()


def rice_decode(data, count):
    width = data[0]
    stream = np.unpackbits(np.frombuffer(bytes(data[1:]), dtype=np.uint8), bitorder="little")
    signs = stream[:count].astype(bool)
    offset = count
    if width:
        lows = stream[offset : offset + count * width].reshape(count, width).astype(U64)
        low = (lows << np.arange(width, dtype=U64)[None, :]).sum(axis=1, dtype=U64)
    else:
        low = np.zeros(count, dtype=U64)
    offset += count * width
    unary = stream[offset:]
    zeros = np.flatnonzero(unary == 0)
    if zeros.size < count:
        raise ValueError("truncated Rice stream")
    ends = zeros[:count]
    if unary[ends[-1] + 1 :].any() or unary.size - ends[-1] - 1 >= 8:
        raise ValueError("Rice stream carries trailing data")
    high = np.diff(np.concatenate(([-1], ends))) - 1
    mag = (high.astype(U64) << U64(width)) | low
    out = mag.astype(np.int64)
    out[signs] = -out[signs]
    return out


def _block(payload):
    return struct.pack(">I", len(payload)) + payload


def _unblock(data, offset):
    (size,) = struct.unpack_from(">I", data, offset)
    offset += 4
    return bytes(data[offset : offset + size]), offset + size


# -------------------------------------------------------------- the signature
def challenge_seed(scheme, msg, sig):
    """The 32-byte seed from which the implementation derives c, recomputed from sig."""
    c, z, h = sig
    _, t_pk, vk_bytes = scheme.vk
    w_rec = scheme.C.recompute_w(t_pk, c, z, h)
    seed = xof("Hc", vk_bytes, w_rec, msg)
    if not np.array_equal(hash_challenge(seed, scheme.C.phi, scheme.C.omega, scheme.q), c):
        raise ValueError("signature challenge does not match its commitment")
    return seed


def encode_signature(layout, scheme, msg, sig):
    """Compact encoding: challenge seed, Rice-coded centred z, Rice-coded h."""
    _, z, h = sig
    seed = challenge_seed(scheme, msg, sig)
    z_centred = scheme.R.center(z).reshape(-1)
    h_values = np.asarray(h, dtype=np.int64).reshape(-1)
    return seed + _block(rice_encode(z_centred)) + _block(rice_encode(h_values))


def decode_signature(layout, data):
    seed = bytes(data[:CHALLENGE_SEED_BYTES])
    offset = CHALLENGE_SEED_BYTES
    z_block, offset = _unblock(data, offset)
    h_block, offset = _unblock(data, offset)
    if offset != len(data):
        raise ValueError("trailing bytes in signature")
    c = hash_challenge(seed, layout.phi, layout.omega, layout.q)
    z_c = rice_decode(z_block, layout.ell * layout.phi)
    z = (z_c % np.int64(layout.q)).astype(U64).reshape(layout.ell, layout.phi)
    h = rice_decode(h_block, layout.k * layout.phi).reshape(layout.k, layout.phi)
    return c, z, h


def encode_signature_fixed(layout, scheme, msg, sig):
    """Fixed-width encoding, lossless for every signature: z mod q and h mod q_w."""
    _, z, h = sig
    seed = challenge_seed(scheme, msg, sig)
    z_bytes = pack_bits(np.ascontiguousarray(z, dtype=U64).reshape(-1), layout.bits_q)
    h_mod = (np.asarray(h, dtype=np.int64) % np.int64(layout.q_w)).astype(U64).reshape(-1)
    return seed + z_bytes + pack_bits(h_mod, layout.bits_h_fixed)


def signature_parts(layout, data):
    """Bytes taken by each part of a compact signature."""
    z_block, offset = _unblock(data, CHALLENGE_SEED_BYTES)
    h_block, _ = _unblock(data, offset)
    return {
        "challenge_seed": CHALLENGE_SEED_BYTES,
        "z": len(z_block) + 4,
        "h": len(h_block) + 4,
        "z_rice_parameter": z_block[0],
        "h_rice_parameter": h_block[0],
    }


def signatures_equal(a, b):
    return all(np.array_equal(np.asarray(x), np.asarray(y)) for x, y in zip(a, b))
