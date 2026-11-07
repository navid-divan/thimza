"""Signing sessions of the vendored Thimza implementation, one round at a time.

A session plays signer 1 and every other member of the signer set T = {1..t}.
Only the work of signer 1 is timed. Two modes exist:

* honest: all t signers run the protocol, the combiner builds the signature,
  and the signature must verify. Used for small t.
* simulated: the method of the paper's benchmark (experiments/run_all.py,
  bench_one). The t-1 peers send the commitment and the opening of signer 1
  under their own index, which costs signer 1 exactly what t distinct peers
  cost, and which scales to t = 1024. No signature is produced.

The rounds are exposed one by one so that a caller can place a network transfer
between them.
"""
import gc
import os
import time

import numpy as np

from thimza.params import THIMZA, TRACCOON
from thimza.sampling import Drbg
from thimza.schemes.prior import TRaccoon
from thimza.schemes.thimza_scheme import Thimza

from leotest import wire

LEVEL_NAMES = {128: "I", 192: "III", 256: "V"}
U64 = np.uint64


def now_ns():
    return time.perf_counter_ns()


def ms_since(start_ns):
    return (time.perf_counter_ns() - start_ns) / 1e6


def level_params(level):
    return THIMZA[int(level)]


def reseed(scheme):
    """Fresh nonces from os.urandom after a deterministic key generation."""
    scheme.C.smp.rng = Drbg(None)


def signer_keys(level, t, honest, key_seed=None):
    """A scheme instance holding keys for T = {1..t}.

    honest: a (t, t) key from the dealer of the paper.
    simulated: a key with threshold min(t, 8) for n = max(t, 8) parties, as in
    the paper's benchmark, which gives signer 1 its n - 1 pair seeds.
    """
    seed = key_seed if key_seed is not None else int.from_bytes(os.urandom(6), "little")
    scheme = Thimza(level_params(level), seed=seed)
    if honest:
        scheme.keygen(t, t)
    else:
        scheme.keygen(min(t, 8), max(t, 8))
        scheme.t_thr = t
        scheme.n_parties = max(scheme.n_parties, t)
        scheme.sk["shares"] = {1: scheme.sk["shares"][1]}
        scheme.sk["seeds"] = {key: value for key, value in scheme.sk["seeds"].items() if 1 in key}
    reseed(scheme)
    return scheme


def dealer_keygen_ms(level, t):
    """Dealer cost with the paper's method: keygen(min(t, 8), max(t, 8))."""
    scheme = Thimza(level_params(level), seed=int.from_bytes(os.urandom(6), "little"))
    gc.collect()
    start = now_ns()
    scheme.keygen(min(t, 8), max(t, 8))
    elapsed = ms_since(start)
    del scheme
    gc.collect()
    return elapsed


class Session:
    def __init__(self, scheme, t, msg, honest):
        self.S = scheme
        self.L = wire.Layout(scheme)
        self.t = int(t)
        self.T = list(range(1, self.t + 1))
        self.msg = bytes(msg)
        self.honest = bool(honest)
        self.compute_ms = {}
        self.objects = {}
        self.signature = None
        self.verified = None
        self._tokens = {}
        self._cmts = None
        self._wbars = None
        self._zs = None
        self._c = None
        self._w = None

    # ------------------------------------------------------------ round one
    def round1(self):
        S = self.S
        start = now_ns()
        token, cmt = S.round1(1, self.msg)
        self.compute_ms["round1"] = ms_since(start)
        self._tokens[1] = token
        cmts = {1: cmt}
        if self.honest:
            for j in self.T[1:]:
                self._tokens[j], cmts[j] = S.round1(j, self.msg)
        else:
            for j in self.T[1:]:
                cmts[j] = S.H0(self.msg, j, token.wbar)
        self._cmts = [cmts[j] for j in self.T]
        self.objects["cmt"] = wire.encode_cmt(cmt)
        self.objects["state_after_round1"] = wire.token_bytes(self.L, token)
        return self.objects["cmt"]

    def request_bytes(self):
        return wire.encode_request(self.L, self.msg, self.T, self._cmts)

    # ------------------------------------------------------------ round two
    def round2(self):
        S = self.S
        token = self._tokens[1]
        start = now_ns()
        wbar = S.round2(token, self.T, self._cmts)
        self.compute_ms["round2"] = ms_since(start)
        wbars = {1: wbar}
        if self.honest:
            for j in self.T[1:]:
                wbars[j] = S.round2(self._tokens[j], self.T, self._cmts)
        else:
            for j in self.T[1:]:
                wbars[j] = wbar
        self._wbars = [wbars[j] for j in self.T]
        self.objects["wbar"] = wire.encode_wbar(self.L, wbar)
        self.objects["state_after_round2"] = wire.token_bytes(self.L, token)
        return self.objects["wbar"]

    def openings_bytes(self):
        return wire.encode_openings(self.L, self._wbars)

    # ---------------------------------------------------------- round three
    def round3(self):
        S = self.S
        token = self._tokens[1]
        start = now_ns()
        z, c, w, calls = S.round3(token, self.T, self._cmts, self._wbars)
        self.compute_ms["round3"] = ms_since(start)
        self.objects["prf_calls"] = int(calls)
        self.objects["state_after_round3"] = wire.token_bytes(self.L, token)
        zs = [z]
        if self.honest:
            for j in self.T[1:]:
                zj, _, _, _ = S.round3(self._tokens[j], self.T, self._cmts, self._wbars)
                zs.append(zj)
        self._zs = zs
        self._c = c
        self._w = w
        self.objects["z"] = wire.encode_z(self.L, z)
        return self.objects["z"]

    # ------------------------------------------------------------- combiner
    def combine(self):
        """Combiner cost; with simulated peers the t responses are copies."""
        zs = self._zs if self.honest else [self._zs[0]] * self.t
        start = now_ns()
        sig = self.S.combine(self.T, self.msg, zs, self._c, self._w)
        self.compute_ms["combine"] = ms_since(start)
        if self.honest:
            self.signature = sig
            start = now_ns()
            self.verified = bool(self.S.verify(self.msg, sig))
            self.compute_ms["verify"] = ms_since(start)
        return sig


def simulated_round_times(scheme, t, msg):
    session = Session(scheme, t, msg, honest=False)
    session.round1()
    session.round2()
    session.round3()
    return session


def honest_signature_fast(level, t, msg, key_seed=None):
    """A valid Thimza signature for |T| = t drawn from its exact distribution.

    Uses the function of the paper's correctness experiment
    (experiments/correctness_bound.py), which computes z = c s + sum_j r_j and
    the hint from the aggregate of t truncated commitments, so that t up to 1024
    costs t commitments rather than t full signers. Returns a scheme object whose
    vk matches the signature, so that the unmodified Thimza verifier applies.
    """
    from experiments.correctness_bound import honest_signature
    from thimza.core import RaccoonCore
    from thimza.prf import xof

    P = level_params(level)
    seed = key_seed if key_seed is not None else int.from_bytes(os.urandom(6), "little")
    scheme = Thimza(P, seed=seed)
    scheme.keygen(1, 1)
    C = scheme.C
    C.vkb = scheme.vk[2]
    C.t_pk = scheme.vk[1]
    s = scheme.sk["s"]
    reseed(scheme)
    sig = honest_signature(C, P["nu_c"], s, int(t), bytes(msg))
    return scheme, sig


def traccoon_scheme(level, t):
    """Threshold Raccoon keyed for signer 1 only: its row, column and MAC keys."""
    scheme = TRaccoon(TRACCOON[int(level)], seed=int.from_bytes(os.urandom(6), "little"))
    scheme.keygen(min(t, 8), 8)
    rng = np.random.default_rng()
    for j in range(1, t + 1):
        for key in ((1, j), (j, 1)):
            if key not in scheme.sk["seeds"]:
                scheme.sk["seeds"][key] = rng.bytes(32)
            if key not in scheme.sk["mac"]:
                scheme.sk["mac"][key] = rng.bytes(32)
    scheme.n_parties = max(scheme.n_parties, t)
    return scheme


def traccoon_round_times(scheme, t, msg):
    """One signer of Threshold Raccoon, with the method of the paper's benchmark."""
    T = list(range(1, t + 1))
    sid = os.urandom(16)
    out = {}
    start = now_ns()
    state, contrib = scheme.round1(1, msg, T, sid)
    out["round1"] = ms_since(start)
    start = now_ns()
    scheme.round2(1, state, T, msg, sid, [contrib] * t)
    out["round2"] = ms_since(start)
    ws = [state[1]] * t
    start = now_ns()
    scheme.round3(1, state, T, msg, sid, ws)
    out["round3"] = ms_since(start)
    out["sign"] = out["round1"] + out["round2"] + out["round3"]
    return out
