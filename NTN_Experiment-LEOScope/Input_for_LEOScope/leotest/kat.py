"""Known answers of the vendored Thimza code.

The integer pipeline (SHAKE expansion, rejection sampling, the NTT with its
floating point quotient, Shamir sharing, Lagrange coefficients, challenges and
hashes) is exact, so its digests must be identical on every machine. The
Gaussian sampler goes through numpy's log and cos, whose last bit may differ
between processors and libm builds, so the digests that depend on it are only
compared, never required.

Run `python -m leotest.kat` to print the reference values.
"""
import hashlib
import json

import numpy as np

from thimza.params import THIMZA
from thimza.prf import hash_challenge, prf_uniform, uniform_rq, xof
from thimza.ring import Rq
from thimza.sampling import Drbg, Sampler
from thimza.schemes.thimza_scheme import Thimza
from thimza.shamir import lagrange, share

U64 = np.uint64


def _digest(*arrays):
    h = hashlib.sha256()
    for item in arrays:
        if isinstance(item, (bytes, bytearray)):
            h.update(bytes(item))
        else:
            h.update(np.ascontiguousarray(item, dtype=U64).tobytes())
    return h.hexdigest()


def integer_kats():
    out = {}
    for level, P in THIMZA.items():
        q, phi, ell, k = P["q"], P["phi"], P["ell"], P["k"]
        R = Rq(phi, q)
        entry = {}
        entry["uniform_matrix"] = _digest(uniform_rq(b"thimza-ntn-kat-A", (k, ell, phi), q))
        entry["prf"] = _digest(prf_uniform(b"\x01" * P["seed_bytes"], b"kat-view", (ell, phi), q))
        seed = xof("Hc", b"kat-vk", b"kat-w", b"kat-msg")
        entry["challenge"] = _digest(hash_challenge(seed, phi, P["omega"], q))
        x = ((np.arange(k * phi, dtype=np.int64) * 7919 + 13) % q).astype(U64).reshape(k, phi)
        y = ((np.arange(k * phi, dtype=np.int64) * 104729 + 7) % q).astype(U64).reshape(k, phi)
        entry["ntt"] = _digest(R.ntt(x))
        entry["ntt_roundtrip"] = bool(np.array_equal(R.intt(R.ntt(x)), x))
        entry["ring_product"] = _digest(R.intt(R.mul(R.ntt(x), R.ntt(y))))
        S = Thimza(P, seed=0)
        S.vk = (b"", None, b"kat-vk-bytes")
        wbar = ((np.arange(k * phi, dtype=np.int64) * 31) % (q >> P["nu_c"])).astype(U64)
        wbar = wbar.reshape(k, phi)
        cmt = S.H0(b"kat-msg", 3, wbar)
        entry["H0"] = _digest(cmt)
        entry["H1"] = _digest(S.H1(b"kat-msg", [1, 3, 4], [cmt, cmt, cmt]))
        entry["lagrange"] = _digest(np.array([lagrange([1, 3, 4, 7], i, q) for i in (1, 3, 4, 7)], dtype=U64))
        smp = Sampler(q, b"kat-share")
        secret = smp.uniform((ell, phi))
        shares = share(secret, 3, 5, q, smp)
        entry["shamir"] = _digest(*[shares[i] for i in sorted(shares)])
        rng = Drbg(b"kat-drbg")
        entry["drbg"] = _digest(rng.bytes(64), rng.below(q, 1000))
        out[str(level)] = entry
    return out


def gaussian_kats():
    from leotest import wire
    from leotest.harness import Session

    out = {}
    for level, P in THIMZA.items():
        q, phi, ell = P["q"], P["phi"], P["ell"]
        entry = {}
        smp = Sampler(q, b"kat-gauss")
        entry["gaussian_nonce"] = _digest(smp.gaussian((ell, phi), 2.0 ** P["log_sigma_w"]))
        entry["gaussian_key"] = _digest(smp.gaussian((ell, phi), 2.0 ** P["log_sigma_t"]))
        S = Thimza(P, seed=4242)
        S.keygen(3, 5)
        entry["verification_key"] = _digest(wire.encode_vk(wire.Layout(S), S.vk))
        session = Session(S, 3, b"thimza-ntn-kat", honest=True)
        session.round1()
        session.round2()
        session.round3()
        sig = session.combine()
        entry["signature_verifies"] = bool(session.verified)
        entry["signature"] = _digest(wire.encode_signature(wire.Layout(S), S, b"thimza-ntn-kat", sig))
        out[str(level)] = entry
    return out


# Reference values computed with python 3.12, numpy 2.3 on an Apple M2.
INTEGER_REFERENCE = {
    "128": {
        "uniform_matrix": "9fa05a58bc8cde57ac7faacaddb363b1e8f44c15bc0dba617d8344692ffe1060",
        "prf": "a0fd058ee837d1beb78f5deba1e4d53b68d88bc228214e689a41c63183f59582",
        "challenge": "9f8aed1ac1bb6b98d0a1af68eb42b085fde94c2d3b7eaa2f182ba025cc253152",
        "ntt": "b037143e0e53c07f26f2986b5bee2f525c25fbb5a4c86a970b6f3d046faf1e37",
        "ntt_roundtrip": True,
        "ring_product": "0c4487c5484d975f15c6026af3b7bb7776bc7e382332a6cd7b1dfde26406d152",
        "H0": "afe1a74a745b601d32974f172e0685eb38c95d8920d466b61071414ea45fc7f0",
        "H1": "195053324aad9560efa50520656d3c3f75b625737f8f46b53fa986a36895d0c4",
        "lagrange": "f7a472ffdf7442862d1f4468a22cbb6c933cfa025c218ba93b0873589e198bc6",
        "shamir": "6881b76631a7805a57bdab62319729624efa6823a625f411340e39375b7b4f5c",
        "drbg": "2a2813505ff937e4c637722b3dfe8f7f861f58774bd5dddceb0feb7a68a4704a",
    },
    "192": {
        "uniform_matrix": "a1d05ff7cacb4d02fd907dc35a83a077873e17f0808599a16e1f6779cbca6d95",
        "prf": "b1fdcdfa143da0e17c069e827129e21dd8d78c8e322714eb8698116e944dbeef",
        "challenge": "d9e4ec2a7d751941ea51789b300f7dcea5335e53150675d4b9db7fb30075eef3",
        "ntt": "b625b783bbd369fc3f37f6becc9c4701c4b8554d522063b7f370e35795a9d909",
        "ntt_roundtrip": True,
        "ring_product": "7c74fbfdc6c8e4da197b781aa9cac0fb84a2be0f73b7193f0136ac23ea14f0d8",
        "H0": "00f1c6445fde49b0a0a4ea240d5081ea9cbb3b27ba3aff1bc7b3814281b3ff03",
        "H1": "5f45f8c471b75c6d7af147686d0f711466910d3298d4e8eed8a7de8fb94a411e",
        "lagrange": "f7a472ffdf7442862d1f4468a22cbb6c933cfa025c218ba93b0873589e198bc6",
        "shamir": "c51b6be60f444734055ae0676bcffad8f23dce7e6615ea8bdfdc1cf06149cec7",
        "drbg": "2a2813505ff937e4c637722b3dfe8f7f861f58774bd5dddceb0feb7a68a4704a",
    },
    "256": {
        "uniform_matrix": "cc25802ccf7a20ec88d858cfa2fb8a8727e43a3ef0acc09806f826e7c60d3fbf",
        "prf": "4be0d491fbf2c352d2d4667ac840e9fb78ae8009ffde14fd89addbc0f0d58209",
        "challenge": "16b0111cf09469c00cf66b2640b833a46d99aa6418f4f5e6f2a7c92fa2e68c27",
        "ntt": "7b651dbfd9ea856d762bbe5a3db65b41b4da160ed0ee8ad4cd1240cf37f9f77d",
        "ntt_roundtrip": True,
        "ring_product": "7e0da77580a4fba485620405021544a9108385c4b7b1b0969c83857562939e7b",
        "H0": "ecd9ae7749824e59c1b228bcc48c77692f4d5a5a038ce4d5e50aa39562fbd561",
        "H1": "08397ce1eed816ed09a59efebff8c8f860ac3761ac020a1a492f1d7d0458319b",
        "lagrange": "f7a472ffdf7442862d1f4468a22cbb6c933cfa025c218ba93b0873589e198bc6",
        "shamir": "a47a781e9ccc3e00539242970e577d66762b18672616a681975b9d713d512a9d",
        "drbg": "2a2813505ff937e4c637722b3dfe8f7f861f58774bd5dddceb0feb7a68a4704a",
    },
}
GAUSSIAN_REFERENCE = {
    "128": {
        "gaussian_nonce": "f2b7830afdc88e1bc36bb5f2658cce074a3823be445eacc028a610ab7c11bf6b",
        "gaussian_key": "28a92493ad5f51905463821fba75ba703da3c6e34862dd673408feade06d9a5a",
        "verification_key": "9d2b2037c7d451895f2cb7d0e03eff959f3beac75d41b88faf343d5e20b948e0",
        "signature_verifies": True,
        "signature": "554ee3a9cc3d4ceca78c5c7702b402d9aafee6d46af01f5d4e2a9227b2eaf1d1",
    },
    "192": {
        "gaussian_nonce": "e2deca464928a1bc1205f097510f7c4ced2c72fe21511270c0f064aef8bbc8bf",
        "gaussian_key": "d470adb9a9ae359e0e3d34610707181928a106b6178e1f8c4fd386d921bf2f73",
        "verification_key": "63a7fc488d339c033f4c13a521ef0a653a09563597762ed6e1c1a9b85571d259",
        "signature_verifies": True,
        "signature": "8d6bfc83ddd161d5a474db19aa37c6c72f3fa7f4713fe25ec5365741ccf0430e",
    },
    "256": {
        "gaussian_nonce": "5af578d33223f30a0d400d607f407f3175537986c484cdac15e244a13afd8334",
        "gaussian_key": "bf3c0fb932cff064fa027a9b656fa1975ea4a3b1f4205340e7760d07d61a53d5",
        "verification_key": "3d6367879850002f8ef08f96ac929bfa69b1ab0b68152edfb8f4ef781357994c",
        "signature_verifies": True,
        "signature": "b86a54c872ca719604895065eac812c088cd8c509b2255d9392111bfe2f83424",
    },
}


def compare(measured, reference):
    rows = []
    for level, entries in measured.items():
        for label, value in entries.items():
            expected = reference.get(level, {}).get(label)
            rows.append(
                {
                    "level": level,
                    "label": label,
                    "value": value,
                    "expected": expected,
                    "match": (value == expected) if expected is not None else None,
                }
            )
    return rows


if __name__ == "__main__":
    print(json.dumps({"integer": integer_kats(), "gaussian": gaussian_kats()}, indent=1))
