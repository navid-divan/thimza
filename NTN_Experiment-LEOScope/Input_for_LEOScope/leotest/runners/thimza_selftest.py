import importlib
import os
import random
import time
import unittest

import numpy as np

from leotest import kat, wire
from leotest.harness import LEVEL_NAMES, Session, level_params, reseed
from leotest.runner import LeotestRunner
from leotest.utils import iso

U64 = np.uint64


class _Recorder(unittest.TestResult):
    def __init__(self):
        super().__init__()
        self.rows = []
        self._started = {}

    def startTest(self, test):
        super().startTest(test)
        self._started[test.id()] = time.perf_counter()

    def _row(self, test, outcome, detail=None):
        started = self._started.get(test.id(), time.perf_counter())
        self.rows.append(
            {
                "test": test.id().split(".")[-1],
                "outcome": outcome,
                "seconds": round(time.perf_counter() - started, 4),
                "detail": detail,
            }
        )

    def addSuccess(self, test):
        super().addSuccess(test)
        self._row(test, "passed")

    def addFailure(self, test, err):
        super().addFailure(test, err)
        self._row(test, "failed", self._exc_info_to_string(err, test)[-1500:])

    def addError(self, test, err):
        super().addError(test, err)
        self._row(test, "error", self._exc_info_to_string(err, test)[-1500:])

    def addSkip(self, test, reason):
        super().addSkip(test, reason)
        self._row(test, "skipped", reason)


def _schoolbook_product(a, b, q):
    n = len(a)
    full = np.convolve(
        np.array([int(x) for x in a], dtype=object), np.array([int(x) for x in b], dtype=object)
    )
    res = [0] * n
    for i, v in enumerate(full):
        if i < n:
            res[i] += v
        else:
            res[i - n] -= v
    return [x % q for x in res]


class ThimzaSelfTestClient(LeotestRunner):
    def __init__(self, testname, config=None, **kwargs):
        super().__init__(
            name=testname,
            title="Thimza correctness on the measurement node",
            description="Unit tests, exact arithmetic, honest signing, codecs and known answers",
            config=config,
            **kwargs
        )

    def _unit_tests(self):
        module = importlib.import_module("tests.test_thimza")
        suite = unittest.defaultTestLoader.loadTestsFromModule(module)
        recorder = _Recorder()
        started = time.perf_counter()
        suite.run(recorder)
        return {
            "module": "tests/test_thimza.py",
            "run": recorder.testsRun,
            "passed": sum(1 for row in recorder.rows if row["outcome"] == "passed"),
            "seconds": round(time.perf_counter() - started, 3),
            "results": recorder.rows,
            "all_passed": recorder.wasSuccessful(),
        }

    def _mulmod_exactness(self, samples):
        from thimza.params import THIMZA
        from thimza.ring import mulmod

        q = THIMZA[128]["q"]
        rng = random.Random(int.from_bytes(os.urandom(8), "little"))
        edge = [0, 1, 2, q - 1, q - 2, (q - 1) // 2, (q + 1) // 2, 1 << 48, (1 << 48) + 1, q >> 1]
        a = edge + [rng.randrange(q) for _ in range(samples)]
        b = list(reversed(edge)) + [rng.randrange(q) for _ in range(samples)]
        got = mulmod(np.array(a, dtype=U64), np.array(b, dtype=U64), q)
        mismatches = [i for i, (x, y, z) in enumerate(zip(a, b, got)) if (x * y) % q != int(z)]
        return {"q": q, "pairs": len(a), "mismatches": len(mismatches), "exact": not mismatches}

    def _ntt_against_schoolbook(self):
        from thimza.params import THIMZA
        from thimza.ring import Rq

        P = THIMZA[128]
        R = Rq(P["phi"], P["q"])
        rng = np.random.default_rng()
        a = rng.integers(0, P["q"], P["phi"], dtype=np.uint64)
        b = rng.integers(0, P["q"], P["phi"], dtype=np.uint64)
        fast = R.intt(R.mul(R.ntt(a), R.ntt(b)))
        slow = _schoolbook_product(a, b, P["q"])
        return {"equal": [int(x) for x in fast] == slow}

    def _honest_signing(self, levels, pairs):
        rows = []
        for level in levels:
            for t, n in pairs:
                from thimza.schemes.thimza_scheme import Thimza

                S = Thimza(level_params(level), seed=int.from_bytes(os.urandom(6), "little"))
                S.keygen(t, n)
                reseed(S)
                msg = b"thimza-ntn-selftest-%d-%d" % (t, n)
                session = Session(S, t, msg, honest=True)
                session.round1()
                session.round2()
                session.round3()
                sig = session.combine()
                L = wire.Layout(S)
                blob = wire.encode_signature(L, S, msg, sig)
                decoded = wire.decode_signature(L, blob)
                tampered = (sig[0], sig[1].copy(), sig[2])
                tampered[1][0, 0] = (tampered[1][0, 0] + U64(1)) % U64(S.q)
                rows.append(
                    {
                        "level": level,
                        "t": t,
                        "n": n,
                        "signer_set": session.T,
                        "verifies": bool(session.verified),
                        "codec_roundtrip": wire.signatures_equal(sig, decoded),
                        "decoded_verifies": bool(S.verify(msg, decoded)),
                        "rejects_other_message": not S.verify(msg + b"!", sig),
                        "rejects_tampered_response": not S.verify(msg, tampered),
                        "signature_bytes": len(blob),
                    }
                )
        return rows

    def _independent_verifier(self, levels):
        from tests.test_thimza import independent_verify, sign_all
        from thimza.schemes.thimza_scheme import Thimza

        rows = []
        for level in levels:
            S = Thimza(level_params(level), seed=int.from_bytes(os.urandom(6), "little"))
            S.keygen(3, 5)
            reseed(S)
            sig = sign_all(S, [1, 3, 5], b"independent")
            started = time.perf_counter()
            accepts = independent_verify(S, b"independent", sig)
            rejects = not independent_verify(S, b"other", sig)
            rows.append(
                {
                    "level": level,
                    "accepts_valid": bool(accepts),
                    "rejects_other_message": bool(rejects),
                    "seconds": round(time.perf_counter() - started, 3),
                }
            )
        return rows

    def _codec_roundtrips(self, levels):
        from thimza.schemes.thimza_scheme import Thimza

        rows = []
        for level in levels:
            S = Thimza(level_params(level), seed=int.from_bytes(os.urandom(6), "little"))
            S.keygen(4, 6)
            reseed(S)
            L = wire.Layout(S)
            msg = b"codec"
            session = Session(S, 4, msg, honest=True)
            cmt = session.round1()
            request = session.request_bytes()
            wbar_bytes = session.round2()
            openings = session.openings_bytes()
            z_bytes = session.round3()
            sig = session.combine()
            m2, T2, cmts2 = wire.decode_request(L, request)
            decoded_openings = wire.decode_openings(L, openings, 4)
            checks = {
                "cmt": len(cmt) == L.hbytes,
                "request": m2 == msg and T2 == session.T and cmts2 == session._cmts,
                "wbar": np.array_equal(wire.decode_wbar(L, wbar_bytes), session._wbars[0]),
                "openings": all(
                    np.array_equal(x, y) for x, y in zip(decoded_openings, session._wbars)
                ),
                "z": np.array_equal(wire.decode_z(L, z_bytes), session._zs[0]),
                "signature": wire.signatures_equal(
                    sig, wire.decode_signature(L, wire.encode_signature(L, S, msg, sig))
                ),
                "signature_verifies": bool(session.verified),
            }
            rows.append({"level": level, "checks": checks, "all": all(checks.values())})
        return rows

    def _start_test(self, artifact_name):
        levels = [int(x) for x in self.param("levels", [128, 192, 256])]
        pairs = [tuple(p) for p in self.param("honest_pairs", [[2, 3], [3, 5], [5, 8], [7, 10]])]
        report = {"started": iso(), "levels": levels}

        steps = [
            ("unit_tests", lambda: self._unit_tests()),
            ("mulmod_exactness", lambda: self._mulmod_exactness(int(self.param("mulmod_samples", 20000)))),
            ("ntt_against_schoolbook", lambda: self._ntt_against_schoolbook()),
            ("honest_signing", lambda: self._honest_signing(levels, pairs)),
            ("independent_verifier", lambda: self._independent_verifier(levels)),
            ("codec_roundtrips", lambda: self._codec_roundtrips(levels)),
            ("integer_kats", lambda: kat.compare(kat.integer_kats(), kat.INTEGER_REFERENCE)),
            ("gaussian_kats", lambda: kat.compare(kat.gaussian_kats(), kat.GAUSSIAN_REFERENCE)),
        ]
        for name, step in steps:
            if self.budget_exhausted():
                report[name] = {"skipped": "time budget"}
                continue
            started = time.perf_counter()
            try:
                report[name] = step()
            except Exception as exc:
                report[name] = {"error": "%s: %s" % (type(exc).__name__, exc)}
            self.emit({"record": name, "seconds": round(time.perf_counter() - started, 3), "data": report[name]})

        def ok(name, test):
            value = report.get(name)
            try:
                return bool(test(value))
            except Exception:
                return False

        required = {
            "unit_tests": ok("unit_tests", lambda v: v["all_passed"]),
            "mulmod_exactness": ok("mulmod_exactness", lambda v: v["exact"]),
            "ntt_against_schoolbook": ok("ntt_against_schoolbook", lambda v: v["equal"]),
            "honest_signing": ok(
                "honest_signing",
                lambda v: all(
                    r["verifies"] and r["codec_roundtrip"] and r["decoded_verifies"]
                    and r["rejects_other_message"] and r["rejects_tampered_response"]
                    for r in v
                ),
            ),
            "independent_verifier": ok(
                "independent_verifier",
                lambda v: all(r["accepts_valid"] and r["rejects_other_message"] for r in v),
            ),
            "codec_roundtrips": ok("codec_roundtrips", lambda v: all(r["all"] for r in v)),
            "integer_kats": ok("integer_kats", lambda v: all(r["match"] for r in v)),
        }
        report["required_checks"] = required
        report["all_required_passed"] = all(required.values())
        report["gaussian_kats_match"] = ok(
            "gaussian_kats", lambda v: all(r["match"] for r in v if r["label"] != "signature_verifies")
        )
        report["level_names"] = {str(k): v for k, v in LEVEL_NAMES.items()}
        report["finished"] = iso()
        return report
