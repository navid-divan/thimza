import gc
import time

from leotest.harness import (
    LEVEL_NAMES,
    Session,
    dealer_keygen_ms,
    honest_signature_fast,
    ms_since,
    now_ns,
    signer_keys,
    traccoon_round_times,
    traccoon_scheme,
)
from leotest.metrics import summarize
from leotest.runner import LeotestRunner
from leotest.utils import iso, load_average, max_rss_kb

ROUNDS = ("round1", "round2", "round3", "sign")


def _stats(samples):
    report = summarize(samples, unit="ms")
    report["best"] = min(samples) if samples else None
    return report


class ThimzaTimeClient(LeotestRunner):
    def __init__(self, testname, config=None, **kwargs):
        super().__init__(
            name=testname,
            title="Thimza time cost on the measurement node",
            description="Key generation, the three signing rounds, combine and verify, levels I, III, V",
            config=config,
            **kwargs
        )

    def _reps(self, t):
        large = int(self.param("large_threshold", 512))
        if t >= large:
            return int(self.param("reps_large", 15))
        return int(self.param("reps", 30))

    def _thimza(self, level, t, msg):
        out = {"t": t}
        keygen = []
        for _ in range(int(self.param("keygen_reps", 3) if t < 512 else self.param("keygen_reps_large", 2))):
            if self.budget_exhausted():
                break
            keygen.append(dealer_keygen_ms(level, t))
        out["dealer_keygen_ms"] = _stats(keygen)
        out["dealer_keygen_samples_ms"] = keygen

        scheme = signer_keys(level, t, honest=False)
        samples = {name: [] for name in ROUNDS}
        prf_calls = None
        for _ in range(self._reps(t)):
            if self.budget_exhausted():
                break
            gc.collect()
            session = Session(scheme, t, msg, honest=False)
            session.round1()
            session.round2()
            session.round3()
            for name in ("round1", "round2", "round3"):
                samples[name].append(session.compute_ms[name])
            samples["sign"].append(sum(session.compute_ms[n] for n in ("round1", "round2", "round3")))
            prf_calls = session.objects["prf_calls"]
        out["signer_ms"] = {name: _stats(values) for name, values in samples.items()}
        out["signer_samples_ms"] = samples
        out["prf_calls_round3"] = prf_calls

        combine = []
        for _ in range(int(self.param("combine_reps", 10))):
            if self.budget_exhausted():
                break
            session = Session(scheme, t, msg, honest=False)
            session.round1()
            session.round2()
            session.round3()
            session.combine()
            combine.append(session.compute_ms["combine"])
        out["combine_ms"] = _stats(combine)
        out["combine_samples_ms"] = combine
        del scheme
        gc.collect()
        return out

    def _verify(self, level, msg):
        scheme, sig = honest_signature_fast(level, 2, msg)
        samples = []
        for _ in range(int(self.param("verify_reps", 30))):
            start = now_ns()
            ok = scheme.verify(msg, sig)
            samples.append(ms_since(start))
            if not ok:
                return {"error": "honest signature rejected"}
        return {"ms": _stats(samples), "samples_ms": samples}

    def _traccoon(self, level, t, msg):
        scheme = traccoon_scheme(level, t)
        samples = {name: [] for name in ROUNDS}
        for _ in range(self._reps(t)):
            if self.budget_exhausted():
                break
            gc.collect()
            times = traccoon_round_times(scheme, t, msg)
            for name in ROUNDS:
                samples[name].append(times[name])
        del scheme
        gc.collect()
        return {
            "t": t,
            "signer_ms": {name: _stats(values) for name, values in samples.items()},
            "signer_samples_ms": samples,
        }

    def _start_test(self, artifact_name):
        levels = [int(x) for x in self.param("levels", [128, 192, 256])]
        thresholds = [int(x) for x in self.param("thresholds", [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024])]
        baseline = [int(x) for x in self.param("traccoon_thresholds", [16, 128, 1024])]
        msg = b"m" * int(self.param("message_bytes", 32))
        report = {"started": iso(), "levels": {}, "load_average_start": load_average()}
        for level in levels:
            entry = {"name": LEVEL_NAMES.get(level), "thimza": [], "traccoon": [], "verify": None}
            entry["load_average_start"] = load_average()
            for t in thresholds:
                if self.budget_exhausted():
                    entry["thimza"].append({"t": t, "skipped": "time budget"})
                    continue
                started = time.perf_counter()
                row = self._thimza(level, t, msg)
                row["wall_s"] = round(time.perf_counter() - started, 2)
                entry["thimza"].append(row)
                self.emit({"record": "thimza", "level": level, "t": t, "data": row})
            if not self.budget_exhausted():
                entry["verify"] = self._verify(level, msg)
                self.emit({"record": "verify", "level": level, "data": entry["verify"]})
            if self.param("include_traccoon", True):
                for t in baseline:
                    if self.budget_exhausted():
                        entry["traccoon"].append({"t": t, "skipped": "time budget"})
                        continue
                    row = self._traccoon(level, t, msg)
                    entry["traccoon"].append(row)
                    self.emit({"record": "traccoon", "level": level, "t": t, "data": row})
            entry["load_average_end"] = load_average()
            report["levels"][str(level)] = entry
        report["max_rss_kb"] = max_rss_kb()
        report["finished"] = iso()
        return report
