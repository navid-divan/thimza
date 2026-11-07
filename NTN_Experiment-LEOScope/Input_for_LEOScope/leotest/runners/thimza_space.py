import gc
import math
import time
import tracemalloc

from leotest import wire
from leotest.harness import (
    LEVEL_NAMES,
    Session,
    honest_signature_fast,
    level_params,
    signer_keys,
)
from leotest.metrics import summarize
from leotest.runner import LeotestRunner
from leotest.utils import iso, max_rss_kb


def _paper_sig_budget_bits(P, layout):
    """Bits that the paper's size model gives to z and h."""
    from thimza.core import bits_gauss

    sagg = 2.0 ** P["log_sigma_w"] * math.sqrt(P["Tmax"])
    z_bits = layout.ell * layout.phi * bits_gauss(sagg)
    h_bits = layout.k * layout.phi * bits_gauss(max(sagg / 2.0 ** layout.nu_w, 1.0))
    return z_bits, h_bits


class ThimzaSpaceClient(LeotestRunner):
    def __init__(self, testname, config=None, **kwargs):
        super().__init__(
            name=testname,
            title="Thimza space cost with real encodings",
            description="Exact bytes of keys, round messages, requests, openings, signatures and state",
            config=config,
            **kwargs
        )

    def _objects(self, level, t, msg):
        scheme = signer_keys(level, t, honest=False)
        layout = wire.Layout(scheme)
        tracemalloc.start()
        session = Session(scheme, t, msg, honest=False)
        cmt = session.round1()
        request = session.request_bytes()
        wbar = session.round2()
        openings = session.openings_bytes()
        z = session.round3()
        peak = tracemalloc.get_traced_memory()[1]
        tracemalloc.stop()
        model = scheme.sizes(t)
        vk = wire.encode_vk(layout, scheme.vk)
        measured = {
            "cmt": len(cmt),
            "wbar": len(wbar),
            "z": len(z),
            "request": len(request),
            "openings": len(openings),
            "vk": len(vk),
            "sk": wire.sk_len(layout, t),
        }
        predicted = {
            "cmt": layout.hbytes,
            "wbar": wire.packed_len(layout.k * layout.phi, layout.bits_wbar),
            "z": wire.packed_len(layout.ell * layout.phi, layout.bits_q),
            "request": wire.request_len(layout, len(msg), t),
            "openings": wire.openings_len(layout, t),
            "vk": len(vk),
            "sk": wire.sk_len(layout, t),
        }
        state = {
            phase: session.objects["state_after_round%d" % phase] for phase in (1, 2, 3)
        }
        sent = measured["cmt"] + measured["wbar"] + measured["z"]
        received = measured["request"] + measured["openings"]
        del scheme, session
        gc.collect()
        return {
            "layout": layout.as_dict(),
            "bytes": measured,
            "bytes_predicted_by_codec": predicted,
            "codec_matches_prediction": measured == predicted,
            "paper_model_bytes": {k: round(v) for k, v in model.items()},
            "paper_model_matches": {
                "r1": measured["cmt"] == round(model["r1"]),
                "r2": measured["wbar"] == round(model["r2"]),
                "r3": measured["z"] == round(model["r3"]),
                "vk": measured["vk"] == round(model["vk"]),
            },
            "per_signer": {
                "sent_bytes": sent,
                "received_bytes": received,
                "received_over_sent": received / float(sent),
                "paper_counts_sent_only": round(model["total"]),
            },
            "state_bytes": {
                "after_round1": state[1],
                "after_round2": state[2],
                "after_round3": state[3],
            },
            "python_heap_peak_bytes_one_signer_session": peak,
        }

    def _signatures(self, level, t, trials, msg):
        P = level_params(level)
        rows = []
        for _ in range(trials):
            if self.budget_exhausted():
                break
            started = time.perf_counter()
            scheme, sig = honest_signature_fast(level, t, msg)
            layout = wire.Layout(scheme)
            valid = bool(scheme.verify(msg, sig))
            blob = wire.encode_signature(layout, scheme, msg, sig)
            fixed = wire.encode_signature_fixed(layout, scheme, msg, sig)
            decoded = wire.decode_signature(layout, blob)
            parts = wire.signature_parts(layout, blob)
            z_bits, h_bits = _paper_sig_budget_bits(P, layout)
            rows.append(
                {
                    "verifies": valid,
                    "roundtrip": wire.signatures_equal(sig, decoded),
                    "decoded_verifies": bool(scheme.verify(msg, decoded)),
                    "compact_bytes": len(blob),
                    "fixed_bytes": len(fixed),
                    "parts": parts,
                    "z_fits_paper_budget": (parts["z"] - 5) * 8 <= z_bits,
                    "h_fits_paper_budget": (parts["h"] - 5) * 8 <= h_bits,
                    "seconds": round(time.perf_counter() - started, 3),
                }
            )
            del scheme
        model = None
        if rows:
            from thimza.schemes.thimza_scheme import Thimza

            probe = Thimza(P, seed=3)
            probe.keygen(2, 3)
            model = round(probe.sizes(t)["sig"])
        compact = [r["compact_bytes"] for r in rows]
        return {
            "trials": len(rows),
            "all_verify": all(r["verifies"] and r["decoded_verifies"] and r["roundtrip"] for r in rows),
            "compact_bytes": summarize(compact, unit="bytes"),
            "fixed_bytes": rows[0]["fixed_bytes"] if rows else None,
            "paper_model_bytes": model,
            "fraction_within_paper_model": (
                sum(1 for b in compact if b <= model) / float(len(compact)) if rows else None
            ),
            "fraction_z_fits_paper_budget": (
                sum(1 for r in rows if r["z_fits_paper_budget"]) / float(len(rows)) if rows else None
            ),
            "rice_parameters": sorted({(r["parts"]["z_rice_parameter"], r["parts"]["h_rice_parameter"]) for r in rows}),
            "samples": rows,
        }

    def _start_test(self, artifact_name):
        levels = [int(x) for x in self.param("levels", [128, 192, 256])]
        thresholds = [int(x) for x in self.param("thresholds", [2, 16, 128, 1024])]
        trials = {int(k): int(v) for k, v in (self.param("signature_trials", {}) or {}).items()}
        msg = b"m" * int(self.param("message_bytes", 32))
        report = {"started": iso(), "message_bytes": len(msg), "levels": {}}
        for level in levels:
            entry = {"name": LEVEL_NAMES.get(level), "thresholds": {}}
            for t in thresholds:
                if self.budget_exhausted():
                    entry["thresholds"][str(t)] = {"skipped": "time budget"}
                    continue
                objects = self._objects(level, t, msg)
                self.emit({"record": "objects", "level": level, "t": t, "data": objects})
                sigs = self._signatures(level, t, trials.get(t, 5), msg)
                self.emit({"record": "signatures", "level": level, "t": t, "data": sigs})
                objects["signature"] = {k: v for k, v in sigs.items() if k != "samples"}
                entry["thresholds"][str(t)] = objects
            report["levels"][str(level)] = entry
        report["max_rss_kb"] = max_rss_kb()
        report["finished"] = iso()
        return report

