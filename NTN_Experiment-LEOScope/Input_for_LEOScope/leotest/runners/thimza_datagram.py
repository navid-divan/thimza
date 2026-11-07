import platform
import re

from leotest import wire
from leotest.harness import LEVEL_NAMES, honest_signature_fast, signer_keys
from leotest.metrics import jitter_report, summarize
from leotest.runner import LeotestRunner
from leotest.utils import execute, iso, which


_RTT_RE = re.compile(r"time[=<]\s*([0-9.]+)\s*ms")
_SEQ_RE = re.compile(r"icmp_seq[= ](\d+)")
_LOSS_RE = re.compile(
    r"(\d+) packets transmitted, (\d+) (?:packets )?received.*?([0-9.]+)% packet loss", re.DOTALL
)


def thimza_catalogue(levels):
    """One entry per distinct object size: commitments, openings, responses, keys, signatures."""
    plan = {}
    for level in levels:
        name = LEVEL_NAMES.get(level, str(level))
        scheme = signer_keys(level, 2, honest=False)
        layout = wire.Layout(scheme)
        items = {
            "round 1 commitment": layout.hbytes,
            "round 2 opening": wire.packed_len(layout.k * layout.phi, layout.bits_wbar),
            "round 3 response": wire.packed_len(layout.ell * layout.phi, layout.bits_q),
            "verification key": len(wire.encode_vk(layout, scheme.vk)),
        }
        sig_scheme, sig = honest_signature_fast(level, 1024, b"datagram")
        items["signature at t=1024"] = len(
            wire.encode_signature(wire.Layout(sig_scheme), sig_scheme, b"datagram", sig)
        )
        for label, size in items.items():
            plan.setdefault(int(size), []).append("level %s %s" % (name, label))
    return plan


class ThimzaDatagramClient(LeotestRunner):
    def __init__(self, testname, config=None, **kwargs):
        super().__init__(
            name=testname,
            title="Single-datagram delivery of Thimza objects",
            description="ICMP echo with payloads equal to the size of each Thimza object",
            config=config,
            **kwargs
        )

    def _one_run(self, target, size, count, interval, deadline_s):
        args = ["-n", "-c", count, "-i", interval, "-s", size]
        if platform.system() == "Linux":
            args += ["-W", int(self.param("reply_timeout_s", 3))]
        result = execute("ping", *args, target, timeout=deadline_s)
        rtts = [float(m.group(1)) for m in _RTT_RE.finditer(result["stdout"])]
        loss = _LOSS_RE.search(result["stdout"])
        return {
            "record": "ping",
            "target": target,
            "payload_bytes": size,
            "ip_packet_bytes": size + 28,
            "exceeds_1500_byte_mtu": (size + 28) > 1500,
            "count": count,
            "interval_s": interval,
            "returncode": result["returncode"],
            "replies": len(rtts),
            "loss_percent": float(loss.group(3)) if loss else (100.0 * (count - len(rtts)) / count),
            "rtt_ms": summarize(rtts, unit="ms"),
            "jitter_ms": jitter_report(rtts),
            "rtt_samples_ms": rtts,
            "stderr": result["stderr"][:1000],
            "start": result["start"],
        }

    def _start_test(self, artifact_name):
        if which("ping") is None:
            return {"available": False, "error": "ping binary not present"}
        levels = [int(x) for x in self.param("levels", [128, 192, 256])]
        targets = self.param("targets", ["8.8.8.8"])
        count = int(self.param("count", 20))
        interval = float(self.param("interval", 0.2))
        plan = thimza_catalogue(levels)
        for size in self.param("baseline_payload_bytes", [56, 1024, 1472]):
            plan.setdefault(int(size), []).append("baseline")
        ordered = sorted(plan.items())
        deadline = count * interval + float(self.param("run_slack_s", 12))
        report = {
            "started": iso(),
            "targets": targets,
            "plan": [{"payload_bytes": size, "objects": tags} for size, tags in ordered],
            "runs": [],
            "skipped": [],
        }
        for target in targets:
            for size, tags in ordered:
                remaining = self.remaining_budget()
                if self.budget_exhausted() or (remaining is not None and remaining < deadline):
                    report["skipped"].append({"target": target, "payload_bytes": size})
                    continue
                record = self._one_run(target, size, count, interval, deadline)
                record["objects"] = tags
                self.emit(record)
                report["runs"].append({k: v for k, v in record.items() if k != "record"})
        report["finished"] = iso()
        return report
