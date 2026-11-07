"""Thimza signing sessions in which every round crosses the satellite link.

The node plays signer 1 of a signer set T = {1..t}. A session opens a TCP and
TLS 1.3 connection, measures one empty request as the reference round trip,
and then runs the three rounds. Each round computes the signer's message with
the unmodified Thimza code and sends it in one pipelined exchange that returns
the coordinator's next broadcast:

    round 1: cmt_i up,  the request V = (msg, T, (cmt_j)_j) down
    round 2: wbar_i up, the t openings (wbar_j)_j down
    round 3: z_i up,    the combined signature down, which is then verified

The uplink bodies are the real encoded messages. The downlink bodies have the
exact length of the real broadcasts; their content comes from the endpoint.
With t <= honest_max_t the t signers are all real and the session produces a
signature of its own; above that, peers are simulated as in the paper's
benchmark and the signature delivered in round 3 is a valid signature for the
same level and t, drawn before the session.
"""
import random
import re
import subprocess
import time

from leotest import wire
from leotest.harness import (
    LEVEL_NAMES,
    Session,
    honest_signature_fast,
    ms_since,
    now_ns,
    signer_keys,
)
from leotest.metrics import bin_by_phase, jitter_report, summarize
from leotest.netlink import Link
from leotest.runner import LeotestRunner
from leotest.utils import iso, which

ROUNDS = ("round1", "round2", "round3")
_GROUP_RE = re.compile(r"Negotiated TLS1\.3 group:\s*(\S+)")
_TEMPKEY_RE = re.compile(r"Peer Temp Key:\s*([^,\n]+)")


def _tls_group_probe(host, port):
    """The key-exchange group that this image's OpenSSL negotiates by default."""
    if which("openssl") is None:
        return {"available": False}
    cmd = ["openssl", "s_client", "-connect", "%s:%d" % (host, port), "-servername", host,
           "-tls1_3", "-brief"]
    try:
        proc = subprocess.run(cmd, input="", text=True, capture_output=True, timeout=20, check=False)
    except subprocess.TimeoutExpired:
        return {"available": True, "negotiated_group": None, "established": False, "error": "timeout"}
    blob = proc.stdout + proc.stderr
    match = _GROUP_RE.search(blob) or _TEMPKEY_RE.search(blob)
    return {
        "available": True,
        "negotiated_group": match.group(1).strip() if match else None,
        "established": "CONNECTION ESTABLISHED" in blob,
    }


class ThimzaLinkClient(LeotestRunner):
    def __init__(self, testname, config=None, **kwargs):
        super().__init__(
            name=testname,
            title="Thimza signing sessions over the LEO link",
            description="Each round of one signer is one exchange across the satellite link on TLS 1.3",
            config=config,
            **kwargs
        )

    # ---------------------------------------------------------------- setup
    def _endpoint(self):
        endpoint = self.param("endpoint", {}) or {}
        return {
            "host": endpoint.get("host", "speed.cloudflare.com"),
            "port": int(endpoint.get("port", 443)),
            "up_path": endpoint.get("up_path", "/__up"),
            "down_path": endpoint.get("down_path", "/__down?bytes={n}"),
            "cafile": endpoint.get("cafile"),
        }

    def _prepare(self, levels, thresholds, msg, honest_max_t):
        configs = {}
        for level in levels:
            for t in thresholds:
                honest = t <= honest_max_t
                scheme = signer_keys(level, t, honest=honest)
                layout = wire.Layout(scheme)
                sig_scheme, sig = honest_signature_fast(level, t, msg)
                sig_layout = wire.Layout(sig_scheme)
                configs[(level, t)] = {
                    "level": level,
                    "t": t,
                    "honest": honest,
                    "scheme": scheme,
                    "layout": layout,
                    "request_bytes": wire.request_len(layout, len(msg), t),
                    "openings_bytes": wire.openings_len(layout, t),
                    "signature_scheme": sig_scheme,
                    "signature_layout": sig_layout,
                    "signature_blob": wire.encode_signature(sig_layout, sig_scheme, msg, sig),
                }
        return configs

    def _schedule(self, configs, counts, seed):
        rng = random.Random(seed)
        pending = {key: int(counts.get(key[1], counts.get("default", 10))) for key in configs}
        order = []
        while any(pending.values()):
            batch = [key for key, left in pending.items() if left > 0]
            rng.shuffle(batch)
            for key in batch:
                order.append(key)
                pending[key] -= 1
        return order

    # -------------------------------------------------------------- session
    def _exchange(self, link, record, name, steps, expected_down):
        if not link.alive():
            started = now_ns()
            link.open()
            record["reconnects"].append({"before": name, "ms": ms_since(started)})
        leg = link.exchange(steps)
        leg["phase_s"] = leg["start_unix"] % self._epoch
        leg["expected_down"] = expected_down
        record["exchanges"][name] = leg
        if any(status != 200 for status in leg["statuses"]):
            raise RuntimeError("%s returned HTTP %s" % (name, leg["statuses"]))
        if expected_down is not None and leg["body_received"] != expected_down:
            raise RuntimeError(
                "%s delivered %d bytes, expected %d" % (name, leg["body_received"], expected_down)
            )
        return leg

    def _session(self, cfg, index, endpoint, msg, include_signature):
        up = endpoint["up_path"]
        down = endpoint["down_path"]
        record = {
            "record": "session",
            "index": index,
            "level": cfg["level"],
            "t": cfg["t"],
            "mode": "honest" if cfg["honest"] else "simulated peers",
            "exchanges": {},
            "reconnects": [],
            "ok": False,
            "error": None,
        }
        link = Link(endpoint["host"], endpoint["port"], self._timeout, endpoint["cafile"])
        try:
            record["start_unix"] = time.time()
            record["phase_s"] = record["start_unix"] % self._epoch
            record["connection"] = link.open()
            self._exchange(link, record, "baseline", [("GET", down.format(n=0), None)], 0)

            session = Session(cfg["scheme"], cfg["t"], msg, cfg["honest"])
            wall = now_ns()
            cmt = session.round1()
            request_len = cfg["request_bytes"]
            self._exchange(
                link, record, "round1",
                [("POST", up, cmt), ("GET", down.format(n=request_len), None)], request_len,
            )
            if len(session.request_bytes()) != request_len:
                raise RuntimeError("request encoding has an unexpected length")

            wbar = session.round2()
            openings_len = cfg["openings_bytes"]
            self._exchange(
                link, record, "round2",
                [("POST", up, wbar), ("GET", down.format(n=openings_len), None)], openings_len,
            )

            z = session.round3()
            blob = cfg["signature_blob"]
            if include_signature:
                steps = [("POST", up, z), ("GET", down.format(n=len(blob)), None)]
                expected = len(blob)
            else:
                steps = [("POST", up, z)]
                expected = None
            self._exchange(link, record, "round3", steps, expected)
            record["wall_session_ms"] = ms_since(wall)
            record["end_unix"] = time.time()
            record["compute_ms"] = dict(session.compute_ms)
            record["sent_bytes"] = {"cmt": len(cmt), "wbar": len(wbar), "z": len(z)}
            record["received_bytes"] = {"request": request_len, "openings": openings_len}
            if include_signature:
                started = now_ns()
                decoded = wire.decode_signature(cfg["signature_layout"], blob)
                record["signature_verifies"] = bool(cfg["signature_scheme"].verify(msg, decoded))
                record["compute_ms"]["decode_and_verify"] = ms_since(started)
                record["received_bytes"]["signature"] = len(blob)
            record["ok"] = True
        except Exception as exc:
            record["error"] = "%s: %s" % (type(exc).__name__, exc)
        finally:
            record["http_requests"] = link.requests
            record["volume_bytes"] = {"up": link.sent_bytes, "down": link.received_bytes}
            link.close()
        if record["ok"]:
            self._totals(record)
        return record

    def _totals(self, record):
        ex = record["exchanges"]
        compute = sum(record["compute_ms"][r] for r in ROUNDS)
        record["signer_compute_ms"] = compute
        record["signer_done_ms"] = (
            compute + ex["round1"]["ms"] + ex["round2"]["ms"] + ex["round3"]["first_response_ms"]
        )
        record["session_ms"] = compute + sum(ex[r]["ms"] for r in ROUNDS)
        network = [ex[r]["network_ms"] for r in ROUNDS]
        record["session_network_only_ms"] = (
            compute + sum(network) if all(v is not None for v in network) else None
        )
        conn = record["connection"]
        record["session_with_connection_setup_ms"] = (
            record["session_ms"] + conn["tcp_connect_ms"] + conn["tls_handshake_ms"]
        )
        if "decode_and_verify" in record["compute_ms"]:
            record["to_verified_signature_ms"] = (
                record["session_ms"] + record["compute_ms"]["decode_and_verify"]
            )
        down2 = ex["round2"]["responses"][-1]
        tail_ms = down2["done_ms"] - ex["round2"]["first_response_ms"] - (down2["server_ms"] or 0.0)
        record["openings_goodput_mbps"] = (
            record["received_bytes"]["openings"] * 8.0 / (tail_ms / 1000.0) / 1e6 if tail_ms > 0 else None
        )

    # -------------------------------------------------------------- summary
    def _summary(self, records):
        out = {}
        groups = {}
        for rec in records:
            groups.setdefault((rec["level"], rec["t"]), []).append(rec)
        for (level, t), recs in sorted(groups.items()):
            good = [r for r in recs if r["ok"]]

            def values(fn):
                vals = []
                for r in good:
                    try:
                        v = fn(r)
                    except (KeyError, TypeError, IndexError):
                        continue
                    if v is not None:
                        vals.append(v)
                return vals

            exchanges = {}
            for name in ("baseline",) + ROUNDS:
                exchanges[name] = {
                    "ms": summarize(values(lambda r: r["exchanges"][name]["ms"]), unit="ms"),
                    "network_ms": summarize(values(lambda r: r["exchanges"][name]["network_ms"]), unit="ms"),
                    "server_ms": summarize(values(lambda r: r["exchanges"][name]["server_ms"]), unit="ms"),
                    "server_tcp_rtt_ms": summarize(
                        values(
                            lambda r: r["exchanges"][name]["responses"][-1]["server_timing"]["l4"]["rtt"] / 1000.0
                        ),
                        unit="ms",
                    ),
                }
            session = values(lambda r: r["session_ms"])
            out["%d/%d" % (level, t)] = {
                "level": level,
                "level_name": LEVEL_NAMES.get(level),
                "t": t,
                "mode": recs[0]["mode"],
                "sessions": len(recs),
                "succeeded": len(good),
                "errors": sorted({r["error"] for r in recs if r["error"]}),
                "bytes_sent_per_session": good[0]["sent_bytes"] if good else None,
                "bytes_received_per_session": good[0]["received_bytes"] if good else None,
                "tcp_connect_ms": summarize(values(lambda r: r["connection"]["tcp_connect_ms"]), unit="ms"),
                "tls_handshake_ms": summarize(values(lambda r: r["connection"]["tls_handshake_ms"]), unit="ms"),
                "compute_ms": {
                    name: summarize(values(lambda r: r["compute_ms"][name]), unit="ms")
                    for name in ROUNDS + ("decode_and_verify",)
                },
                "exchanges": exchanges,
                "openings_goodput_mbps": summarize(values(lambda r: r["openings_goodput_mbps"]), unit="Mbit/s"),
                "signer_done_ms": summarize(values(lambda r: r["signer_done_ms"]), unit="ms"),
                "session_ms": summarize(session, unit="ms"),
                "session_jitter_ms": jitter_report(session),
                "session_network_only_ms": summarize(values(lambda r: r["session_network_only_ms"]), unit="ms"),
                "session_with_connection_setup_ms": summarize(
                    values(lambda r: r["session_with_connection_setup_ms"]), unit="ms"
                ),
                "to_verified_signature_ms": summarize(values(lambda r: r["to_verified_signature_ms"]), unit="ms"),
                "signatures_verified": sum(1 for r in good if r.get("signature_verifies")),
                "server_reported_retransmissions": sum(
                    int(resp["server_timing"]["l4"].get("retrans", 0) > 0)
                    for r in good
                    for leg in r["exchanges"].values()
                    for resp in leg["responses"]
                    if resp.get("server_timing") and resp["server_timing"].get("l4")
                ),
                "phase_profile": bin_by_phase(good, "start_unix", "session_ms", self._epoch, self._bins),
            }
        return out

    # ----------------------------------------------------------------- main
    def _start_test(self, artifact_name):
        levels = [int(x) for x in self.param("levels", [128, 192, 256])]
        thresholds = [int(x) for x in self.param("thresholds", [2, 16, 128, 1024])]
        counts = {
            (int(k) if str(k).isdigit() else k): int(v)
            for k, v in (self.param("sessions", {}) or {}).items()
        }
        msg = b"m" * int(self.param("message_bytes", 32))
        honest_max_t = int(self.param("honest_max_t", 16))
        include_signature = bool(self.param("include_signature_leg", True))
        gap_s = float(self.param("max_gap_s", 1.0))
        self._timeout = float(self.param("timeout_s", 30))
        self._epoch = float(self.param("epoch_period_s", 15.0))
        self._bins = int(self.param("phase_bins", 15))
        endpoint = self._endpoint()

        report = {
            "started": iso(),
            "endpoint": {k: v for k, v in endpoint.items() if k != "cafile"},
            "levels": levels,
            "thresholds": thresholds,
            "message_bytes": len(msg),
            "honest_max_t": honest_max_t,
            "tls_group_probe": _tls_group_probe(endpoint["host"], endpoint["port"]),
        }
        probe = Link(endpoint["host"], endpoint["port"], self._timeout, endpoint["cafile"])
        try:
            report["probe_connection"] = probe.open()
            report["probe_exchange"] = probe.exchange([("GET", endpoint["down_path"].format(n=0), None)])
        except Exception as exc:
            report["error"] = "endpoint unreachable: %s: %s" % (type(exc).__name__, exc)
            return report
        finally:
            probe.close()

        started = time.perf_counter()
        configs = self._prepare(levels, thresholds, msg, honest_max_t)
        report["prepare_s"] = round(time.perf_counter() - started, 2)
        order = self._schedule(configs, counts, seed=int(time.time()))
        report["planned_sessions"] = len(order)
        rng = random.Random()
        records = []
        skipped = 0
        for index, key in enumerate(order):
            remaining = self.remaining_budget()
            if self.budget_exhausted() or (remaining is not None and remaining < 20.0):
                skipped += 1
                continue
            record = self._session(configs[key], index, endpoint, msg, include_signature)
            self.emit(record)
            records.append(record)
            if gap_s > 0:
                time.sleep(rng.uniform(0.0, gap_s))
        report["sessions_run"] = len(records)
        report["sessions_skipped"] = skipped
        report["volume_bytes"] = {
            "up": sum(r["volume_bytes"]["up"] for r in records),
            "down": sum(r["volume_bytes"]["down"] for r in records),
        }
        report["summary"] = self._summary(records)
        report["finished"] = iso()
        return report
