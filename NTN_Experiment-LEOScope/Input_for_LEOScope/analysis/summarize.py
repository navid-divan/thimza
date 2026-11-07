"""Turn a finished run (a directory or the .zip that LEOScope produces) into CSV tables.

    python3 analysis/summarize.py <run.zip or artifacts directory> --out tables
"""
import argparse
import csv
import json
import os
import tempfile
import zipfile

# Signing time of one signer in ms in the paper (Apple M2, best of three runs).
PAPER_SIGN_MS = {
    128: {16: 3.1, 128: 9.6, 1024: 60.2},
    192: {16: 4.2, 128: 13.2, 1024: 83.9},
    256: {16: 4.7, 128: 14.8, 1024: 95.3},
}
PAPER_RTT_MS = 100.0
PAPER_BANDWIDTH_BPS = 100e6


def load(root):
    docs = {}
    for base, _, files in os.walk(root):
        for name in files:
            if name == "summary.json" or name == "manifest.json":
                path = os.path.join(base, name)
                try:
                    with open(path, "r", encoding="utf-8") as handle:
                        doc = json.load(handle)
                except (OSError, json.JSONDecodeError):
                    continue
                key = "manifest" if name == "manifest.json" else os.path.basename(base)
                docs[key] = doc
    return docs


def result(docs, name):
    doc = docs.get(name)
    if not doc or doc.get("status") != "ok":
        return None
    return doc.get("result")


def med(stats):
    return stats.get("median") if isinstance(stats, dict) else None


def write(path, rows):
    if not rows:
        return False
    fields = []
    for row in rows:
        for key in row:
            if key not in fields:
                fields.append(key)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({k: (round(v, 4) if isinstance(v, float) else v) for k, v in row.items()})
    return True


def node_rows(docs):
    rows = []
    manifest = docs.get("manifest") or {}
    info = result(docs, "sysinfo") or {}
    selftest = result(docs, "thimza_selftest") or {}
    hw = info.get("hardware") or {}
    rows.append(
        {
            "start": manifest.get("start"),
            "end": manifest.get("end"),
            "wall_s": manifest.get("wall_s"),
            "cpu": hw.get("cpu_model"),
            "cores": hw.get("cpu_count"),
            "memory_kb": hw.get("mem_total_kb"),
            "machine": hw.get("machine"),
            "numpy": (info.get("numpy") or {}).get("version"),
            "python_ssl": info.get("python_ssl"),
            "thimza_tree_sha256": ((info.get("provenance") or {}).get("thimza") or {}).get("tree_sha256"),
            "selftest_all_required_passed": selftest.get("all_required_passed"),
            "gaussian_kats_match_reference": selftest.get("gaussian_kats_match"),
            "stages": " ".join(
                "%s:%s" % (r.get("test"), r.get("status")) for r in manifest.get("results", [])
            ),
        }
    )
    return rows


def time_rows(docs):
    res = result(docs, "thimza_time")
    if not res:
        return []
    rows = []
    for level, entry in res["levels"].items():
        level = int(level)
        traccoon = {r["t"]: r for r in entry.get("traccoon", []) if "signer_ms" in r}
        verify = med((entry.get("verify") or {}).get("ms"))
        for row in entry.get("thimza", []):
            if "signer_ms" not in row:
                continue
            t = row["t"]
            s = row["signer_ms"]
            tr = traccoon.get(t)
            tr_sign = med(tr["signer_ms"]["sign"]) if tr else None
            rows.append(
                {
                    "level": level,
                    "t": t,
                    "round1_ms": med(s["round1"]),
                    "round2_ms": med(s["round2"]),
                    "round3_ms": med(s["round3"]),
                    "sign_ms": med(s["sign"]),
                    "sign_p95_ms": s["sign"].get("p95"),
                    "sign_best_ms": s["sign"].get("best"),
                    "samples": s["sign"].get("n"),
                    "paper_sign_ms_m2": PAPER_SIGN_MS.get(level, {}).get(t),
                    "dealer_keygen_ms": med(row["dealer_keygen_ms"]),
                    "combine_ms": med(row["combine_ms"]),
                    "verify_ms": verify,
                    "traccoon_sign_ms": tr_sign,
                    "speedup_over_traccoon": (tr_sign / med(s["sign"])) if tr_sign and med(s["sign"]) else None,
                }
            )
    return rows


def space_rows(docs):
    res = result(docs, "thimza_space")
    if not res:
        return []
    rows = []
    for level, entry in res["levels"].items():
        for t, o in entry["thresholds"].items():
            if "bytes" not in o:
                continue
            b = o["bytes"]
            sig = o.get("signature") or {}
            rows.append(
                {
                    "level": int(level),
                    "t": int(t),
                    "cmt": b["cmt"],
                    "wbar": b["wbar"],
                    "z": b["z"],
                    "sent_per_signer": o["per_signer"]["sent_bytes"],
                    "request_received": b["request"],
                    "openings_received": b["openings"],
                    "received_per_signer": o["per_signer"]["received_bytes"],
                    "received_over_sent": o["per_signer"]["received_over_sent"],
                    "vk": b["vk"],
                    "sk": b["sk"],
                    "signature_compact_median": med(sig.get("compact_bytes")),
                    "signature_compact_max": (sig.get("compact_bytes") or {}).get("max"),
                    "signature_fixed_width": sig.get("fixed_bytes"),
                    "signature_paper_model": sig.get("paper_model_bytes"),
                    "signatures_all_verify": sig.get("all_verify"),
                    "state_after_round1": o["state_bytes"]["after_round1"]["bytes"],
                    "state_after_round2": o["state_bytes"]["after_round2"]["bytes"],
                    "codec_equals_paper_r1_r2_r3_vk": all(o["paper_model_matches"].values()),
                }
            )
    return rows


def link_rows(docs):
    res = result(docs, "thimza_link")
    if not res or "summary" not in res:
        return [], []
    rows, phase_rows = [], []
    for key, s in res["summary"].items():
        if "exchanges" not in s or not s.get("succeeded"):
            continue
        ex = s["exchanges"]
        sent = s.get("bytes_sent_per_session") or {}
        received = s.get("bytes_received_per_session") or {}
        sent_total = sum(sent.values())
        received_total = sum(received.values())
        compute = sum(med(s["compute_ms"][r]) or 0.0 for r in ("round1", "round2", "round3"))
        rtt = med(ex["baseline"]["network_ms"])
        goodput = med(s["openings_goodput_mbps"])
        paper_model = 3 * PAPER_RTT_MS + sent_total * 8.0 / PAPER_BANDWIDTH_BPS * 1000.0 + compute
        byte_complete = None
        if rtt is not None and goodput:
            byte_complete = 3 * rtt + (sent_total + received_total) * 8.0 / (goodput * 1e6) * 1000.0 + compute
        rows.append(
            {
                "level": s["level"],
                "t": s["t"],
                "mode": s["mode"],
                "sessions_ok": s["succeeded"],
                "sessions": s["sessions"],
                "bytes_sent": sent_total,
                "bytes_received": received_total,
                "rtt_raw_ms": med(ex["baseline"]["ms"]),
                "rtt_network_ms": rtt,
                "server_tcp_rtt_ms": med(ex["baseline"]["server_tcp_rtt_ms"]),
                "tcp_connect_ms": med(s["tcp_connect_ms"]),
                "tls_handshake_ms": med(s["tls_handshake_ms"]),
                "compute_ms": compute,
                "round1_network_ms": med(ex["round1"]["network_ms"]),
                "round2_network_ms": med(ex["round2"]["network_ms"]),
                "round3_network_ms": med(ex["round3"]["network_ms"]),
                "openings_goodput_mbps": goodput,
                "session_ms": med(s["session_ms"]),
                "session_p95_ms": s["session_ms"].get("p95"),
                "session_network_only_ms": med(s["session_network_only_ms"]),
                "session_network_only_p95_ms": s["session_network_only_ms"].get("p95"),
                "with_connection_setup_ms": med(s["session_with_connection_setup_ms"]),
                "to_verified_signature_ms": med(s["to_verified_signature_ms"]),
                "paper_model_ms": paper_model,
                "byte_complete_model_ms": byte_complete,
                "signatures_verified": s["signatures_verified"],
                "server_reported_retransmissions": s["server_reported_retransmissions"],
                "errors": " | ".join(s["errors"]),
            }
        )
        for b in s["phase_profile"]:
            phase_rows.append(
                {
                    "level": s["level"],
                    "t": s["t"],
                    "phase_lo_s": b["phase_lo_s"],
                    "phase_hi_s": b["phase_hi_s"],
                    "sessions": b["stats"].get("n"),
                    "session_median_ms": b["stats"].get("median"),
                    "session_p95_ms": b["stats"].get("p95"),
                }
            )
    return rows, phase_rows


def datagram_rows(docs):
    res = result(docs, "thimza_datagram")
    if not res:
        return []
    return [
        {
            "payload_bytes": r["payload_bytes"],
            "ip_packet_bytes": r["ip_packet_bytes"],
            "objects": "; ".join(r["objects"]),
            "loss_percent": r["loss_percent"],
            "rtt_median_ms": med(r["rtt_ms"]),
            "replies": r["replies"],
            "count": r["count"],
        }
        for r in res["runs"]
    ]


def peer_rows(docs):
    res = result(docs, "thimza_peer")
    if not res or "summary" not in res:
        return []
    rows = []
    for key, s in res["summary"].items():
        level, t = key.split("/")
        rows.append(
            {
                "level": int(level),
                "t": int(t),
                "sessions_ok": s["succeeded"],
                "sessions": s["sessions"],
                "to_verified_signature_ms": med(s["to_verified_signature_ms"]),
                "to_verified_parallel_peers_ms": med(s.get("to_verified_parallel_peers_ms")),
                "round1_exchange_ms": med(s["legs_ms"]["cmt_up_request_down"]),
                "round2_exchange_ms": med(s["legs_ms"]["opening_up_openings_down"]),
                "round3_exchange_ms": med(s["legs_ms"]["response_up_signature_down"]),
            }
        )
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", help="artifacts directory or LEOScope .zip")
    parser.add_argument("--out", default="tables")
    args = parser.parse_args()

    root = args.source
    tmp = None
    if zipfile.is_zipfile(root):
        tmp = tempfile.mkdtemp(prefix="thimza-ntn-")
        with zipfile.ZipFile(root) as handle:
            handle.extractall(tmp)
        root = tmp
    docs = load(root)
    os.makedirs(args.out, exist_ok=True)
    link, phase = link_rows(docs)
    tables = {
        "node.csv": node_rows(docs),
        "time.csv": time_rows(docs),
        "space.csv": space_rows(docs),
        "link.csv": link,
        "link_phase.csv": phase,
        "datagram.csv": datagram_rows(docs),
        "peer.csv": peer_rows(docs),
    }
    for name, rows in tables.items():
        if write(os.path.join(args.out, name), rows):
            print("wrote %s (%d rows)" % (os.path.join(args.out, name), len(rows)))
    if link:
        print()
        print("%-5s %-5s %10s %10s %12s %12s %12s" % (
            "level", "t", "received", "session", "net only", "paper model", "byte model"))
        for r in link:
            print("%-5d %-5d %10d %10.1f %12.1f %12.1f %12s" % (
                r["level"], r["t"], r["bytes_received"], r["session_ms"] or -1,
                r["session_network_only_ms"] or -1, r["paper_model_ms"],
                "%.1f" % r["byte_complete_model_ms"] if r["byte_complete_model_ms"] else "-"))


if __name__ == "__main__":
    main()
