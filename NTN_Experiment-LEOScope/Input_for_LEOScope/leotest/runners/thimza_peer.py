"""A distributed Thimza signing session across the satellite link.

The measurement node plays signer 1. A server node, given in the LEOScope
"Server" field, plays the coordinator, the combiner and signers 2..t. Every
message is a real Thimza message, the channel is plain TCP because Thimza needs
no authenticated channel, and the signature produced at the end is verified on
both sides. Both sides derive the same (t, t) key from a seed sent in the clear,
which stands in for the trusted dealer of the scheme.

Without a server, the client records that it was skipped.
"""
import json
import os
import socket
import struct
import time

from leotest import wire
from leotest.harness import LEVEL_NAMES, level_params, ms_since, now_ns, reseed
from leotest.metrics import summarize
from leotest.runner import LeotestRunner
from leotest.utils import iso, is_server_mode, server_ip_from_env


def _send(sock, payload):
    sock.sendall(struct.pack(">I", len(payload)) + payload)


def _recv_exact(sock, count):
    chunks = []
    while count > 0:
        chunk = sock.recv(min(1 << 16, count))
        if not chunk:
            raise ConnectionError("peer closed the connection")
        chunks.append(chunk)
        count -= len(chunk)
    return b"".join(chunks)


def _recv(sock):
    (size,) = struct.unpack(">I", _recv_exact(sock, 4))
    return _recv_exact(sock, size)


def _keys(level, t, key_seed):
    from thimza.schemes.thimza_scheme import Thimza

    scheme = Thimza(level_params(level), seed=int(key_seed))
    scheme.keygen(t, t)
    reseed(scheme)
    return scheme


class ThimzaPeerClient(LeotestRunner):
    def __init__(self, testname, config=None, **kwargs):
        super().__init__(
            name=testname,
            title="Distributed Thimza signing between the node and a server node",
            description="Real coordinator and peers on a server node, signer 1 behind the LEO link",
            config=config,
            **kwargs
        )

    # ---------------------------------------------------------------- server
    def _serve_one(self, conn):
        hello = json.loads(_recv(conn).decode())
        level, t = int(hello["level"]), int(hello["t"])
        msg = bytes.fromhex(hello["msg"])
        S = _keys(level, t, hello["key_seed"])
        L = wire.Layout(S)
        T = list(range(1, t + 1))
        timing = {}
        started = now_ns()
        tokens, cmts = {}, {}
        for j in T[1:]:
            tokens[j], cmts[j] = S.round1(j, msg)
        timing["peers_round1_ms"] = ms_since(started)
        _send(conn, b"READY")

        cmts[1] = _recv(conn)
        ordered = [cmts[j] for j in T]
        _send(conn, wire.encode_request(L, msg, T, ordered))
        started = now_ns()
        wbars = {j: S.round2(tokens[j], T, ordered) for j in T[1:]}
        timing["peers_round2_ms"] = ms_since(started)

        wbars[1] = wire.decode_wbar(L, _recv(conn))
        opened = [wbars[j] for j in T]
        _send(conn, wire.encode_openings(L, opened))
        started = now_ns()
        zs = {}
        c = w = None
        for j in T[1:]:
            zs[j], c, w, _ = S.round3(tokens[j], T, ordered, opened)
        timing["peers_round3_ms"] = ms_since(started)

        zs[1] = wire.decode_z(L, _recv(conn))
        started = now_ns()
        if c is None:
            raise RuntimeError("t = 1 is not a threshold session")
        sig = S.combine(T, msg, [zs[j] for j in T], c, w)
        timing["combine_ms"] = ms_since(started)
        timing["server_verifies"] = bool(S.verify(msg, sig))
        _send(conn, wire.encode_signature(L, S, msg, sig))
        timing["client_result"] = _recv(conn).decode()
        _send(conn, json.dumps(timing).encode())
        return {"level": level, "t": t, "server": timing}

    def _serve(self, port):
        listener = socket.socket(socket.AF_INET6 if socket.has_ipv6 else socket.AF_INET, socket.SOCK_STREAM)
        listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        if listener.family == socket.AF_INET6:
            listener.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 0)
            listener.bind(("::", port))
        else:
            listener.bind(("0.0.0.0", port))
        listener.listen(8)
        listener.settimeout(5.0)
        served, failed = 0, 0
        while not self.budget_exhausted():
            try:
                conn, addr = listener.accept()
            except socket.timeout:
                continue
            try:
                conn.settimeout(60.0)
                conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                result = self._serve_one(conn)
                served += 1
                self.emit({"record": "served", "at": iso(), "data": result})
            except Exception as exc:
                failed += 1
                self.emit({"record": "serve_error", "error": "%s: %s" % (type(exc).__name__, exc)})
            finally:
                conn.close()
        listener.close()
        return {"mode": "server", "sessions_served": served, "sessions_failed": failed}

    # ---------------------------------------------------------------- client
    def _connect(self, host, port, wait_s):
        deadline = time.monotonic() + wait_s
        last = None
        while time.monotonic() < deadline and not self.budget_exhausted():
            started = now_ns()
            try:
                sock = socket.create_connection((host, port), timeout=10.0)
                sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                sock.settimeout(60.0)
                return sock, ms_since(started)
            except OSError as exc:
                last = exc
                time.sleep(2.0)
        raise ConnectionError("server %s:%d not reachable: %s" % (host, port, last))

    def _session(self, host, port, level, t, msg, wait_s):
        record = {"record": "peer_session", "level": level, "t": t, "ok": False, "error": None}
        sock = None
        try:
            sock, record["tcp_connect_ms"] = self._connect(host, port, wait_s)
            key_seed = int.from_bytes(os.urandom(6), "little")
            _send(sock, json.dumps({"level": level, "t": t, "key_seed": key_seed, "msg": msg.hex()}).encode())
            S = _keys(level, t, key_seed)
            L = wire.Layout(S)
            if _recv(sock) != b"READY":
                raise RuntimeError("server did not get ready")
            legs, compute = {}, {}
            record["start_unix"] = time.time()
            wall = now_ns()

            started = now_ns()
            token, cmt = S.round1(1, msg)
            compute["round1"] = ms_since(started)
            cmt_bytes = wire.encode_cmt(cmt)
            started = now_ns()
            _send(sock, cmt_bytes)
            request = _recv(sock)
            legs["cmt_up_request_down"] = ms_since(started)
            m2, T, cmts = wire.decode_request(L, request)
            if m2 != msg or T != list(range(1, t + 1)):
                raise RuntimeError("request does not match the session")

            started = now_ns()
            wbar = S.round2(token, T, cmts)
            compute["round2"] = ms_since(started)
            wbar_bytes = wire.encode_wbar(L, wbar)
            started = now_ns()
            _send(sock, wbar_bytes)
            openings = _recv(sock)
            legs["opening_up_openings_down"] = ms_since(started)
            wbars = wire.decode_openings(L, openings, t)

            started = now_ns()
            z, _, _, _ = S.round3(token, T, cmts, wbars)
            compute["round3"] = ms_since(started)
            z_bytes = wire.encode_z(L, z)
            started = now_ns()
            _send(sock, z_bytes)
            blob = _recv(sock)
            legs["response_up_signature_down"] = ms_since(started)
            started = now_ns()
            ok = bool(S.verify(msg, wire.decode_signature(L, blob)))
            compute["decode_and_verify"] = ms_since(started)
            record["wall_to_verified_signature_ms"] = ms_since(wall)
            _send(sock, b"OK" if ok else b"FAIL")
            record["server"] = json.loads(_recv(sock).decode())
            serial = float(record["server"].get("peers_round3_ms", 0.0))
            record["to_verified_parallel_peers_ms"] = (
                record["wall_to_verified_signature_ms"] - serial * (t - 2) / float(t - 1)
                if t > 1
                else record["wall_to_verified_signature_ms"]
            )
            record.update(
                {
                    "legs_ms": legs,
                    "compute_ms": compute,
                    "client_verifies": ok,
                    "bytes": {
                        "sent": len(cmt_bytes) + len(wbar_bytes) + len(z_bytes),
                        "received": len(request) + len(openings) + len(blob),
                        "signature": len(blob),
                    },
                    "ok": ok and bool(record["server"].get("server_verifies")),
                }
            )
        except Exception as exc:
            record["error"] = "%s: %s" % (type(exc).__name__, exc)
        finally:
            if sock is not None:
                sock.close()
        return record

    def _start_test(self, artifact_name):
        port = int(self.param("port", 45401))
        if is_server_mode() or self.param("force_server", False):
            return self._serve(port)
        host = self.param("server_host") or server_ip_from_env()
        if not host:
            return {"mode": "client", "skipped": "no server node configured", "started": iso()}
        levels = [int(x) for x in self.param("levels", [128, 192, 256])]
        thresholds = [int(x) for x in self.param("thresholds", [2, 4, 8, 16])]
        sessions = int(self.param("sessions", 15))
        wait_s = float(self.param("connect_wait_s", 60))
        msg = b"m" * int(self.param("message_bytes", 32))
        started = iso()
        records = []
        for _ in range(sessions):
            for level in levels:
                for t in thresholds:
                    if self.budget_exhausted():
                        continue
                    record = self._session(host, port, level, t, msg, wait_s)
                    self.emit(record)
                    records.append(record)
        summary = {}
        for level in levels:
            for t in thresholds:
                good = [r for r in records if r["ok"] and r["level"] == level and r["t"] == t]
                summary["%d/%d" % (level, t)] = {
                    "level_name": LEVEL_NAMES.get(level),
                    "sessions": sum(1 for r in records if r["level"] == level and r["t"] == t),
                    "succeeded": len(good),
                    "to_verified_signature_ms": summarize(
                        [r["wall_to_verified_signature_ms"] for r in good], unit="ms"
                    ),
                    "to_verified_parallel_peers_ms": summarize(
                        [r["to_verified_parallel_peers_ms"] for r in good], unit="ms"
                    ),
                    "server_peers_round3_ms": summarize(
                        [r["server"]["peers_round3_ms"] for r in good], unit="ms"
                    ),
                    "legs_ms": {
                        name: summarize([r["legs_ms"][name] for r in good], unit="ms")
                        for name in ("cmt_up_request_down", "opening_up_openings_down", "response_up_signature_down")
                    },
                }
        return {
            "mode": "client",
            "server_host_configured": True,
            "port": port,
            "sessions_run": len(records),
            "errors": sorted({r["error"] for r in records if r["error"]}),
            "summary": summary,
            "started": started,
            "finished": iso(),
        }
