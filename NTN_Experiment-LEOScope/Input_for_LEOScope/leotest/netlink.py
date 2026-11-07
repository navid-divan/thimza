"""Timed exchanges on one keep-alive HTTPS connection.

A Thimza round of one signer is a message to the coordinator followed by the
coordinator's broadcast. On the public speed-test endpoint of Cloudflare, which
accepts any body on POST /__up and returns exactly N bytes on GET
/__down?bytes=N, a round is therefore one pipelined exchange: the POST that
carries the signer's message and the GET that carries the broadcast are written
back to back on the same TLS 1.3 connection. The server answers in order and
reads the whole POST body before it answers the GET, so the broadcast leaves
only after the signer's message has arrived, and the exchange costs one round
trip plus both transfers, as the protocol does.

The endpoint reports in the Server-Timing header how long it worked on each
request and the TCP state of the connection as the server sees it; both are
parsed, so that the server's own time can be separated from the network time.
"""
import http.client
import re
import socket
import ssl
import time
from urllib.parse import parse_qsl

USER_AGENT = "thimza-ntn/1.0 (LEOScope measurement)"
_DUR_RE = re.compile(r"(\w+);dur=([0-9.]+)")
_DESC_RE = re.compile(r'(\w+);desc="\?([^"]*)"')
_NUMERIC_L4 = (
    "rtt", "min_rtt", "rtt_var", "sent", "recv", "lost", "retrans",
    "sent_bytes", "recv_bytes", "delivery_rate", "cwnd", "unsent_bytes",
)


def parse_server_timing(value):
    if not value:
        return None
    out = {"durations_ms": {}, "l4": None}
    for name, dur in _DUR_RE.findall(value):
        out["durations_ms"][name] = float(dur)
    for name, query in _DESC_RE.findall(value):
        if name != "cfL4":
            continue
        fields = dict(parse_qsl(query))
        l4 = {}
        for key in _NUMERIC_L4:
            if key in fields:
                try:
                    l4[key] = float(fields[key])
                except ValueError:
                    pass
        out["l4"] = l4
    out["server_ms"] = sum(out["durations_ms"].values()) if out["durations_ms"] else None
    return out


def _ns():
    return time.perf_counter_ns()


class _SharedFile:
    """One buffered reader for every response, so that pipelined bytes are never lost."""

    def __init__(self, fp):
        self._fp = fp

    def close(self):
        return None

    def __getattr__(self, name):
        return getattr(self._fp, name)


class _SocketShim:
    def __init__(self, fp):
        self._fp = _SharedFile(fp)

    def makefile(self, *args, **kwargs):
        return self._fp


class Link:
    def __init__(self, host, port=443, timeout=30.0, cafile=None):
        self.host = host
        self.port = int(port)
        self.timeout = float(timeout)
        self.context = ssl.create_default_context(cafile=cafile)
        self.sock = None
        self._shim = None
        self._open = False
        self.sent_bytes = 0
        self.received_bytes = 0
        self.requests = 0

    def open(self):
        started = _ns()
        infos = socket.getaddrinfo(self.host, self.port, type=socket.SOCK_STREAM)
        dns_ms = (_ns() - started) / 1e6
        family, socktype, proto, _, sockaddr = infos[0]
        raw = socket.socket(family, socktype, proto)
        raw.settimeout(self.timeout)
        started = _ns()
        raw.connect(sockaddr)
        tcp_ms = (_ns() - started) / 1e6
        raw.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        started = _ns()
        tls = self.context.wrap_socket(raw, server_hostname=self.host)
        tls_ms = (_ns() - started) / 1e6
        self.sock = tls
        self._shim = _SocketShim(tls.makefile("rb"))
        self._open = True
        return {
            "dns_ms": dns_ms,
            "tcp_connect_ms": tcp_ms,
            "tls_handshake_ms": tls_ms,
            "tls_version": tls.version(),
            "cipher": tls.cipher()[0] if tls.cipher() else None,
            "address_family": "ipv6" if family == socket.AF_INET6 else "ipv4",
        }

    def alive(self):
        return self._open and self.sock is not None

    def _request_bytes(self, method, path, body):
        lines = [
            "%s %s HTTP/1.1" % (method, path),
            "Host: %s" % self.host,
            "User-Agent: %s" % USER_AGENT,
            "Connection: keep-alive",
            "Accept-Encoding: identity",
        ]
        if body is not None:
            lines.append("Content-Type: application/octet-stream")
            lines.append("Content-Length: %d" % len(body))
        head = ("\r\n".join(lines) + "\r\n\r\n").encode("ascii")
        return head, (head + body if body is not None else head)

    def exchange(self, steps):
        """Write every request of steps back to back, then read the responses in order.

        steps is a list of (method, path, body). Returns the timing of the whole
        exchange and of each response.
        """
        payload = b""
        header_bytes = 0
        sent = 0
        for method, path, body in steps:
            head, data = self._request_bytes(method, path, body)
            payload += data
            header_bytes += len(head)
            sent += len(body) if body is not None else 0
        wall = time.time()
        started = _ns()
        self.sock.sendall(payload)
        responses = []
        for method, path, body in steps:
            response = http.client.HTTPResponse(self._shim, method=method)
            response.begin()
            data = response.read()
            timing = parse_server_timing(response.getheader("server-timing"))
            responses.append(
                {
                    "method": method,
                    "path": path.split("?")[0],
                    "status": response.status,
                    "done_ms": (_ns() - started) / 1e6,
                    "body_received": len(data),
                    "server_ms": timing["server_ms"] if timing else None,
                    "server_timing": timing,
                    "colo": response.getheader("cf-meta-colo"),
                }
            )
            if response.will_close:
                self._open = False
        elapsed = (_ns() - started) / 1e6
        received = sum(r["body_received"] for r in responses)
        self.requests += len(steps)
        self.sent_bytes += sent
        self.received_bytes += received
        server = [r["server_ms"] for r in responses]
        server_ms = sum(server) if all(v is not None for v in server) else None
        return {
            "start_unix": wall,
            "ms": elapsed,
            "first_response_ms": responses[0]["done_ms"],
            "requests": len(steps),
            "request_header_bytes": header_bytes,
            "body_sent": sent,
            "body_received": responses[-1]["body_received"],
            "statuses": [r["status"] for r in responses],
            "server_ms": server_ms,
            "network_ms": (elapsed - server_ms) if server_ms is not None else None,
            "responses": responses,
            "connection_kept": self._open,
        }

    def close(self):
        if self.sock is not None:
            try:
                self.sock.close()
            except OSError:
                pass
        self.sock = None
        self._open = False
