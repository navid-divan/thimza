import datetime
import json
import os
import platform
import re
import shutil
import socket
import subprocess
import sys
import time


UTC = datetime.timezone.utc


def time_now():
    return datetime.datetime.now(tz=UTC)


def iso(ts=None):
    if ts is None:
        ts = time_now()
    return ts.strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def unix_now():
    return time.time()


def monotonic_ns():
    return time.perf_counter_ns()


def execute(name, *args, timeout=None):
    opts = [name]
    for arg in args:
        opts.append(str(arg))
    starttime = time_now()
    try:
        output = subprocess.run(
            opts, text=True, capture_output=True, timeout=timeout, check=False
        )
        returncode = output.returncode
        stdout = output.stdout
        stderr = output.stderr
    except subprocess.TimeoutExpired as exc:
        returncode = -1
        stdout = exc.stdout.decode("utf-8", "replace") if exc.stdout else ""
        stderr = "timeout after %s s" % timeout
    except FileNotFoundError:
        returncode = -2
        stdout = ""
        stderr = "executable not found: %s" % name
    endtime = time_now()
    return {
        "cmd": opts,
        "start": iso(starttime),
        "end": iso(endtime),
        "wall_s": (endtime - starttime).total_seconds(),
        "returncode": returncode,
        "stdout": stdout,
        "stderr": stderr,
    }


def which(name):
    return shutil.which(name)


def read_text(path, limit=200000):
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as handle:
            return handle.read(limit)
    except OSError:
        return None


def cpu_model():
    text = read_text("/proc/cpuinfo") or ""
    for pattern in (
        r"^model name\s*:\s*(.+)$",
        r"^Model\s*:\s*(.+)$",
        r"^Processor\s*:\s*(.+)$",
        r"^Hardware\s*:\s*(.+)$",
        r"^cpu model\s*:\s*(.+)$",
    ):
        match = re.search(pattern, text, re.MULTILINE)
        if match:
            return match.group(1).strip()
    device_tree = read_text("/proc/device-tree/model", limit=256)
    if device_tree:
        return device_tree.replace("\x00", "").strip()
    if which("lscpu"):
        result = execute("lscpu", timeout=10)
        match = re.search(r"^Model name:\s*(.+)$", result["stdout"], re.MULTILINE)
        if match:
            return match.group(1).strip()
    if platform.system() == "Darwin":
        result = execute("sysctl", "-n", "machdep.cpu.brand_string")
        if result["returncode"] == 0:
            return result["stdout"].strip()
    return platform.processor() or "unknown"


def mem_total_kb():
    text = read_text("/proc/meminfo") or ""
    match = re.search(r"^MemTotal:\s*(\d+) kB$", text, re.MULTILINE)
    if match:
        return int(match.group(1))
    return None


def load_average():
    try:
        return list(os.getloadavg())
    except (OSError, AttributeError):
        return None


def cpu_count():
    try:
        return len(os.sched_getaffinity(0))
    except AttributeError:
        return os.cpu_count()


def max_rss_kb():
    try:
        import resource

        value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    except (ImportError, OSError):
        return None
    if platform.system() == "Darwin":
        return int(value / 1024)
    return int(value)


def leotest_env():
    keys = [
        "LEOTEST_SERVER",
        "LEOTEST_JOBID",
        "LEOTEST_NODEID",
        "LEOTEST_SERVERIP",
        "LEOTEST_SERVER_NODEID",
    ]
    return {key: os.environ.get(key) for key in keys}


def is_server_mode():
    return os.environ.get("LEOTEST_SERVER", "0") == "1"


def server_ip_from_env():
    value = os.environ.get("LEOTEST_SERVERIP")
    if value in (None, "", "None"):
        return None
    return value


class JsonlWriter:
    def __init__(self, path):
        self.path = path
        self._handle = open(path, "a", encoding="utf-8")

    def write(self, record):
        self._handle.write(json.dumps(record, ensure_ascii=False, default=str))
        self._handle.write("\n")
        self._handle.flush()
        try:
            os.fsync(self._handle.fileno())
        except OSError:
            pass

    def close(self):
        try:
            self._handle.close()
        except OSError:
            pass


def write_json(path, obj):
    tmp = "%s.tmp" % path
    with open(tmp, "w", encoding="utf-8") as handle:
        json.dump(obj, handle, ensure_ascii=False, indent=2, default=str)
        handle.flush()
        try:
            os.fsync(handle.fileno())
        except OSError:
            pass
    os.replace(tmp, path)


def resolve_host(host):
    try:
        infos = socket.getaddrinfo(host, None, proto=socket.IPPROTO_TCP)
    except socket.gaierror as exc:
        return {"host": host, "error": str(exc), "addresses": []}
    addresses = sorted({info[4][0] for info in infos})
    return {"host": host, "addresses": addresses, "error": None}


def tcp_connect_time(host, port, timeout=10.0):
    try:
        infos = socket.getaddrinfo(host, port, proto=socket.IPPROTO_TCP)
    except socket.gaierror as exc:
        return {"ok": False, "error": str(exc), "connect_ms": None}
    family, socktype, proto, _, sockaddr = infos[0]
    sock = socket.socket(family, socktype, proto)
    sock.settimeout(timeout)
    start = monotonic_ns()
    try:
        sock.connect(sockaddr)
        elapsed = (monotonic_ns() - start) / 1e6
        return {"ok": True, "error": None, "connect_ms": elapsed, "peer": sockaddr[0]}
    except OSError as exc:
        return {"ok": False, "error": str(exc), "connect_ms": None}
    finally:
        try:
            sock.close()
        except OSError:
            pass


def python_info():
    return {
        "version": sys.version.split()[0],
        "implementation": platform.python_implementation(),
        "executable": sys.executable,
    }
