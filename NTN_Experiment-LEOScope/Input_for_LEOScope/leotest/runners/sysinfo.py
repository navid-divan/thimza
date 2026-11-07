import contextlib
import io
import os
import platform
import ssl

from leotest import provenance
from leotest.runner import LeotestRunner
from leotest.utils import (
    cpu_count,
    cpu_model,
    execute,
    iso,
    load_average,
    max_rss_kb,
    mem_total_kb,
    python_info,
    read_text,
    resolve_host,
    which,
)


def _captured(fn):
    buffer = io.StringIO()
    try:
        with contextlib.redirect_stdout(buffer):
            fn()
    except Exception as exc:
        return "unavailable: %s" % exc
    return buffer.getvalue()


def _cpu_flags():
    text = read_text("/proc/cpuinfo") or ""
    for line in text.splitlines():
        if line.startswith("flags") or line.startswith("Features"):
            return sorted(set(line.split(":", 1)[1].split()))
    return []


def _cgroup_limits():
    out = {}
    for name in ("memory.max", "cpu.max", "cpuset.cpus.effective"):
        value = read_text(os.path.join("/sys/fs/cgroup", name), limit=256)
        if value is not None:
            out[name] = value.strip()
    return out


def _cpufreq():
    base = "/sys/devices/system/cpu/cpu0/cpufreq"
    out = {}
    for name in ("scaling_governor", "scaling_cur_freq", "scaling_max_freq", "cpuinfo_max_freq"):
        value = read_text(os.path.join(base, name), limit=64)
        if value is not None:
            out[name] = value.strip()
    return out


def _thimza_parameters():
    from thimza.params import THIMZA
    from thimza.schemes.thimza_scheme import Thimza

    table = {}
    for level, P in THIMZA.items():
        entry = {k: (float(v) if isinstance(v, float) else v) for k, v in P.items()}
        scheme = Thimza(P, seed=1)
        scheme.keygen(2, 3)
        model = {}
        for t in (2, 16, 128, 1024):
            scheme.n_parties = t
            model[str(t)] = {k: round(v) for k, v in scheme.sizes(t).items()}
        entry["paper_size_model_bytes"] = model
        table[str(level)] = entry
    return table


class SysInfoClient(LeotestRunner):
    def __init__(self, testname, config=None, **kwargs):
        super().__init__(
            name=testname,
            title="Node, software stack and Thimza build profile",
            description="Captures the execution environment of the measurement node",
            config=config,
            **kwargs
        )

    def _numpy(self):
        try:
            import numpy as np
        except ImportError as exc:
            return {"available": False, "error": str(exc)}
        return {
            "available": True,
            "version": np.__version__,
            "runtime": _captured(np.show_runtime),
            "config": _captured(np.show_config),
        }

    def _start_test(self, artifact_name):
        targets = self.param("resolve", ["speed.cloudflare.com", "1.1.1.1", "8.8.8.8"])
        openssl_cli = which("openssl")
        report = {
            "collected_at": iso(),
            "hardware": {
                "cpu_model": cpu_model(),
                "cpu_count": cpu_count(),
                "mem_total_kb": mem_total_kb(),
                "load_average": load_average(),
                "max_rss_kb": max_rss_kb(),
                "machine": platform.machine(),
                "cpu_flags": _cpu_flags(),
                "cpufreq": _cpufreq(),
                "cgroup": _cgroup_limits(),
            },
            "kernel": {
                "uname": platform.uname()._asdict(),
                "os_release": read_text("/etc/os-release"),
                "tcp_congestion_control": (
                    read_text("/proc/sys/net/ipv4/tcp_congestion_control") or ""
                ).strip(),
            },
            "python": python_info(),
            "numpy": self._numpy(),
            "python_ssl": ssl.OPENSSL_VERSION,
            "openssl_cli": (
                execute("openssl", "version", timeout=20)["stdout"].strip()
                if openssl_cli
                else None
            ),
            "ping_binary": which("ping"),
            "thread_environment": {
                key: os.environ.get(key)
                for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS")
            },
            "leotest_env": {
                key: value for key, value in os.environ.items() if key.startswith("LEOTEST_")
            },
            "dns": [resolve_host(target) for target in targets],
            "provenance": provenance.report(),
            "thimza_parameters": _thimza_parameters(),
        }
        self.emit({"record": "sysinfo", "data": report})
        return report
