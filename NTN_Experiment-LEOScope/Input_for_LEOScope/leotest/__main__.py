import argparse
import importlib
import logging
import os
import sys
import time

import yaml

from leotest.utils import (
    cpu_count,
    cpu_model,
    iso,
    is_server_mode,
    leotest_env,
    load_average,
    mem_total_kb,
    python_info,
    time_now,
    write_json,
)


logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(name)s %(message)s",
    stream=sys.stdout,
)
_logger = logging.getLogger("leotest")


DEFAULT_ORDER = [
    "sysinfo",
    "thimza_selftest",
    "thimza_space",
    "thimza_time",
    "thimza_datagram",
    "thimza_link",
    "thimza_peer",
]

SERVER_RUNNERS = {"thimza_peer"}


def build_runner(testname, config):
    spec = config["tests"][testname]
    module = importlib.import_module("leotest.runners.%s" % spec["runner"])
    entry = getattr(module, spec["entry_point"])
    return entry(
        testname=testname,
        config=config,
        data_cb=None,
        location=None,
        network_type="leo-satellite",
        connection_type=None,
        device_id=os.environ.get("LEOTEST_NODEID"),
    )


def order_tests(config):
    names = list(config.get("tests", {}).keys())
    if is_server_mode():
        return [n for n in names if config["tests"][n].get("runner") in SERVER_RUNNERS]
    explicit = config.get("schedule", {}).get("order")
    if explicit:
        ordered = [n for n in explicit if n in names]
        ordered += [n for n in names if n not in ordered]
        return ordered
    ranked = []
    for name in names:
        runner = config["tests"][name].get("runner", "")
        rank = DEFAULT_ORDER.index(runner) if runner in DEFAULT_ORDER else len(DEFAULT_ORDER)
        ranked.append((rank, name))
    ranked.sort()
    return [name for _, name in ranked]


def node_profile():
    return {
        "collected_at": iso(),
        "cpu_model": cpu_model(),
        "cpu_count": cpu_count(),
        "mem_total_kb": mem_total_kb(),
        "load_average": load_average(),
        "python": python_info(),
        "env": leotest_env(),
        "server_mode": is_server_mode(),
    }


def main():
    parser = argparse.ArgumentParser(description="LEOScope experiment: Thimza on a LEO link")
    parser.add_argument("--test-config", type=str, default="", metavar="PATH")
    args = parser.parse_args()

    with open(args.test_config, "r", encoding="utf-8") as stream:
        config = yaml.safe_load(stream)

    artifact_root = config.get("artifacts", {}).get("path_local", "/artifacts")
    os.makedirs(artifact_root, exist_ok=True)

    schedule = config.get("schedule", {}) or {}
    budget_s = float(schedule.get("budget_s", 1500))
    inter_test_sleep_s = float(schedule.get("inter_test_sleep_s", 2))
    reserve_s = float(schedule.get("reserve_s", 20))

    run_start_wall = time_now()
    run_start_mono = time.monotonic()
    hard_deadline = run_start_mono + budget_s

    names = order_tests(config)
    manifest = {
        "experiment": config.get("experiment", {}),
        "start": iso(run_start_wall),
        "budget_s": budget_s,
        "tests_planned": names,
        "node": node_profile(),
    }
    write_json(os.path.join(artifact_root, "manifest.json"), manifest)
    _logger.info("planned tests: %s", names)

    results = []
    for index, name in enumerate(names):
        remaining = hard_deadline - time.monotonic()
        if remaining <= reserve_s:
            _logger.warning("time budget exhausted, skipping %s", name)
            results.append({"test": name, "status": "skipped", "error": "time budget"})
            continue
        _logger.info("starting %s (%.1f s remaining)", name, remaining)
        try:
            runner = build_runner(name, config)
        except Exception as exc:
            _logger.exception("could not construct runner for %s", name)
            results.append(
                {"test": name, "status": "error", "error": "construct: %s" % exc}
            )
            continue
        share = config["tests"][name].get("budget_s")
        if share and not is_server_mode():
            runner.set_deadline(time.monotonic() + min(float(share), remaining - reserve_s))
        else:
            runner.set_deadline(hard_deadline - reserve_s)
        summary = runner.start_test()
        runner.stop_test()
        runner.teardown()
        results.append(
            {
                "test": name,
                "status": summary.get("status"),
                "error": summary.get("error"),
                "wall_s": summary.get("wall_s"),
            }
        )
        _logger.info("finished %s status=%s", name, summary.get("status"))
        if index < len(names) - 1 and inter_test_sleep_s > 0:
            time.sleep(min(inter_test_sleep_s, max(0.0, hard_deadline - time.monotonic())))

    run_end_wall = time_now()
    final = dict(manifest)
    final.update(
        {
            "end": iso(run_end_wall),
            "wall_s": (run_end_wall - run_start_wall).total_seconds(),
            "results": results,
            "node_after": node_profile(),
        }
    )
    write_json(os.path.join(artifact_root, "manifest.json"), final)
    _logger.info("experiment complete: %s", results)


if __name__ == "__main__":
    main()
