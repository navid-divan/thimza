import sys

import yaml


REQUIRED_RUNNERS = {
    "sysinfo": "SysInfoClient",
    "thimza_selftest": "ThimzaSelfTestClient",
    "thimza_space": "ThimzaSpaceClient",
    "thimza_time": "ThimzaTimeClient",
    "thimza_datagram": "ThimzaDatagramClient",
    "thimza_link": "ThimzaLinkClient",
    "thimza_peer": "ThimzaPeerClient",
}

# Bytes of the Thimza objects per level, as measured by the codec of this package.
OBJECTS = {
    128: {"cmt": 80, "wbar": 4160, "z": 12544, "sig": 13152},
    192: {"cmt": 120, "wbar": 5824, "z": 18816, "sig": 19568},
    256: {"cmt": 160, "wbar": 6656, "z": 21952, "sig": 22272},
}


def link_volume(spec):
    sessions = spec.get("sessions") or {}
    msg = int(spec.get("message_bytes", 32))
    up = down = count = 0
    for level in spec.get("levels", [128, 192, 256]):
        o = OBJECTS[int(level)]
        for t in spec.get("thresholds", [2, 16, 128, 1024]):
            n = int(sessions.get(t, sessions.get("default", 10)))
            count += n
            up += n * (o["cmt"] + o["wbar"] + o["z"])
            request = 2 + msg + 2 + 2 * t + t * o["cmt"]
            down += n * (request + t * o["wbar"] + o["sig"])
    return count, up, down


def datagram_volume(spec):
    sizes = set(int(x) for x in spec.get("baseline_payload_bytes", [56, 1024, 1472]))
    for level in spec.get("levels", [128, 192, 256]):
        sizes.update(OBJECTS[int(level)].values())
    per_target = sum(sizes) * int(spec.get("count", 20))
    return len(sizes), 2 * per_target * len(spec.get("targets", ["8.8.8.8"]))


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "experiment-config.yml"
    with open(path, "r", encoding="utf-8") as handle:
        config = yaml.safe_load(handle)

    problems = []
    warnings = []

    image = (config.get("docker") or {}).get("image")
    if not image:
        problems.append("docker.image is missing")
    elif "DOCKERHUB_USERNAME" in str(image):
        problems.append("docker.image still contains the DOCKERHUB_USERNAME placeholder")
    name = ((config.get("docker") or {}).get("execute") or {}).get("name")
    if not name:
        problems.append("docker.execute.name is missing")

    cloud = config.get("cloud_config") or {}
    if "AZURE_BLOB_CONNECTION_STRING" in str(cloud.get("connection_string")):
        warnings.append(
            "cloud_config.connection_string is a placeholder; results come back "
            "through the LEOScope run archive"
        )

    tests = config.get("tests") or {}
    if not tests:
        problems.append("no tests defined")
    for test_name, spec in tests.items():
        runner = spec.get("runner")
        entry = spec.get("entry_point")
        if runner not in REQUIRED_RUNNERS:
            problems.append("test %s uses unknown runner %s" % (test_name, runner))
        elif entry != REQUIRED_RUNNERS[runner]:
            problems.append(
                "test %s should use entry_point %s for runner %s"
                % (test_name, REQUIRED_RUNNERS[runner], runner)
            )
        for level in spec.get("levels", []):
            if int(level) not in OBJECTS:
                problems.append("test %s names unknown level %s" % (test_name, level))

    if (config.get("artifacts") or {}).get("path_local") != "/artifacts":
        problems.append("artifacts.path_local must be /artifacts on the testbed")

    budget = float((config.get("schedule") or {}).get("budget_s", 0))
    if budget <= 0:
        problems.append("schedule.budget_s must be positive")

    print("config:   %s" % path)
    print("image:    %s" % image)
    print("tests:    %s" % ", ".join((config.get("schedule") or {}).get("order") or sorted(tests)))
    print("budget:   %.0f s" % budget)
    print("set the LEOScope 'Duration of Experiment (in seconds)' to %d" % int(budget + 240))
    for test_name, spec in tests.items():
        if spec.get("runner") == "thimza_link":
            count, up, down = link_volume(spec)
            print(
                "link:     %d signing sessions, %.1f MB up and %.1f MB down over the satellite link"
                % (count, up / 1e6, down / 1e6)
            )
        if spec.get("runner") == "thimza_datagram":
            sizes, volume = datagram_volume(spec)
            print("datagram: %d payload sizes, %.1f MB of ICMP traffic" % (sizes, volume / 1e6))
    for warning in warnings:
        print("warning:  %s" % warning)
    for problem in problems:
        print("problem:  %s" % problem)
    if problems:
        sys.exit(1)
    print("config looks ready to paste into the LEOScope form")


if __name__ == "__main__":
    main()
