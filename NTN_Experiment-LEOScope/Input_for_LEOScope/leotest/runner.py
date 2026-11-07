import logging
import os

from leotest.errors import RunnerError
from leotest.utils import JsonlWriter, iso, time_now, write_json


_logger = logging.getLogger(__name__)


class LeotestRunner:
    def __init__(
        self,
        name,
        title,
        description="",
        config=None,
        data_cb=None,
        location=None,
        network_type=None,
        connection_type=None,
        device_id=None,
    ):
        self.name = name
        self.title = title
        self.description = description
        self._config = config or {}
        self._data_cb = data_cb
        self._location = location
        self._network_type = network_type
        self._connection_type = connection_type
        self._device_id = device_id
        self.artifact_path = None
        self._stream = None
        self._deadline = None

    def params(self):
        return self._config.get("tests", {}).get(self.name, {})

    def param(self, key, default=None):
        return self.params().get(key, default)

    def set_deadline(self, deadline_monotonic):
        self._deadline = deadline_monotonic

    def budget_exhausted(self):
        if self._deadline is None:
            return False
        import time

        return time.monotonic() >= self._deadline

    def remaining_budget(self):
        if self._deadline is None:
            return None
        import time

        return max(0.0, self._deadline - time.monotonic())

    def write_raw_stdout(self, output, artifact_path, filename="raw_stdout.log"):
        raw_stdout = os.path.join(artifact_path, filename)
        with open(raw_stdout, "w", encoding="utf-8") as handle:
            handle.write(output if isinstance(output, str) else str(output))

    def emit(self, record):
        if self._stream is not None:
            self._stream.write(record)

    def artifact(self, filename):
        return os.path.join(self.artifact_path, filename)

    def _start_test(self, artifact_name):
        raise RunnerError(self.title, "No _start_test() function implemented.")

    def start_test(self):
        artifact_root = self._config.get("artifacts", {}).get("path_local", "/artifacts")
        self.artifact_path = os.path.join(artifact_root, self.name)
        if not os.path.exists(self.artifact_path):
            os.makedirs(self.artifact_path, exist_ok=True)
        self._stream = JsonlWriter(self.artifact(self.name + ".jsonl"))
        started = time_now()
        header = {
            "record": "runner_start",
            "test": self.name,
            "title": self.title,
            "start": iso(started),
            "params": self.params(),
        }
        self.emit(header)
        try:
            data = self._start_test(self.name)
            status = "ok"
            error = None
        except Exception as exc:
            data = None
            status = "error"
            error = "%s: %s" % (type(exc).__name__, exc)
            _logger.exception("runner %s failed", self.name)
        ended = time_now()
        summary = {
            "record": "runner_end",
            "test": self.name,
            "title": self.title,
            "status": status,
            "error": error,
            "start": iso(started),
            "end": iso(ended),
            "wall_s": (ended - started).total_seconds(),
            "node_id": self._device_id,
            "result": data,
        }
        self.emit(summary)
        write_json(self.artifact("summary.json"), summary)
        return summary

    def _stop_test(self):
        return None

    def stop_test(self):
        return self._stop_test()

    def _teardown(self):
        return None

    def teardown(self):
        result = self._teardown()
        if self._stream is not None:
            self._stream.close()
            self._stream = None
        return result
