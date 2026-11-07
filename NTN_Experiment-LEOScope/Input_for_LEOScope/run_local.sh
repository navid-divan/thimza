#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

MODE="${1:-container}"
CONFIG="${2:-experiment-config.local.yml}"

if [ "${MODE}" = "python" ]; then
  python3 -m venv .venv
  ./.venv/bin/pip install --quiet --upgrade pip
  ./.venv/bin/pip install --quiet -r requirements.txt
  mkdir -p artifacts_local
  ./.venv/bin/python -m leotest --test-config "${CONFIG}"
  exit 0
fi

docker build -t thimza-ntn:local .
rm -rf "$(pwd)/artifacts_local"
mkdir -p "$(pwd)/artifacts_local"
python3 - "${CONFIG}" "$(pwd)/artifacts_local/experiment-config.yaml" <<'PY'
import sys, yaml
with open(sys.argv[1]) as handle:
    config = yaml.safe_load(handle)
config.setdefault("artifacts", {})["path_local"] = "/artifacts"
with open(sys.argv[2], "w") as handle:
    yaml.safe_dump(config, handle, sort_keys=False)
PY

docker run --rm \
  --user "$(id -u)" \
  -e LEOTEST_SERVER=0 \
  -e LEOTEST_JOBID=local-job \
  -e LEOTEST_NODEID=local-node \
  -e LEOTEST_SERVERIP=None \
  -e LEOTEST_SERVER_NODEID=None \
  -v "$(pwd)/artifacts_local:/artifacts" \
  thimza-ntn:local

echo "artifacts written to $(pwd)/artifacts_local"
