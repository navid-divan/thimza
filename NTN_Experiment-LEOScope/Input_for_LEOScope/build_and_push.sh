#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

DOCKERHUB_USER="${DOCKERHUB_USER:-}"
IMAGE_NAME="${IMAGE_NAME:-thimza-ntn}"
IMAGE_TAG="${IMAGE_TAG:-1.0.0}"
PLATFORMS="${PLATFORMS:-linux/amd64,linux/arm64}"

if [ -z "${DOCKERHUB_USER}" ]; then
  echo "set DOCKERHUB_USER first, for example: export DOCKERHUB_USER=anonymous" >&2
  exit 1
fi

if [ -d ../Code/thimza ]; then
  if ! diff -rq -x '__pycache__' -x '.DS_Store' ../Code/thimza thimza >/dev/null \
     || ! cmp -s ../Code/tests/test_thimza.py tests/test_thimza.py \
     || ! cmp -s ../Code/experiments/correctness_bound.py experiments/correctness_bound.py; then
    echo "the vendored Thimza code differs from ../Code; refresh it with:" >&2
    echo "  rsync -a --delete --exclude __pycache__ ../Code/thimza/ thimza/ && cp ../Code/tests/test_thimza.py tests/ && cp ../Code/experiments/correctness_bound.py experiments/" >&2
    exit 1
  fi
  echo "vendored Thimza code is identical to ../Code"
fi

IMAGE="${DOCKERHUB_USER}/${IMAGE_NAME}"
echo "building ${IMAGE}:${IMAGE_TAG} for ${PLATFORMS}"

docker buildx build \
  --platform "${PLATFORMS}" \
  --tag "${IMAGE}:${IMAGE_TAG}" \
  --tag "${IMAGE}:latest" \
  --provenance=false \
  --sbom=false \
  --push \
  .

echo "pushed ${IMAGE}:${IMAGE_TAG}"
echo "experiment-config.yml must carry: image: '${IMAGE}:${IMAGE_TAG}'"
