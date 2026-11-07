FROM python:3.12-slim-trixie

RUN apt-get update && apt-get install -y --no-install-recommends \
        openssl \
        ca-certificates \
        iputils-ping \
        libcap2-bin \
        procps \
    && setcap cap_net_raw+ep /usr/bin/ping \
    && rm -rf /var/lib/apt/lists/*

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    HOME=/tmp \
    OMP_NUM_THREADS=1 \
    OPENBLAS_NUM_THREADS=1 \
    MKL_NUM_THREADS=1

COPY requirements.txt /tmp/requirements.txt
RUN pip install --no-cache-dir -r /tmp/requirements.txt

WORKDIR /app
COPY thimza /app/thimza
COPY tests /app/tests
COPY experiments /app/experiments
COPY leotest /app/leotest

RUN python -m unittest tests.test_thimza \
    && python -m leotest.provenance \
    && openssl version \
    && chmod -R a+rX /app

ENTRYPOINT [ "python", "-m", "leotest", "--test-config", "/artifacts/experiment-config.yaml" ]
