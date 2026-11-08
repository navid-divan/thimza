# $\textsf{Thimza}$ on a LEO Satellite Link: LEOScope Experiment

This directory containts the input and the output of our experiment that measures the
$\textsf{Thimza}$ threshold signature on a LEOScope node behind a Starlink terminal. It
covers the three $\textsf{Thimza}$ parameter sets (levels I, III and V, that is 128, 192
and 256 bit security, all with φ = 512 and q = 2^49 − 2^41 + 1). Each set is
measured both on the node's processor and across the satellite link.

| Folder | Content |
| --- | --- |
| `Input_for_LEOScope/` | the experiment container that was submitted to LEOScope: code, configuration and build scripts |
| `Output_of_LEOScope/` | the artifacts that LEOScope returned for the run of 5 November 2026 |

This artifact is anonymized review. The Docker image name
`anonymous/thimza-ntn:1.0.0` is anonymized, so build the image locally.

---

## 1. Input: `Input_for_LEOScope/`

| Path | Role |
| --- | --- |
| `Dockerfile`, `.dockerignore`, `requirements.txt` | image based on `python:3.12-slim-trixie` with NumPy 2.3.5 and PyYAML 6.0.3. It runs the unit tests while building and gives `ping` the `cap_net_raw` capability, so ICMP works for the non-root user that LEOScope runs it as |
| `experiment-config.yml` | the configuration pasted into the LEOScope form (the full plan) |
| `experiment-config.local.yml` | a short version of every stage, for local runs |
| `leotest/` | the measurement harness: entry point (`__main__.py`), scheduler (`harness.py`), stage base class (`runner.py`), one runner per stage in `runners/`, real wire encodings (`wire.py`), known answers (`kat.py`), statistics (`metrics.py`), link client (`netlink.py`) and code digests (`provenance.py`) |
| `thimza/`, `tests/test_thimza.py`, `experiments/correctness_bound.py` | byte-identical copies of the paper's reference implementation (in this tree, `GitHub/`). Nothing in `leotest/` changes the scheme |
| `analysis/summarize.py` | turns a run (a folder or the LEOScope `.zip`) into CSV tables |
| `check_config.py` | checks a configuration and prints its time budget and traffic volume |
| `build_and_push.sh` | builds the image for linux/amd64 and linux/arm64 and pushes it |
| `run_local.sh` | runs the experiment locally, in a container or in a virtual environment |

### Stages in Run

| Stage | Measures |
| --- | --- |
| `sysinfo` | processor, flags, frequency governor, cgroup limits, kernel, Python, NumPy and its SIMD dispatch, OpenSSL, DNS, the SHA-256 of every file of the code that runs, and the parameter table with our research's size model |
| `thimza_selftest` | correctness on the node: the 11 unit tests, exactness of the floating-point `mulmod`, the NTT against multiplication, honest (t, n) signing at all levels with rejection of a changed message and of a tampered response, the independent schoolbook verifier, round trips of every wire encoding, and known answers |
| `thimza_link` | live signing sessions in which every round of one signer crosses the satellite link, at all levels and t = 2, 16, 128, 1024. Sessions are interleaved and spread over the 15 s reconfiguration period of the constellation |
| `thimza_datagram` | ICMP echo with payloads equal to every Thimza object size, which shows which messages fit in one datagram on this path |
| `thimza_peer` | optional distributed session with a real coordinator and real peers on a LEOScope server node. It is skipped when no server node is given |
| `thimza_time` | time cost on the node: dealer key generation, the three rounds of one signer, the combiner and the verifier, at t = 2 … 1024 and all levels, with Threshold Raccoon as the baseline. Every sample is kept |
| `thimza_space` | space cost with real encodings: round messages, the request and openings that a signer receives, keys, the session token, and the sizes of real signatures, each compared with the paper's size model |

The link stage runs right after the self-test, so the measurements that only
the satellite link can give are taken first. Every stage has its own time budget
and never aborts the run, and every record is written as soon as it exists.

### Measurement Structure

- **Real bytes.** `leotest/wire.py` encodes the actual objects. Round messages
  and keys are fixed-width packings whose sizes match the paper's (80, 4,160 and
  12,544 bytes at level I). A signature carries the 32-byte challenge seed and
  Golomb–Rice codes of z and h, and every decoded signature is checked with the
  unmodified verifier.
- **One round trip per round.** A round of a signer is its message to the
  coordinator, followed by the coordinator's broadcast. Each round is one
  pipelined exchange over TLS 1.3 with Cloudflare's public speed test endpoint
  (`speed.cloudflare.com`): a POST that carries the encoded message, then a GET
  that returns exactly as many bytes as the broadcast. In round one that is the
  request V, in round two the t openings, and in round three the signature. The
  endpoint's processing time and TCP view come from its `Server-Timing` header,
  and every latency is reported raw and with that processing time removed.
- **Peers.** Up to t = 16, all signers run for real. Above that, peers are
  simulated as in the paper's benchmark: they return the commitment and opening
  of signer 1 under their own index, which costs signer 1 the same as t distinct
  peers. The signature delivered in round three is a valid signature for the
  same level and t, and it is verified on the node.
- **Both directions.** Before round three, a signer receives t openings. At
  t = 1024 that is 4.26 MB at level I, against 16.4 KiB sent, so both
  directions are measured.
- **Volume.** The full plan runs 231 signing sessions and moves about 5 MB up
  and 127 MB down, plus about 5 MB of ICMP. The node's own IP address is not
  recorded.

### Running 
Local smoke test, which writes to `Input_for_LEOScope/artifacts_local/`:
```bash
cd Input_for_LEOScope && ./run_local.sh container
```
```bash
cd Input_for_LEOScope && ./run_local.sh python
```
To check a configuration before you submit it:
```bash
cd Input_for_LEOScope && python3 check_config.py experiment-config.yml
```
To publish the image, set `DOCKERHUB_USER` to your registry account and put the
resulting image name into `experiment-config.yml`. On Apple Silicon, start
colima with Rosetta for the amd64 half
(`colima start --vm-type vz --vz-rosetta --cpu 6 --memory 10 --disk 60`).
```bash
cd Input_for_LEOScope && DOCKERHUB_USER=<account> ./build_and_push.sh
```
LEOScope form fields used for the run:
| Field | Value |
| --- | --- |
| Node | `starlink-london-ns2` (the image is multi-architecture, so any node can run it) |
| Docker image | the pushed image, e.g. `anonymous/thimza-ntn:1.0.0` |
| Experiment name | `thimza-ntn-london-<date>`: lower case, letters, digits and hyphens |
| CRON string, Triggers | empty (the job runs once) |
| Preferred start / end | start in UTC at least ten minutes ahead, end a couple of hours later |
| Duration of experiment | `1800` s (the 1,560 s budget plus margin, as printed by `check_config.py`) |
| Overhead experiment, Allow reschedule | unchecked |
| Experiment config file | the whole of `experiment-config.yml` |
| Server | empty, or a server node to enable `thimza_peer` |

---

## 2. Output: `Output_of_LEOScope/`

```
Output_of_LEOScope/
├── manifest.json            node before and after the run, plan, status and wall time of every stage
├── experiment-config.yaml   the configuration as the container read it
└── <stage>/                 one folder per stage
    ├── <stage>.jsonl        every record, one JSON object per line
    └── summary.json         the final record of the stage
```

Each `<stage>.jsonl` starts with a `runner_start` record that holds the stage
parameters. The measurement records follow, and the file ends with a
`runner_end` record that holds `status`, `error`, `start`, `end`, `wall_s` and
the stage `result`. `summary.json` is that last record.

### Details of Run

| | |
| --- | --- |
| Date | 2026-11-05, 09:52:13 to 10:02:30 UTC (617 s) |
| Node | `starlink-london-ns2`: Intel Core i7-1185G7 at 3.00 GHz, 8 cores, 32 GB, x86_64, Linux 7.0.0-27-generic |
| Software | Debian 13 container, CPython 3.12.16, NumPy 2.3.5, OpenSSL 3.5.7 |
| Endpoint | `speed.cloudflare.com`, served from Cloudflare's London (LHR) location |

| Stage | Status | Wall time |
| --- | --- | --- |
| `sysinfo` | ok | 0.2 s |
| `thimza_selftest` | ok, every required check passed and the known answers match | 6.3 s |
| `thimza_link` | ok, 231 of 231 sessions completed and every signature verified | 296.0 s |
| `thimza_datagram` | ok | 115.0 s |
| `thimza_peer` | skipped, since no server node was configured | 0.0 s |
| `thimza_time` | ok | 89.9 s |
| `thimza_space` | ok, every signature verified | 97.3 s |

### Main Results at t = 1024

| | Level I | Level III | Level V |
| --- | --- | --- | --- |
| Signer time on the node (ms, median) | 86.6 | 120.2 | 133.9 |
| Threshold Raccoon signer on the node (ms) | 187.9 | 272.4 | 294.9 |
| Speedup over Threshold Raccoon | 2.17× | 2.27× | 2.20× |
| Combiner / verifier (ms) | 10.4 / 3.0 | 14.6 / 4.2 | 16.0 / 4.5 |
| Bytes sent per signer | 16,784 | 24,760 | 28,768 |
| Bytes received per signer | 4,343,844 | 6,088,740 | 6,981,668 |
| Signature, compact median / paper model (B) | 12,735 / 13,152 | 18,936 / 19,568 | 21,639 / 22,272 |
| Signing session over the link (ms, median / p95) | 659 / 1,755 | 809 / 875 | 918 / 2,112 |
| Same session, network time only (ms, median) | 556 | 649 | 724 |
| Paper latency model / model that also counts received bytes (ms) | 404 / 522 | 438 / 574 | 444 / 626 |

- **Link.** The raw round trip time per exchange is 62 to 70 ms, or 33 to 39 ms
  once the endpoint's processing time is removed. At t = 1024, receiving the
  openings dominates the session, so the model that also counts received bytes
  tracks the measurement better than the send-only model.
- **Datagrams.** Payloads up to 1,472 B (1,500 B IP packets) were answered, with
  0 to 5 % loss and a median RTT of 25 to 34 ms, so the round one commitments
  (80 to 160 B) each fit in one datagram. Every larger object (keys, openings,
  responses and signatures, 3,872 B and up) got no reply in 20 tries.

To regenerate the full results, use the summariser. It writes `node.csv`,
`time.csv` (with the paper's Apple M2 numbers alongside), `space.csv`,
`link.csv`, `link_phase.csv`, `datagram.csv` and, when `thimza_peer` ran,
`peer.csv`:
```bash
python3 Input_for_LEOScope/analysis/summarize.py Output_of_LEOScope --out tables
```

---

## Notes

- The challenge seed is 32 bytes at every level, while the paper's size model
  counts 2λ bits. The wire format carries what the implementation uses, so on
  this account level III and V signatures are 16 and 32 bytes shorter than in
  the paper's model.
- The Gaussian sampler uses NumPy's `log` and `cos`, so signatures for a fixed
  seed may differ between processors in the last bit. The integer pipeline is
  exact, and its known answers must match everywhere, which the self-test
  enforces.
- The prototype is not constant time, and the timings are those of the
  reference Python implementation.
