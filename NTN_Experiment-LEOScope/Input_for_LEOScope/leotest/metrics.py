import math


def _sorted(values):
    return sorted(v for v in values if v is not None and not math.isnan(v))


def percentile(values, q):
    data = _sorted(values)
    if not data:
        return None
    if len(data) == 1:
        return data[0]
    pos = (len(data) - 1) * (q / 100.0)
    low = math.floor(pos)
    high = math.ceil(pos)
    if low == high:
        return data[int(pos)]
    return data[low] + (data[high] - data[low]) * (pos - low)


def mean(values):
    data = _sorted(values)
    if not data:
        return None
    return sum(data) / len(data)


def stdev(values):
    data = _sorted(values)
    if len(data) < 2:
        return None
    mu = sum(data) / len(data)
    return math.sqrt(sum((x - mu) ** 2 for x in data) / (len(data) - 1))


def median(values):
    return percentile(values, 50)


def summarize(values, unit=None):
    data = _sorted(values)
    if not data:
        return {"n": 0, "unit": unit}
    return {
        "n": len(data),
        "unit": unit,
        "min": data[0],
        "max": data[-1],
        "mean": mean(data),
        "median": median(data),
        "stdev": stdev(data),
        "p25": percentile(data, 25),
        "p75": percentile(data, 75),
        "p90": percentile(data, 90),
        "p95": percentile(data, 95),
        "p99": percentile(data, 99),
        "iqr": (percentile(data, 75) - percentile(data, 25)),
        "cv": (stdev(data) / mean(data)) if (mean(data) and stdev(data)) else None,
    }


def mean_absolute_successive_difference(values):
    data = [v for v in values if v is not None]
    if len(data) < 2:
        return None
    diffs = [abs(data[i + 1] - data[i]) for i in range(len(data) - 1)]
    return sum(diffs) / len(diffs)


def rfc3550_jitter(values):
    data = [v for v in values if v is not None]
    if len(data) < 2:
        return None
    jitter = 0.0
    for i in range(1, len(data)):
        jitter += (abs(data[i] - data[i - 1]) - jitter) / 16.0
    return jitter


def jitter_report(values):
    return {
        "masd": mean_absolute_successive_difference(values),
        "rfc3550": rfc3550_jitter(values),
        "stdev": stdev(values),
        "p95_minus_p50": (
            (percentile(values, 95) - percentile(values, 50))
            if percentile(values, 50) is not None
            else None
        ),
    }


def throughput_bps(num_bytes, seconds):
    if not seconds or seconds <= 0:
        return None
    return (num_bytes * 8.0) / seconds


def bin_by_phase(samples, key_time, key_value, period_s, num_bins):
    bins = [[] for _ in range(num_bins)]
    width = period_s / float(num_bins)
    for sample in samples:
        t = sample.get(key_time)
        v = sample.get(key_value)
        if t is None or v is None:
            continue
        phase = t % period_s
        index = min(int(phase / width), num_bins - 1)
        bins[index].append(v)
    out = []
    for index, values in enumerate(bins):
        out.append(
            {
                "bin": index,
                "phase_lo_s": index * width,
                "phase_hi_s": (index + 1) * width,
                "stats": summarize(values),
            }
        )
    return out
