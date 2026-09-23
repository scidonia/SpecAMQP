#!/usr/bin/env python3
"""Off-gate timing evidence for the corpus instruments: `amqp-ref` and `amqp-spec`.

    python3 bench/run.py                                    # the committed workload set
    python3 bench/run.py --repetitions 2 --out /tmp/x.json  # a quick smoke run

Runs each built binary over the workload set in `bench/workloads.json`, discards a warm-up
execution, and records min/median/max wall time and peak RSS over the repetitions that
follow, together with the environment the numbers were taken in and the ratios the scaling
series imply. The record is written to `bench/results/<run set>-<date>.json`.

The binaries are run directly — `lean/.lake/build/bin/amqp-ref`, not `lake exe amqp-ref` —
because `lake`'s up-to-date check is overhead a measurement should not contain. Build them
first (`cd lean && lake build amqp-ref amqp-spec`); this script never builds anything and
never writes outside its `--out` path and a temporary directory.

This is off-gate evidence, and it must not become a gate.
---------------------------------------------------------
Nothing here asserts a duration, names a threshold, or fails on a ratio: a non-zero exit
means a binary did not run, and nothing else. A wall-clock threshold would report the
host's load as the code's behaviour, which is why this repository forbids a test from
reading a real clock. The output is for a human comparing two records.

What it measures, and what it does not
--------------------------------------
The subject is the Lean specification (`amqp-spec`) and the Lean reference implementation
(`amqp-ref`), both compiled natively by Lean's own C backend. That is not the artefact
whose performance matters downstream: a corpus will eventually be replayed against a Rust
port, and **nothing here transfers to it** — different language, allocator and runtime, and
a fixed cost per process that a long-lived service never pays. This file makes no
performance claim about any port, and none about the Lean artefacts beyond the shape of
the curve it records.

What the numbers are good for is three things, and only three:

  a) an accidental-complexity detector. An accumulator that appends to the end of a list,
     or a renderer that grows a string two characters at a time, is quadratic in the
     corpus size; this repository was bitten by exactly those two, and both were found by
     someone noticing rather than by measuring. The scaling series below is what makes the
     class visible: a linear implementation costs the same per vector at every size, a
     quadratic one costs twice as much per vector for twice the corpus;
  b) the corpus's cost, which is what decides how far the corpus can grow. The whole of
     `vectors/generated.ndjson` costs about 0.6 s per run, so a corpus ten times its size
     is still seconds rather than minutes — that is the budget the next thousand vectors
     are spent against;
  c) a reference baseline for a downstream differential harness, which can compare its own
     per-vector cost against a number taken from these same corpora.

How to read the ratios
----------------------
Twice the work costs twice the time when the implementation is linear and four times when
it is quadratic, so the ratio of times across a doubling is the discriminator. Two
corrections make that ratio honest here, and both are applied in what follows.

  - Each measurement contains the process's fixed cost — start, runtime init, reading the
    file, exiting — which the `startup-floor` workload measures on a zero-vector corpus.
    That cost is a fifth of a `generated-quarter` run, so a raw ratio is diluted towards 1
    even for a perfectly linear implementation. The runner therefore also reports the
    *marginal* cost per vector, `(t - floor) / vectors`, which is what the complexity
    question is actually about.
  - A prefix of a corpus is an equal-work step only if the corpus's mixture is uniform,
    and `vectors/generated.ndjson` is not: its first quarter holds 8.2 MB of the file's
    15.8 MB, so the `prefix` series moves volume and mixture together. The `growth` series
    repeats one fixed set of vectors instead, holding the mixture exactly constant while
    the volume doubles, and its work ratio is exact. Read the prefix series for what the
    corpus's own prefixes cost and the growth series for the complexity question.

Both series are reported and neither is scored: a marginal ratio near 1.00 is linear, near
2.00 is quadratic, and the numbers in between are what they are.

Reproduction and the environment block
--------------------------------------
Every run records what a re-runner needs to judge the numbers: CPU model and usable core
count, the load average before and after each workload, the `lean/lean-toolchain`
revision, the git commit and every dirty path, and the SHA-256 of each binary, each corpus
and this script. Repetitions are interleaved rather than taken workload by workload: each
round measures every workload once, so a host that drifts under load during the run moves
them all together and the ratios survive it — min/median/max are extremes within each
workload's own samples, and the load averages bracket the window those samples came from.
Each measurement also records the runner's own resident set at fork time,
`fork_parent_rss_kb`, because a forked child inherits its parent's resident pages into its
peak-RSS high-water mark: a parent holding 112 MB reports 112 MB for a binary whose own
peak is 84 MB. The runner stays thin so the peak it reports is the binary's, and that
field is what lets a reader check it. A run with the tree dirty still records the *binary*
hashes, which is the stronger provenance. Only `python3` (standard library) and `git` are
needed; the runner needs no Lean toolchain, because the binaries are already built.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent

# `amqp-ref`/`amqp-spec` end each run with this line on stderr; the warm-up run reads it
# to check that the corpus the binary saw is the corpus this runner cut.
VERDICT_SUMMARY = re.compile(r"(\d+) vector\(s\), (\d+) failure\(s\) in (.+)")


# --------------------------------------------------------------------------------------
# environment
# --------------------------------------------------------------------------------------


def load_average() -> list[float] | None:
    """The three /proc/loadavg numbers, or None where the kernel does not offer them."""
    try:
        with open("/proc/loadavg", encoding="ascii") as handle:
            return [float(field) for field in handle.read().split()[:3]]
    except (OSError, ValueError):
        return None


def cpu_model() -> str | None:
    """The CPU model as /proc/cpuinfo spells it, or None off Linux."""
    try:
        with open("/proc/cpuinfo", encoding="utf-8", errors="replace") as handle:
            for line in handle:
                if line.lower().startswith("model name"):
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return None


def total_memory_kb() -> int | None:
    """MemTotal from /proc/meminfo, in kB, so a peak RSS has something to sit against."""
    try:
        with open("/proc/meminfo", encoding="ascii") as handle:
            for line in handle:
                if line.startswith("MemTotal:"):
                    return int(line.split()[1])
    except (OSError, ValueError, IndexError):
        pass
    return None


def git_state() -> dict:
    """`git`'s answer for the tree this runner is standing in: commit, branch, dirty set."""

    def git(*args: str) -> str:
        done = subprocess.run(
            ["git", *args], cwd=ROOT, capture_output=True, text=True, check=False
        )
        if done.returncode != 0:
            raise SystemExit(f"bench: git {' '.join(args)} failed: {done.stderr.strip()}")
        return done.stdout

    dirty = sorted(
        line[3:] for line in git("status", "--porcelain").splitlines() if line.strip()
    )
    return {
        "commit": git("rev-parse", "HEAD").strip(),
        "branch": git("rev-parse", "--abbrev-ref", "HEAD").strip(),
        "dirty": bool(dirty),
        "dirty_paths": dirty,
        # The field a reader wants in a hurry: a dirty path under `bench/` is this
        # measurement's own scaffolding and says nothing about the binaries that ran.
        "dirty_outside_bench": any(not path.startswith("bench/") for path in dirty),
    }


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def parent_rss_kb() -> int | None:
    """This runner's own resident set.

    It is recorded with every measurement because a forked child inherits its parent's
    resident pages into its own peak-RSS high-water mark — measured on this machine, a
    parent holding 112 MB reports 112 MB for a binary whose own peak is 84 MB. So the
    runner stays thin (nothing the size of a corpus is ever held in it), and the number
    recorded here is what tells a reader the peak it sits beside is the binary's own.
    """
    try:
        with open("/proc/self/status", encoding="ascii") as handle:
            for line in handle:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1])
    except (OSError, ValueError, IndexError):
        pass
    return None


def count_lines(path: Path, nonblank: bool) -> int:
    """Line count, read line by line so that nothing the corpus's size is retained."""
    total = 0
    with path.open("rb") as handle:
        for line in handle:
            if not nonblank or line.strip():
                total += 1
    return total


def environment(manifest_path: Path) -> dict:
    toolchain = ROOT / "lean" / "lean-toolchain"
    usable = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count()
    return {
        "taken_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "cpu_model": cpu_model(),
        "usable_cores": usable,
        "reported_cores": os.cpu_count(),
        "load_average": load_average(),
        "memory_total_kb": total_memory_kb(),
        "kernel": platform.release(),
        "host": platform.node(),
        "python": platform.python_version(),
        "lean_toolchain": toolchain.read_text(encoding="utf-8").strip()
        if toolchain.exists()
        else None,
        "git": git_state(),
        "runner": {"path": "bench/run.py", "sha256": sha256(Path(__file__).resolve())},
        "manifest": {
            "path": str(manifest_path.relative_to(ROOT)),
            "sha256": sha256(manifest_path),
        },
    }


# --------------------------------------------------------------------------------------
# the measured runs
# --------------------------------------------------------------------------------------


def run_once(command: list[str], stderr_to: Path | None) -> tuple[float, int, int]:
    """Run `command` once, returning (wall seconds, peak RSS in kB, exit status).

    Wall time is taken around the process, and peak RSS from the child's own rusage via
    `os.wait4`, so the number is that process's high-water mark and not the machine's.
    stdout and stderr go to /dev/null: a measurement should not pay for a terminal, and
    the corpus's verdict lines are the contracts' business, not this file's.
    """
    started = time.monotonic_ns()
    with open(os.devnull, "wb") as sink:
        errors = open(stderr_to, "wb") if stderr_to is not None else open(os.devnull, "wb")
        try:
            process = subprocess.Popen(command, cwd=ROOT, stdout=sink, stderr=errors)
            _, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
        finally:
            errors.close()
    return (time.monotonic_ns() - started) / 1e9, usage.ru_maxrss, process.returncode


def slice_corpus(corpus: Path, fraction: float, repeat: int, scratch: Path,
                 identifier: str) -> tuple[Path, int, int]:
    """Materialise one workload's input: the first `ceil(fraction * lines)` lines, repeated.

    Returns (path, vectors, bytes). The vectors count is the non-empty line count, which
    is what the harness parses; whole lines are always kept, so a prefix is never a
    half-parsed vector. A whole-corpus workload is handed to the binary in place. The cut
    is written line by line rather than prepared in memory, for the reason `parent_rss_kb`
    gives: the runner's resident set has to stay small enough not to become the floor of
    the peak it reports.
    """
    total = count_lines(corpus, nonblank=False)
    kept = math.ceil(total * fraction)
    if kept == total and repeat == 1:
        return corpus, count_lines(corpus, nonblank=True), corpus.stat().st_size
    if kept == 0:
        destination = scratch / f"{identifier}.ndjson"
        destination.write_bytes(b"")
        return destination, 0, 0

    base = scratch / f"{identifier}.base"
    vectors = 0
    last = b""
    with corpus.open("rb") as source, base.open("wb") as cut:
        for _ in range(kept):
            last = source.readline()
            if not last:
                break
            cut.write(last)
            if last.strip():
                vectors += 1
        if last and not last.endswith(b"\n"):
            cut.write(b"\n")  # repeats must not glue the corpus's unterminated last line
    octets = base.stat().st_size

    destination = scratch / f"{identifier}.ndjson"
    with destination.open("wb") as payload:
        for _ in range(repeat):
            with base.open("rb") as source:
                shutil.copyfileobj(source, payload)
    base.unlink()
    return destination, vectors * repeat, octets * repeat


def warm_up(binary: Path, corpus: Path, vectors: int, scratch: Path, tag: str) -> None:
    """One discarded execution that also checks the binary ran the corpus this runner cut.

    Its stderr carries the vector count, which must match the count this runner recorded;
    a mismatch means the prefix and the corpus have drifted apart, and it is worth
    knowing that before seven measurements are taken over the wrong input.
    """
    report = scratch / f"{tag}.warmup.err"
    _, _, status = run_once([str(binary), str(corpus)], report)
    text = report.read_text(encoding="utf-8", errors="replace")
    if status != 0:
        raise SystemExit(f"bench: {tag}: the binary exited {status}: {text.strip()[:400]}")
    match = VERDICT_SUMMARY.search(text)
    if match is None:
        raise SystemExit(f"bench: {tag}: the binary printed no vector summary: {text.strip()[:400]}")
    seen, failures = int(match.group(1)), int(match.group(2))
    if failures:
        raise SystemExit(f"bench: {tag}: the binary reported {failures} failing vector(s)")
    if seen != vectors:
        raise SystemExit(
            f"bench: {tag}: the binary saw {seen} vectors but this runner cut {vectors}: "
            "the prefix and the corpus have drifted apart"
        )


def run_measured(binary: Path, corpus: Path, tag: str) -> tuple[float, int]:
    """One timed execution, with the exit status checked: a measured run must succeed."""
    wall, peak, status = run_once([str(binary), str(corpus)], None)
    if status != 0:
        raise SystemExit(f"bench: {tag}: a measured run exited {status}")
    return wall, peak


def summarise(values: list[float] | list[int], integral: bool = False) -> dict:
    """min/median/max over the measured runs, with every run kept beside them."""
    def round_to(value: float) -> float | int:
        return int(round(value)) if integral else round(value, 6)

    return {
        "runs": [round_to(value) for value in values],
        "min": round_to(min(values)),
        "median": round_to(statistics.median(values)),
        "max": round_to(max(values)),
    }


# --------------------------------------------------------------------------------------
# the scaling series
# --------------------------------------------------------------------------------------


def analyse(entries: list[dict], floor: dict, statistic: str) -> dict:
    """Points, marginal cost per vector, and the ratio across each step of a series.

    Linear costs the same per vector at every size, so `marginal_ratio` is 1.00 and the
    time ratio equals the work ratio; quadratic doubles the marginal and squares the time
    ratio. Nothing here is compared against a threshold; both numbers are reported.
    """
    floor_seconds = floor["wall_seconds"][statistic]
    points = []
    for entry in entries:
        seconds = entry["wall_seconds"][statistic]
        marginal = (seconds - floor_seconds) / entry["vectors"] if entry["vectors"] else None
        points.append(
            {
                "id": entry["id"],
                "vectors": entry["vectors"],
                "bytes": entry["bytes"],
                "seconds": seconds,
                "marginal_us_per_vector": None if marginal is None else round(marginal * 1e6, 3),
            }
        )
    steps = []
    for before, after in zip(points, points[1:]):
        step = {
            "from": before["id"],
            "to": after["id"],
            "work_ratio": round(after["vectors"] / before["vectors"], 4),
            "time_ratio": round(after["seconds"] / before["seconds"], 4),
        }
        if before["marginal_us_per_vector"] and after["marginal_us_per_vector"]:
            step["marginal_ratio"] = round(
                after["marginal_us_per_vector"] / before["marginal_us_per_vector"], 4
            )
        steps.append(step)
    return {"floor": floor["id"], "statistic": statistic, "points": points, "steps": steps}


# --------------------------------------------------------------------------------------
# report
# --------------------------------------------------------------------------------------


def marginal_text(point: dict) -> str:
    """A point's marginal cost per vector, or a placeholder where it is not defined."""
    value = point["marginal_us_per_vector"]
    return f"{value:>8.2f} us/vector" if value is not None else "         n/a"


def print_report(record: dict) -> None:
    env = record["environment"]
    load = env["load_average"]
    print("environment")
    print(f"  taken            {env['taken_utc']}")
    print(f"  cpu              {env['cpu_model']} ({env['usable_cores']} usable cores)")
    print(f"  memory           {env['memory_total_kb']} kB total")
    print(f"  load average     {' '.join(f'{x:.2f}' for x in load) if load else 'unavailable'}")
    print(f"  lean-toolchain   {env['lean_toolchain']}")
    state = "dirty" if env["git"]["dirty"] else "clean"
    print(f"  git              {env['git']['commit'][:12]} on {env['git']['branch']}, {state}"
          + (f", {len(env['git']['dirty_paths'])} dirty path(s)" if env["git"]["dirty"] else ""))
    print(f"  repetitions      {record['repetitions']} measured, {record['warmup']} warm-up discarded")
    print()

    for name, binary in record["binaries"].items():
        print(f"{name}  {binary['path']}  sha256 {binary['sha256'][:16]}")
        print("  workload                 vectors        bytes    min s    med s    max s"
              "  rss min/med/max kB  forked from kB")
        for entry in record["measurements"].values():
            if entry["executable"] != name:
                continue
            wall, rss = entry["wall_seconds"], entry["peak_rss_kb"]
            print(f"  {entry['id']:<24}{entry['vectors']:>7}{entry['bytes']:>13}"
                  f"{wall['min']:>9.3f}{wall['median']:>9.3f}{wall['max']:>9.3f}"
                  f"{rss['min']:>11}{rss['median']:>8}{rss['max']:>8}"
                  f"{entry['fork_parent_rss_kb']:>17}")
        print()

    print("scaling  (marginal cost per vector is measured against the startup floor;")
    print("          a linear implementation is 1.00 and a quadratic one 2.00. The min")
    print("          columns are the least contaminated by host load, the median columns")
    print("          what the host actually delivered during the run.)")
    for name in record["binaries"]:
        for series, analysis in record["scaling"][name].items():
            print(f"  {name} / {series}: {analysis['note']}")
            for slow, quick in zip(analysis["median"]["points"], analysis["min"]["points"]):
                print(f"    {slow['id']:<24}{slow['vectors']:>7} vectors{slow['bytes']:>13} bytes"
                      f"  min {quick['seconds']:>7.3f} s{marginal_text(quick)}"
                      f"   median {slow['seconds']:>7.3f} s{marginal_text(slow)}")
            for median_step, min_step in zip(analysis["median"]["steps"], analysis["min"]["steps"]):
                print(f"    {median_step['from']} -> {median_step['to']} "
                      f"(work x{median_step['work_ratio']:.2f})")
                print(f"      time      min x{min_step['time_ratio']:.2f}"
                      f"   median x{median_step['time_ratio']:.2f}")
                if "marginal_ratio" in median_step and "marginal_ratio" in min_step:
                    print(f"      marginal  min x{min_step['marginal_ratio']:.2f}"
                          f"   median x{median_step['marginal_ratio']:.2f}")
        print()
    print(f"record written to {record['record']['path']}")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--workloads", default=str(HERE / "workloads.json"),
                        help="the workload manifest (default: bench/workloads.json)")
    parser.add_argument("--out", default=None,
                        help="where to write the record (default: bench/results/<run set>-<date>.json)")
    parser.add_argument("--repetitions", type=int, default=None,
                        help="measured runs per workload, overriding the manifest")
    arguments = parser.parse_args(argv)

    manifest_path = Path(arguments.workloads).resolve()
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    repetitions = arguments.repetitions or manifest["repetitions"]
    warmup = manifest["warmup"]
    if repetitions < 5:
        print(f"bench: {repetitions} repetition(s) is below the five this evidence form "
              "asks for; the record will say so.", file=sys.stderr)

    binaries = {}
    for entry in manifest["executables"]:
        path = ROOT / entry["path"]
        if not path.is_file():
            raise SystemExit(f"bench: {path} is not built; run `cd lean && lake build {entry['name']}`")
        stat = path.stat()
        binaries[entry["name"]] = {
            "path": entry["path"],
            "root": entry.get("root"),
            "size_bytes": stat.st_size,
            "mtime_utc": datetime.fromtimestamp(stat.st_mtime, timezone.utc)
            .strftime("%Y-%m-%dT%H:%M:%SZ"),
            "sha256": sha256(path),
        }

    workloads = manifest["workloads"]
    floor_id = manifest["floor"]
    if floor_id not in {workload["id"] for workload in workloads}:
        raise SystemExit(f"bench: the manifest's floor {floor_id!r} names no workload")

    record = {
        "run_set": manifest["run_set"],
        "note": manifest["note"],
        "repetitions": repetitions,
        "warmup": warmup,
        "environment": environment(manifest_path),
        "binaries": binaries,
        "workloads": {},
        "measurements": {},
        "scaling": {},
    }

    with tempfile.TemporaryDirectory(prefix="specamqp-bench-") as scratch_name:
        scratch = Path(scratch_name)
        inputs = {}
        for workload in workloads:
            corpus = ROOT / workload["corpus"]
            if not corpus.is_file():
                raise SystemExit(f"bench: no such corpus: {corpus}")
            path, vectors, octets = slice_corpus(
                corpus, workload["prefix"], workload["repeat"], scratch, workload["id"]
            )
            inputs[workload["id"]] = (path, vectors, octets)
            record["workloads"][workload["id"]] = {
                "corpus": workload["corpus"],
                "prefix": workload["prefix"],
                "repeat": workload["repeat"],
                "note": workload["note"],
                "vectors": vectors,
                "bytes": octets,
                # Only a whole-corpus workload hashes its source file: a prefix is cut
                # here, and the corpus hash would not describe what the binary ran.
                "corpus_sha256": sha256(corpus) if workload["prefix"] == 1.0 else None,
            }

        for name in binaries:
            binary = ROOT / binaries[name]["path"]
            # Warm every workload first, so the same page-cache and runtime state is
            # behind each workload's samples, then interleave the measured rounds: every
            # workload is measured once per round, so a machine that drifts under load
            # during the run moves all of them together and the ratios survive it.
            for _ in range(warmup):
                for workload in workloads:
                    identifier = workload["id"]
                    path, vectors, _ = inputs[identifier]
                    warm_up(binary, path, vectors, scratch, f"{name}-{identifier}")

            samples: dict[str, list[tuple[float, int]]] = {w["id"]: [] for w in workloads}
            loads: dict[str, dict[str, list[float] | None]] = {}
            parent_peak = parent_rss_kb()
            for _ in range(repetitions):
                for workload in workloads:
                    identifier = workload["id"]
                    path, _, _ = inputs[identifier]
                    window = loads.setdefault(identifier, {"before": None, "after": None})
                    if window["before"] is None:
                        window["before"] = load_average()
                    wall, peak = run_measured(binary, path, f"{name}-{identifier}")
                    samples[identifier].append((wall, peak))
                    window["after"] = load_average()
                    observed = parent_rss_kb()
                    if observed is not None:
                        parent_peak = max(parent_peak or 0, observed)

            for workload in workloads:
                identifier = workload["id"]
                path, vectors, octets = inputs[identifier]
                times = [wall for wall, _ in samples[identifier]]
                peaks = [peak for _, peak in samples[identifier]]
                result = {
                    "executable": name,
                    "id": identifier,
                    "vectors": vectors,
                    "bytes": octets,
                    "wall_seconds": summarise(times),
                    "peak_rss_kb": summarise(peaks, integral=True),
                    "fork_parent_rss_kb": parent_peak,
                    "load_average_before": loads[identifier]["before"],
                    "load_average_after": loads[identifier]["after"],
                    "exit_status": 0,
                }
                record["measurements"][f"{name}/{identifier}"] = result
                wall, rss = result["wall_seconds"], result["peak_rss_kb"]
                print(f"  measured {name}/{identifier}: {vectors} vectors, "
                      f"min {wall['min']:.3f}s med {wall['median']:.3f}s max {wall['max']:.3f}s, "
                      f"peak RSS {rss['max']} kB", file=sys.stderr)

    for name in binaries:
        analysis = {}
        for series in manifest["series"]:
            entries = [record["measurements"][f"{name}/{identifier}"]
                       for identifier in series["workloads"]]
            floor = record["measurements"][f"{name}/{floor_id}"]
            analysis[series["name"]] = {
                "note": series["note"],
                "median": analyse(entries, floor, "median"),
                "min": analyse(entries, floor, "min"),
            }
        record["scaling"][name] = analysis

    if arguments.out:
        out = Path(arguments.out).resolve()
    else:
        stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        out = HERE / "results" / f"{manifest['run_set']}-{stamp}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    record["record"] = {
        "path": str(out.relative_to(ROOT)) if out.is_relative_to(ROOT) else str(out)
    }
    out.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print_report(record)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
