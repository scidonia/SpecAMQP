#!/usr/bin/env bash
#
# R1 contract: the transport shell's evidence, and the controls that make it evidence.
#
#   tests/contracts/r1_transport_shell.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. the clean loopback passes: exit status 0 and the runner's final line says so;
#   2. every control is invocable through the documented selector and behaves as
#      documented — for a *detecting* control, exit 0 means it was caught where the runner
#      claims, so a control that stops biting fails this gate rather than reporting success;
#   3. each control's reach is pinned per case, including where a case *cannot* detect it:
#      the empty dialogue under a reordering control has an eight-zero-octet header, and
#      swapping two of them is not a change, so three catches out of four is the documented
#      fact rather than a gap in the harness;
#   4. the short-write control is an *observation* rather than a detection, so what this
#      gate pins is the counts it forces — the multi case must carry the payload across
#      hundreds of `send` calls where the clean run makes one, which is what makes "the
#      Lean loop absorbs a partial accept" measured rather than asserted;
#   5. an unknown selector exits 2, so the control surface is closed rather than accepting
#      anything and silently running the clean path.
#
# Why this file exists, recorded because it is the reason a reviewer asked for it: the slice
# that built R1 reported its controls in prose — a comment saying the controls were run and
# observed failing — and a comment is not evidence a reader can re-derive. The selector and
# the runner are the coder's; this contract is what makes them reviewable, and it is the R1
# counterpart of the corpus gates' per-vector verdict comparison.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly runner="$root/scripts/run-transport-loopback.sh"

# The reach each control is expected to have, per case. A detecting control's number is the
# count of cases it must be *caught* in; the short-write control detects nothing because its
# documented outcome is that every case still passes, and it is pinned by its counts instead.
readonly detecting_controls=(truncating-recv:4 reordering-recv:3)

die() { printf 'r1_transport_shell: FAIL: %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

[ -f "$runner" ] || die "missing the runner: $runner"
command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

capture() { # label, then the runner's arguments
  local label="$1"; shift
  set +e
  ( cd "$root" && bash "$runner" "$@" ) >"$tmp/$label.log" 2>&1
  echo "$?" >"$tmp/$label.exit"
  set -e
}

capture clean
for entry in "${detecting_controls[@]}"; do
  capture "${entry%%:*}" --mutant "${entry%%:*}"
done
capture short-send --mutant short-send
capture bad-selector --mutant not-a-control

python3 - "$tmp" <<'PY' || exit 1
import pathlib, re, sys

tmp = pathlib.Path(sys.argv[1])
expected = {"truncating-recv": 4, "reordering-recv": 3}
problems = []


def read(label):
    log = (tmp / f"{label}.log").read_text()
    code = int((tmp / f"{label}.exit").read_text().strip())
    lines = [line for line in log.splitlines() if line.strip()]
    return code, lines, log


def check(condition, message):
    if not condition:
        problems.append(message)


code, lines, _ = read("clean")
check(code == 0, f"the clean run exited {code}, not 0")
check(lines and lines[-1] == "loopback: all cases passed",
      f"the clean run's final line is {lines[-1]!r} rather than 'loopback: all cases passed'")

for name, want in expected.items():
    code, lines, log = read(name)
    caught = len([l for l in lines if l.startswith("caught ")])
    escaped = len([l for l in lines if l.startswith("ESCAPED")])
    check(code == 0, f"{name}: the runner exited {code}, not 0")
    check(lines and lines[-1] == f"loopback: control {name} behaved as documented in every case",
          f"{name}: final line is {lines[-1]!r}")
    check(caught == want,
          f"{name}: caught in {caught} case(s), documented as {want} — a control whose reach moved "
          f"is a change to the harness and has to be re-documented rather than absorbed")
    check(escaped == 0, f"{name}: {escaped} case(s) reported ESCAPED")
# The empty case under a reordering control is asserted to pass, not excused: its header is
# eight zero octets, so there is nothing for the control to change.
code, lines, _ = read("reordering-recv")
empty = [l for l in lines if "case empty" in l]
check(empty and not any(l.startswith("caught ") for l in empty),
      "reordering-recv: the empty case is documented as unreachable by this control, so a "
      "caught line for it means the harness changed its claim without changing this contract")

code, lines, log = read("short-send")
check(code == 0, f"short-send: the runner exited {code}, not 0")
check(lines and lines[-1] == "loopback: control short-send behaved as documented in every case",
      f"short-send: final line is {lines[-1]!r}")
check(len([l for l in lines if l.startswith("ESCAPED")]) == 0, "short-send: a case reported ESCAPED")
counts = [int(m) for m in re.findall(r"in (\d+) send call\(s\)", log)]
check(counts and max(counts) >= 293,
      f"short-send: the largest send count is {max(counts) if counts else 0}, and the control is "
      f"documented as carrying the 300000-octet case across hundreds of calls")
check(len(counts) >= 2, "short-send: the two non-trivial cases' send counts were not both reported")

code, _, log = read("bad-selector")
check(code == 2, f"an unknown selector exited {code}, not 2")

if problems:
    for p in problems:
        print(f"problem: {p}", file=sys.stderr)
    print(f"check FAILED: {len(problems)} problem(s) in the transport shell's controls", file=sys.stderr)
    sys.exit(1)

print("     clean run passes; each control is caught where documented and cannot bite where not")
PY

note "the clean loopback passes, every control is invocable, and each one's reach is pinned"
echo "r1_transport_shell: PASS"
