#!/usr/bin/env bash
# R4: the wire differential's *state*, asserted per vector rather than read off a summary.
#
# `scripts/run-endpoint-wire-differential.sh` replays a corpus against the shipped endpoint over a socket and
# compares each step with `amqp-spec`'s in-process answer, through `scripts/endpoint/WireApp/` and its peer.
# The rung exists so that what the endpoint *claims* and what it *does* are compared at the wire at all, and
# its acceptance question is therefore not "does the run pass" — three of `vectors/slice.ndjson`'s six vectors
# diverge or are refused at the socket by construction, because the differential drives the endpoint through an
# application at a seam the shell reaches only after a read, and two of those steps are not the application's
# to play. Its acceptance question is **whether every divergence is one the run can name**.
#
# So what is asserted here is the rung's state, declared vector by vector:
#
#   * every vector in the corpus carries a verdict, and the agreeing and diverging sets are exactly the
#     declared ones — so a **regression** (a vector that agreed now diverging) and a **new divergence** both
#     fail here, rather than being absorbed into a count that moved;
#   * every divergence carries a structured cause drawn from the seam properties the tier's docstring names,
#     and **`unknown` is forbidden**: an unattributed divergence is the one thing this rung exists to catch,
#     and a run that cannot say why it diverged has measured the difference without explaining it;
#   * the tier's exit status agrees with its own report — non-zero exactly when the report holds a divergence.
#     A tier that exits zero while its report lists divergences, or non-zero with none, is inconsistent, and
#     the inconsistency is precisely what a reader of the summary would never see.
#
# The counts are deliberately not asserted as numbers: the declared *sets* are, and a count is a derived fact
# that would hide a swap between two vectors. The declared set is a planner-owned declaration — closing a seam
# or finding a new one is a reviewed change to this file, not a tolerance to widen. The tier's human output is
# not asserted at all: verdicts and cause labels are contract, sentences are not, which is the lesson
# `r2_endpoint_shell.sh` records at its own expense.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

die() { printf 'r4_wire_differential: FAIL: %s\n' "$1" >&2; exit 1; }

[ -f scripts/run-endpoint-wire-differential.sh ] || die "the tier is not in the tree"
[ -f vectors/slice.ndjson ] || die "the corpus is not in the tree"

report="$(mktemp)"
log="$(mktemp)"
trap 'rm -f "$report" "$log"' EXIT

# The tier exits non-zero when it reports a divergence, which is today's declared state, so the status is
# captured rather than allowed to abort: the assertion about it is made below, against the report.
status=0
bash scripts/run-endpoint-wire-differential.sh --report "$report" >"$log" 2>&1 || status=$?

[ -s "$report" ] || die "the tier wrote no report (exit $status): $(tail -5 "$log")"

R4_STATUS="$status" python3 - "$report" <<'PY' || exit 1
import json, os, pathlib, sys

corpus = "vectors/slice.ndjson"
# The declared state: every vector of `slice.ndjson`, and the cause each divergence is attributed to.
agree = {"slice-open-close-handshake", "slice-sasl-challenge-from-client", "slice-sasl-mechanisms-empty"}
diverge = {
    "slice-open-missing-container-id":          "app-seam-prompt-after-read",
    "slice-open-channel-max-wrong-type":        "app-seam-prompt-after-read",
    "slice-open-before-header":                 "app-seam-start-pre-state",
}
seams = set(diverge.values())

def die(msg):
    print(f"r4_wire_differential: FAIL: {msg}", file=sys.stderr); sys.exit(1)

doc = json.loads(pathlib.Path(sys.argv[1]).read_text())
if doc.get("corpus") != corpus:
    die(f"the report covers {doc.get('corpus')!r}, not {corpus!r}")

entries = doc.get("vectors") or []
seen = {}
for e in entries:
    name = e.get("vector")
    if not name:
        die(f"an entry carries no vector id: {e}")
    seen[name.split("#")[0]] = e

expected = agree | set(diverge)
if set(seen) != expected:
    missing, extra = expected - set(seen), set(seen) - expected
    die(f"the report's vector set is not the declared one — missing {sorted(missing)}, unexpected {sorted(extra)}")

status = int(os.environ.get("R4_STATUS", "0"))
found = []
for name, e in sorted(seen.items()):
    socket = (e.get("socket") or "")
    if socket == "INVALID":
        die(f"{name} never tested the endpoint (INVALID), so this run is not evidence — a listener that did "
            f"not bind or a port range exhausted, which is a different failure from a divergence")
    socket = socket.lower()
    if name in agree:
        if socket != "pass":
            die(f"{name} is declared to agree at the socket and the report says {socket!r}")
        continue
    found.append(name)
    if socket != "fail":
        die(f"{name} is declared to diverge at the socket and the report says {socket!r}")
    causes = {d.get("cause") for d in (e.get("divergences") or [])}
    if not causes:
        die(f"{name} diverges with no divergence recorded")
    if "unknown" in causes:
        die(f"{name} diverges for a cause the run cannot name, which is what this rung exists to catch")
    if not causes <= seams:
        die(f"{name} diverges with cause(s) {sorted(causes)}, which is not the declared seam set {sorted(seams)}")

if not found:
    die("no divergence was reported, so this run is not evidence: a tier that finds nothing is either fixed or not run")
if status == 0 and found:
    die(f"the tier exited zero while its report lists {len(found)} divergence(s)")
if status != 0 and not found:
    die(f"the tier exited {status} with no divergence in its report")

print(f"r4_wire_differential: PASS — {len(agree)} vector(s) agree and {len(found)} diverge, "
      f"every divergence attributed to a declared seam: {', '.join(sorted(found))}")
PY
