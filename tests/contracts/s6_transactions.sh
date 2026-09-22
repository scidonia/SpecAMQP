#!/usr/bin/env bash
#
# S6 contract: the specification and the reference agree on the transaction family's wire.
#
#   tests/contracts/s6_transactions.sh        # inside the `spec` shell
#
# The transaction layer is Part 4's family, carried as a message body rather than as a frame
# performative, and reached only where a control link makes it present. The two artefacts are
# independent: the reference was written from the clauses and shares no definition with `Spec.*`.
# This contract runs both over both corpora through the same harness and compares verdicts
# vector by vector, because a summary difference hides which vector and which condition.
#
# Observable contract:
#
#   1. both executables build and each passes both corpora on its own;
#   2. every vector gets the same status from both — the corpus is the common ground;
#   3. every refusal names the condition its vector pins, from both artefacts. Agreement on
#      *that* a step is refused is half the claim: a coordinator can refuse a discharge for an
#      unknown id and a controller for an unset field, and a status-only comparison would call
#      those two the same. The conditions here are `amqp:illegal-state`,
#      `amqp:transaction:unknown-id` and `amqp:invalid-field`, each pinned by the vector;
#   4. the comparison is not vacuous: the negative corpus exercises refusals, and this contract
#      fails rather than passing on an empty comparison.
#
# Runs offline; writes only inside a temporary directory.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly positive="$root/vectors/txn.ndjson"
readonly negative="$root/vectors/txn-negative.ndjson"

die() { printf 's6_transactions: FAIL: %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"
for corpus in "$positive" "$negative"; do [ -f "$corpus" ] || die "missing corpus: $corpus"; done

( cd "$root/lean" && LAKE_NO_CACHE=1 lake build amqp-ref amqp-spec ) >"$tmp/build.log" 2>&1 ||
  die "building the executables failed: $(tail -3 "$tmp/build.log")"
note "both executables build from Lean"

run() { # exe corpus outfile
  local exe="$1" corpus="$2" out="$3"
  ( cd "$root/lean" && lake exe "$exe" "$corpus" ) >"$out" 2>"$out.err" ||
    die "$exe did not pass $(basename "$corpus"): $(tail -2 "$out.err")"
  grep -q "0 failure(s)" "$out.err" || die "$exe reported failures on $(basename "$corpus")"
}

for corpus in "$positive" "$negative"; do
  case "$corpus" in
    "$positive") name=positive ;;
    *) name=negative ;;
  esac
  run amqp-ref "$corpus" "$tmp/ref-$name.log"
  run amqp-spec "$corpus" "$tmp/spec-$name.log"
  python3 - "$tmp/ref-$name.log" "$tmp/spec-$name.log" "$name" "$corpus" <<'PYCMP' || exit 1
import json, pathlib, sys

CONDITIONS = ("amqp:illegal-state", "amqp:transaction:unknown-id", "amqp:invalid-field")

def verdicts(path):
    out = {}
    for line in pathlib.Path(path).read_text().splitlines():
        if line.strip():
            entry = json.loads(line)
            out[entry["vector"]] = entry
    return out

reference = verdicts(sys.argv[1]); specification = verdicts(sys.argv[2])
name = sys.argv[3]; corpus = pathlib.Path(sys.argv[4])
problems = []

only_ref = set(reference) - set(specification)
only_spec = set(specification) - set(reference)
if only_ref or only_spec:
    problems.append(f"the two artefacts saw different vectors: {sorted(only_ref)[:4]} only in the "
                    f"reference, {sorted(only_spec)[:4]} only in the specification")

shared = sorted(set(reference) & set(specification))
disagreements = [(i, reference[i]["status"], specification[i]["status"],
                  reference[i].get("detail", ""), specification[i].get("detail", ""))
                 for i in shared if reference[i]["status"] != specification[i]["status"]]
for ident, left, right, ldetail, rdetail in disagreements[:8]:
    problems.append(f"{ident}: reference {left} ({ldetail[:70]}) vs specification {right} ({rdetail[:70]})")
if disagreements:
    problems.insert(0, f"{len(disagreements)} vector(s) where the artefacts disagree on status")

# The condition, not just the status: a refusal nobody can name is a failure, and two
# artefacts refusing for different reasons have not agreed about anything.
refusing, pinned = set(), {}
for line in corpus.read_text().splitlines():
    if not line.strip():
        continue
    vector = json.loads(line)
    entry = vector.get("expectError") or {}
    if entry:
        refusing.add(vector["vector"]); pinned[vector["vector"]] = entry.get("condition")

if name == "negative" and not refusing:
    problems.append("the negative corpus contains no refusal, so this comparison proves nothing")

for ident in sorted(refusing & set(shared)):
    for label, verdict in (("reference", reference[ident]), ("specification", specification[ident])):
        detail = verdict.get("detail", "")
        named = [c for c in CONDITIONS if c in detail]
        if not named:
            problems.append(f"{ident}: {label} refused without naming a condition ({detail[:60]})")
        elif pinned.get(ident) and pinned[ident] not in named:
            problems.append(f"{ident}: {label} refused with {named[0]}, and the vector pins {pinned[ident]}")
    if reference[ident].get("detail", "") and specification[ident].get("detail", ""):
        left = [c for c in CONDITIONS if c in reference[ident]["detail"]]
        right = [c for c in CONDITIONS if c in specification[ident]["detail"]]
        if left and right and left[0] != right[0]:
            problems.append(f"{ident}: the artefacts refuse this step for different conditions "
                            f"({left[0]} against {right[0]})")

if problems:
    for p in problems: print("problem: " + p)
    print(f"check FAILED: {len(problems)} problem(s) on the {name} corpus")
    sys.exit(1)
print(f"{name}: {len(shared)} vector(s) agree in status and condition; {len(refusing)} refusal(s) pinned")
PYCMP
done
echo "s6_transactions: PASS"
