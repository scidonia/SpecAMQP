#!/usr/bin/env bash
#
# S3 contract: the specification and the reference agree on the exchange corpora.
#
#   tests/contracts/s3_exchanges.sh        # inside the `spec` shell
#
# The exchange corpora carry the connection lifecycle and the session layer as ordered steps: what a
# peer sends and receives, what each step's outcome must be, and the state it must leave behind. They
# are the largest evidence this repository has for those layers and, until this contract, nothing
# committed ran them — a slice found that while checking its own revert, and it is the kind of gap
# that stays invisible because a sweep run by hand always passes.
#
# Observable contract:
#
#   1. both executables build and each passes both corpora on its own;
#   2. every vector gets the same status from both — the corpus is the common ground, and neither
#      artefact is allowed a private expectation;
#   3. every *step* a vector expects to be refused carries the condition the vector pins, from both
#      artefacts. Agreement on that a step is refused is half the claim: a session can refuse an
#      attach for a handle in use and for an unattached handle, and a status-only comparison calls
#      those the same. Refusals are read per step, because an exchange vector states its expectation
#      on `steps[i].expect` — `expectError` is the whole-vector vocabulary of the value corpora, and
#      reading it here leaves the refusal set empty on a corpus that refuses.
#   4. the comparison is not vacuous: the corpora both admit and refuse, so a run that agreed by
#      admitting everything or refusing everything fails here rather than passing on an empty
#      comparison.
#
# Runs offline; writes only inside a temporary directory.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

die() { printf 's3_exchanges: FAIL: %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

readonly corpora=(
  "$root/vectors/slice.ndjson"
  "$root/vectors/generated-exchanges.ndjson"
)

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"
for corpus in "${corpora[@]}"; do
  [ -f "$corpus" ] || die "missing corpus: $corpus"
done

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

( cd "$root/lean" && LAKE_NO_CACHE=1 lake build amqp-ref amqp-spec ) >"$tmp/build.log" 2>&1 ||
  die "building the executables failed: $(grep -m1 -E '\.lean:[0-9]+:[0-9]+: error' "$tmp/build.log" || tail -3 "$tmp/build.log")"
note "both executables build from Lean"

run() { # exe corpus outfile
  local exe="$1" corpus="$2" out="$3"
  ( cd "$root/lean" && lake exe "$exe" "$corpus" ) >"$out" 2>"$out.err" ||
    die "$exe did not pass $(basename "$corpus"): $(tail -2 "$out.err")"
  grep -q "0 failure(s)" "$out.err" || die "$exe reported failures on $(basename "$corpus")"
}

for corpus in "${corpora[@]}"; do
  name="$(basename "$corpus" .ndjson)"
  run amqp-ref "$corpus" "$tmp/ref-$name.log"
  run amqp-spec "$corpus" "$tmp/spec-$name.log"
  python3 - "$tmp/ref-$name.log" "$tmp/spec-$name.log" "$name" "$corpus" <<'COMPARE' || exit 1
import json, pathlib, sys

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

# Refusals are stated per step in an exchange corpus, at the id the runner emits.
refusing, pinned = set(), {}
admitting = set()
for line in corpus.read_text().splitlines():
    if not line.strip():
        continue
    vector = json.loads(line)
    for index, step in enumerate(vector.get("steps") or [], 1):
        expect = (step or {}).get("expect") or {}
        ident = f"{vector['vector']}#{index}"
        if expect.get("status") == "refused":
            refusing.add(ident); pinned[ident] = expect.get("condition")
        elif expect.get("status") == "admitted":
            admitting.add(ident)

if not refusing:
    problems.append("the corpus contains no refused step, so the comparison cannot see a refusal at all")
if not admitting:
    problems.append("the corpus contains no admitted step, so the comparison cannot see an admission")

# The condition each refusal must name, checked against what each artefact reported. The condition is
# read out of the verdict's own detail, because the runner prints it in the sentence the corpus reads.
for ident in sorted(refusing & set(shared)):
    for label, verdict in (("reference", reference[ident]), ("specification", specification[ident])):
        detail = verdict.get("detail", "")
        want = pinned.get(ident)
        if not want:
            continue
        if want not in detail:
            problems.append(f"{ident}: {label} refused without naming {want} ({detail[:70]})")

if problems:
    for p in problems:
        print("problem: " + p)
    print(f"check FAILED: {len(problems)} problem(s) on the {name} corpus")
    sys.exit(1)
print(f"     {name}: {len(shared)} vector(s) agree in status, {len(refusing)} refused step(s) pinned, "
      f"{len(admitting)} admitted")
COMPARE
done

echo "s3_exchanges: PASS"
