#!/usr/bin/env bash
#
# S4 contract: the fragmentation family, which is the session layer's adequacy control.
#
#   tests/contracts/s4_flow.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. both executables build and each passes both corpora on its own;
#   2. every step gets the same verdict from both artefacts, and every refused step names the
#      same protocol condition and reason class from both;
#   3. the *family* is non-vacuous — it admits and it refuses — and the check is across the pair
#      rather than per file, because this family follows the layers' positive/negative split
#      (`frames`/`frames-negative`, `messages`/`messages-negative`) and a per-file check would
#      demand a refusal among the positives, which is a demand for a defect;
#   4. **the adequacy control the plan's acceptance line names**: every interior split point of
#      the message is exercised as a two-transfer framing. A family that fragmented at one point
#      would satisfy 1–3 and prove nothing about the rule, so the count is pinned here rather than
#      assumed from the generator;
#   5. the two negatives pin their conditions by name: a transfer offered after the message ended,
#      which must begin a new delivery and does not; and a fragment one octet past the announced
#      frame size, which the same split admits at the limit.
#
# Every step in this family is a `receive` step, and that is deliberate: the octets are the
# vector's and the readers are the two artefacts, so neither wrote the fragmentation it is read
# against. A `send` step would have the artefact produce the fragmentation and the family would be
# checking a writer against itself.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly positives="$root/vectors/flow.ndjson"
readonly negatives="$root/vectors/flow-negative.ndjson"
readonly corpora=("$positives" "$negatives")

# The documented reach of the family. `split` is one vector per interior boundary of the message,
# so its count is the message's length less one, and it is the number that says the family is
# adequate rather than merely green.
readonly documented_split_vectors=29
readonly documented_vectors=34

die() { printf 's4_flow: FAIL: %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

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
done

python3 - "$positives" "$negatives" "$tmp/ref-flow.log" "$tmp/spec-flow.log" \
  "$tmp/ref-flow-negative.log" "$tmp/spec-flow-negative.log" <<'COMPARE' || exit 1
import json, pathlib, sys

positives, negatives = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
logs = {
    ("reference", "flow"): pathlib.Path(sys.argv[3]),
    ("specification", "flow"): pathlib.Path(sys.argv[4]),
    ("reference", "flow-negative"): pathlib.Path(sys.argv[5]),
    ("specification", "flow-negative"): pathlib.Path(sys.argv[6]),
}
problems = []


def verdicts(path):
    out = {}
    for line in path.read_text().splitlines():
        if line.strip():
            entry = json.loads(line)
            out[entry["vector"]] = entry
    return out


seen = {side: {} for side in ("reference", "specification")}
corpora = {"flow": positives, "flow-negative": negatives}
for family, path in corpora.items():
    for side in seen:
        seen[side].update(verdicts(logs[(side, family)]))
    # Step-level agreement, both directions.
    ref, spec = verdicts(logs[("reference", family)]), verdicts(logs[("specification", family)])
    only_ref, only_spec = set(ref) - set(spec), set(spec) - set(ref)
    if only_ref or only_spec:
        problems.append(f"{family}: the two artefacts saw different steps "
                        f"({sorted(only_ref)[:4]} only in the reference, {sorted(only_spec)[:4]} only in the specification)")
    for ident in sorted(set(ref) & set(spec)):
        if ref[ident]["status"] != spec[ident]["status"]:
            problems.append(f"{family}: {ident} is {ref[ident]['status']} to the reference and "
                            f"{spec[ident]['status']} to the specification")

    # The refusals, checked against the vector's own expectation: the condition and the class are
    # read out of the verdict's sentence, which is where the runner prints them.
    admitting = refusing = 0
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        vector = json.loads(line)
        for index, step in enumerate(vector.get("steps") or [], 1):
            expect = (step or {}).get("expect") or {}
            ident = f"{vector['vector']}#{index}"
            if expect.get("status") == "admitted":
                admitting += 1
            elif expect.get("status") == "refused":
                refusing += 1
                condition, reason = expect.get("condition", ""), expect.get("reason", "")
                for side in ("reference", "specification"):
                    detail = seen[side].get(ident, {}).get("detail", "")
                    if condition and condition not in detail:
                        problems.append(f"{family}: {ident} refused by the {side} without naming "
                                        f"{condition} ({detail[:70]})")
                    if reason and f"{reason}:" not in detail:
                        problems.append(f"{family}: {ident} refused by the {side} without the "
                                        f"reason class {reason} ({detail[:70]})")
    globals().setdefault("counts", {})[family] = (admitting, refusing)

admitting = sum(a for a, _ in counts.values())
refusing = sum(r for _, r in counts.values())
# Family-level non-vacuity: across the pair, the family must both admit and refuse.
if admitting == 0:
    problems.append("the family contains no admitted step, so the comparison cannot see an admission")
if refusing == 0:
    problems.append("the family contains no refused step, so the comparison cannot see a refusal")

# The adequacy control, pinned: one vector per interior boundary of the message.
split = sum(1 for line in positives.read_text().splitlines() if line.strip()
            and json.loads(line)["vector"].startswith("flow-fragment-split-"))
if split != 29:
    problems.append(f"the family exercises {split} interior split point(s) rather than 29 — a family "
                    f"that fragments at one point satisfies every other clause and proves nothing "
                    f"about the rule")
total = sum(1 for line in positives.read_text().splitlines() if line.strip())
if total != 34:
    problems.append(f"the positive corpus holds {total} vectors rather than the documented 34")

if problems:
    for p in problems:
        print(f"problem: {p}", file=sys.stderr)
    print(f"check FAILED: {len(problems)} problem(s) in the fragmentation family", file=sys.stderr)
    sys.exit(1)

print(f"     {admitting} admission(s) and {refusing} refusal(s) across the family, "
      f"{split} interior split points, verdicts identical from both artefacts")
COMPARE

note "the family admits and refuses, every interior split point is exercised, and both artefacts agree"
echo "s4_flow: PASS"
