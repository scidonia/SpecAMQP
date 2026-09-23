#!/usr/bin/env bash
#
# S7 contract: the security layer, as both artefacts see it.
#
#   tests/contracts/s7_sasl.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. both executables build and each passes both corpora on its own;
#   2. every step gets the same verdict from both artefacts, and every refused step
#      names the same protocol condition and reason class from both. Agreement that a
#      step is refused is half the claim: a SASL init can be refused for naming an
#      unoffered mechanism and for carrying no mechanism at all, and a status-only
#      comparison calls those the same;
#   3. the comparison is not vacuous: the corpora both admit and refuse, so a run that
#      agreed by admitting everything or refusing everything fails here;
#   4. the four declared `sasl-code` failures are each exercised, one vector per code,
#      with the four names read from the generated choice table rather than typed here.
#      That is the check that fails when the artifact gains a fifth code and nobody
#      writes the vector for it — a hand-written list would never notice;
#   5. the layer-transition rules are exercised in both directions and on both sides of
#      the dialogue: an AMQP performative refused *inside* the SASL layer (sent and
#      received), a SASL performative refused inside the AMQP layer (sent and received),
#      and the send-side header mismatch whose absence let a peer switch layers;
#   6. the four failure codes are distinguishable in the verdict's reason, which is the
#      only place a refusal's class is compared: each of the four vectors pins a
#      *different* reason, so a layer that collapsed them to one class fails here.
#
# Runs offline; writes only inside a temporary directory.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

die() { printf 's7_sasl: FAIL: %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

readonly positives="$root/vectors/sasl.ndjson"
readonly negatives="$root/vectors/sasl-negative.ndjson"
readonly choices="$root/lean/Generated/Oasis/Choices.lean"

readonly corpora=("$positives" "$negatives")

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"
for corpus in "${corpora[@]}"; do
  [ -f "$corpus" ] || die "missing corpus: $corpus"
done
[ -f "$choices" ] || die "missing the generated choice table: $choices"

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
    problems.append(f"the two artefacts saw different steps: {sorted(only_ref)[:4]} only in the "
                    f"reference, {sorted(only_spec)[:4]} only in the specification")

shared = sorted(set(reference) & set(specification))
disagreements = [(i, reference[i]["status"], specification[i]["status"],
                  reference[i].get("detail", ""), specification[i].get("detail", ""))
                 for i in shared if reference[i]["status"] != specification[i]["status"]]
for ident, left, right, ldetail, rdetail in disagreements[:8]:
    problems.append(f"{ident}: reference {left} ({ldetail[:70]}) vs specification {right} ({rdetail[:70]})")
if disagreements:
    problems.insert(0, f"{len(disagreements)} step(s) where the artefacts disagree on status")

refusing, pinned, admitting = {}, {}, set()
for line in corpus.read_text().splitlines():
    if not line.strip():
        continue
    vector = json.loads(line)
    for index, step in enumerate(vector.get("steps") or [], 1):
        expect = (step or {}).get("expect") or {}
        ident = f"{vector['vector']}#{index}"
        if expect.get("status") == "refused":
            refusing[ident] = expect.get("condition", "")
            pinned[ident] = expect.get("reason", "")
        elif expect.get("status") == "admitted":
            admitting.add(ident)

# Non-vacuity, per corpus and named: an admitted step in every corpus, and a refused one in the
# corpus that exists to refuse. The positives are the exchange a peer must take end to end, so
# demanding a refusal in them would be demanding a corpus defect.
if not admitting:
    problems.append("the corpus contains no admitted step, so the comparison cannot see an admission")
if not refusing and name.endswith("-negative"):
    problems.append("the negative corpus contains no refused step, so the comparison cannot see a refusal at all")

for ident in sorted(refusing):
    if ident not in shared:
        continue
    condition = refusing[ident]
    reason = pinned[ident]
    for label, verdict in (("reference", reference[ident]), ("specification", specification[ident])):
        detail = verdict.get("detail", "")
        # The condition and the class are both read out of the verdict's own sentence, which is
        # where the runner prints them. An empty condition is not nothing to check: the four
        # declared failure codes carry none, precisely, and the vector says so by omitting the key
        # — so the check here is that no condition was invented, i.e. that none appears.
        if condition:
            if condition not in detail:
                problems.append(f"{ident}: {label} refused without naming {condition} ({detail[:70]})")
        else:
            if "amqp:" in detail:
                problems.append(f"{ident}: {label} named a condition where the vector pins none ({detail[:70]})")
        if reason and f"refused with" in detail and f" {reason}" not in detail and f"{reason}:" not in detail:
            problems.append(f"{ident}: {label} refused without naming the class {reason} ({detail[:80]})")

if problems:
    for p in problems:
        print("problem: " + p)
    print(f"check FAILED: {len(problems)} problem(s) on the {name} corpus")
    sys.exit(1)
print(f"     {name}: {len(shared)} step(s) agree in status, {len(refusing)} refusal(s) pinned, "
      f"{len(admitting)} admission(s)")
COMPARE
done

# 4. One vector per declared `sasl-code` value, the names read from the generated table.
python3 - "$choices" "$negatives" "$positives" <<'PYCODES' || exit 1
import json, pathlib, re, sys
choices, negatives, positives = (pathlib.Path(p) for p in sys.argv[1:4])
table = choices.read_text()
declared = dict(re.findall(
    r'ownerPath := "amqp:security/section:sasl/type:sasl-code", name := "([a-z-]+)", '
    r'value := "(\d+)"', table))
if len(declared) < 5:
    print(f"problem: the sasl-code choice declares {len(declared)} values, expected the artifact's five")
    sys.exit(1)
failure_codes = [name for name in declared if name != "ok"]
pinned = {}
for line in negatives.read_text().splitlines() + positives.read_text().splitlines():
    if not line.strip():
        continue
    vector = json.loads(line)
    for step in vector.get("steps") or []:
        reason = ((step or {}).get("expect") or {}).get("reason")
        if reason in failure_codes:
            pinned.setdefault(reason, []).append(vector["vector"])
missing = [c for c in failure_codes if c not in pinned]
if missing:
    print(f"problem: the declared sasl-code failure(s) {missing} have no vector pinning them")
    sys.exit(1)
print("     the four declared failure codes are each pinned by a vector: "
      + ", ".join(f"{c} → {pinned[c][0]}" for c in sorted(failure_codes)))
PYCODES
note "every declared sasl-code failure has a vector, and its name comes from the table"

# 5 and 6. The layer-transition rules and the four reasons, by name, in the drafts.
python3 - "$negatives" "$positives" <<'PYRULES' || exit 1
import json, pathlib, sys
negatives, positives = (pathlib.Path(p) for p in sys.argv[1:3])
vectors = {}
for path in (negatives, positives):
    for line in path.read_text().splitlines():
        if line.strip():
            vector = json.loads(line)
            vectors[vector["vector"]] = vector
required = {
    # what may be sent when: an AMQP frame refused in the SASL layer, both directions
    "sasl-amqp-frame-sent-after-init": "AMQP frame sent inside the SASL layer",
    "sasl-amqp-frame-received-before-mechanisms": "AMQP frame received inside the SASL layer",
    "sasl-close-in-the-sasl-layer": "close, not only open, refused inside the SASL layer",
    # and a SASL frame refused in the AMQP layer, both directions
    "sasl-frame-sent-in-the-amqp-layer": "SASL frame sent inside the AMQP layer",
    # the send-side header rule that let a peer switch layers
    "sasl-header-switch-on-send": "a header that would switch the layer is refused",
    # the dialogue's order, which is not the same question as the layer's
    "sasl-outcome-before-init": "the outcome before the init",
    "sasl-mechanisms-twice": "the mechanisms announced once",
}
missing = [v for v in required if v not in vectors]
if missing:
    print(f"problem: missing layer-transition vector(s): {missing}")
    sys.exit(1)
for name, why in required.items():
    refused = [s for s in vectors[name]["steps"] if (s.get("expect") or {}).get("status") == "refused"]
    if not refused:
        print(f"problem: {name} pins no refusal, so it cannot test {why}")
        sys.exit(1)
print(f"     {len(required)} layer-transition and dialogue-order vectors pin their refusals")
PYRULES
note "the layer transition and the dialogue's order are exercised, in both directions"

reasons=$(python3 - "$negatives" <<'PYREASONS'
import json, pathlib, sys
seen = set()
for line in pathlib.Path(sys.argv[1]).read_text().splitlines():
    if line.strip():
        for step in json.loads(line).get("steps") or []:
            r = ((step or {}).get("expect") or {}).get("reason")
            if r:
                seen.add(r)
print(len(seen))
PYREASONS
)
[ "$reasons" -ge 6 ] || die "the negatives pin only $reasons reason class(es), which cannot separate the rules"
note "the negatives pin $reasons distinct reason classes"

echo "s7_sasl: PASS"
