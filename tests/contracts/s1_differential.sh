#!/usr/bin/env bash
#
# S1 contract: the specification and the reference implementation agree on the wire.
#
#   tests/contracts/s1_differential.sh        # inside the `spec` shell
#
# The two artefacts are independent: the reference implementation was written from
# the clauses and shares no definition with `Spec.*`. This contract runs both over
# both corpora through the same harness and compares verdicts vector by vector, so
# a disagreement is reported with the vector id and the two details rather than as
# a summary difference.
#
# Observable contract:
#
#   1. both executables exist and each passes both corpora on its own;
#   2. every vector gets the same status from both — the corpus is the common
#      ground, and neither artefact is allowed a private expectation;
#   3. the comparison is not vacuous: where the corpora contain a vector whose
#      bytes are deliberately wrong, both artefacts must reject it. If no vector
#      in the corpus exercises a rejection, this contract fails rather than
#      passing on an empty comparison.
#
# Runs offline; writes only inside a temporary directory.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly worked="$root/vectors/primitives.ndjson"
readonly generated="$root/vectors/generated.ndjson"
readonly disagreement="$root/vectors/constructor-disagreement.ndjson"

die() {
  printf 's1_differential: FAIL: %s\n' "$1" >&2
  exit 1
}

note() { printf 'ok   %s\n' "$1"; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"

( cd "$root/lean" && LAKE_NO_CACHE=1 lake build amqp-ref amqp-spec ) >"$tmp/build.log" 2>&1 ||
  die "building the executables failed: $(tail -3 "$tmp/build.log")"
note "both executables build from Lean"

run() { # exe corpus outfile
  local exe="$1" corpus="$2" out="$3"
  ( cd "$root/lean" && lake exe "$exe" "$corpus" ) >"$out" 2>"$out.err" ||
    die "$exe did not pass $(basename "$corpus"): $(tail -2 "$out.err")"
  grep -q "0 failure(s)" "$out.err" || die "$exe reported failures on $(basename "$corpus")"
}

for corpus in "$worked" "$generated" "$disagreement"; do
  case "$corpus" in
    "$worked") name=worked ;;
    *) name=generated ;;
  esac
  run amqp-ref "$corpus" "$tmp/ref-$name.log"
  run amqp-spec "$corpus" "$tmp/spec-$name.log"
  python3 - "$tmp/ref-$name.log" "$tmp/spec-$name.log" "$name" "$corpus" <<'PYCMP' || exit 1
import json, pathlib, sys

def verdicts(path):
    out = {}
    for line in pathlib.Path(path).read_text().splitlines():
        if line.strip():
            entry = json.loads(line)
            out[entry["vector"]] = entry
    return out

reference, specification, name = verdicts(sys.argv[1]), verdicts(sys.argv[2]), sys.argv[3]
problems = []
only_ref = set(reference) - set(specification)
only_spec = set(specification) - set(reference)
if only_ref or only_spec:
    problems.append(f"the two artefacts saw different vectors: {sorted(only_ref)[:4]} "
                    f"only in the reference, {sorted(only_spec)[:4]} only in the specification")
disagreements = [
    (ident, reference[ident]["status"], specification[ident]["status"],
     reference[ident]["detail"], specification[ident]["detail"])
    for ident in sorted(set(reference) & set(specification))
    if reference[ident]["status"] != specification[ident]["status"]
]
if disagreements:
    for ident, left, right, ldetail, rdetail in disagreements[:8]:
        problems.append(f"{ident}: reference {left} ({ldetail[:70]}) vs "
                        f"specification {right} ({rdetail[:70]})")
    problems.insert(0, f"{len(disagreements)} vector(s) where the artefacts disagree")

# Agreement on *that* a vector is refused is half the claim. Two artefacts can both
# refuse for different reasons — one because the encoding is truncated, the other
# because it exceeds a limit — and a status-only comparison calls that agreement.
# So every rejection must name its reason class as the leading token of the detail,
# both artefacts must name the same class, and where the vector pins `reason` both
# must match the pin. A refusal nobody can name is a failure, not a detail.
CLASSES = ("truncated", "unassigned", "unsupported", "sizeMismatch", "malformed", "limit")

def reason_class(entry):
    # Searched rather than split: a verdict that met its expectation reads "rejected, as the
    # vector expects: limit: …", so the class is not the first colon-separated field. Searching
    # for a known class name finds it in both the passing and the failing form.
    detail = entry.get("detail", "")
    for name in CLASSES:
        if name in detail:
            return name
    return None

entry_kind = {}
refusing = set()
pinned = {}
for line in pathlib.Path(sys.argv[4]).read_text().splitlines():
    if not line.strip():
        continue
    vector = json.loads(line)
    entry = vector.get("expectError") or {}
    entry_kind[vector["vector"]] = vector.get("kind", "")
    # A refusal is a rejection vector, or an encode vector asked to refuse: the second is how an
    # encode-direction refusal is expressed, and it carries no bytes because there is no expected
    # encoding when the encoder must say no.
    if vector.get("kind") == "reject" or (vector.get("kind") == "encode" and entry):
        refusing.add(vector["vector"])
    if vector.get("kind") == "reject" and entry.get("reason"):
        pinned[vector["vector"]] = entry["reason"]

pin_problems = []
for ident, expected in sorted(pinned.items()):
    for label, verdict in (("reference", reference.get(ident)),
                           ("specification", specification.get(ident))):
        if verdict is None:
            pin_problems.append(f"{ident}: {label} produced no verdict for a pinned vector")
        elif reason_class(verdict) != expected:
            pin_problems.append(
                f"{ident}: {label} reports {reason_class(verdict)} where the vector pins {expected}")
if pin_problems:
    problems.extend(pin_problems[:6])
    problems.insert(0, f"{len(pin_problems)} pinned reason(s) not matched")

reason_problems = []
for ident in sorted(set(reference) & set(specification)):
    left, right = reference[ident], specification[ident]
    # Keyed on the corpus kind, not on a verdict status. The harness reports `pass`/`fail` —
    # whether the *vector's* expectation was met — so the earlier status test never matched and
    # this check was inert: the pinned-reason check caught a wrong pin while two artefacts
    # disagreeing about *why* they refused went unnoticed.
    if ident not in refusing:
        continue
    lclass, rclass = reason_class(left), reason_class(right)
    if lclass is None or rclass is None:
        reason_problems.append(
            f"{ident}: a refusal must name a reason class ({', '.join(CLASSES)}); "
            f"reference says {left['detail'][:50]!r}, "
            f"specification says {right['detail'][:50]!r}")
    elif lclass != rclass:
        reason_problems.append(
            f"{ident}: refused for different reasons — reference {lclass}, specification {rclass}")
if reason_problems:
    problems.extend(reason_problems[:6])
    problems.insert(0, f"{len(reason_problems)} rejection(s) whose reason class does not agree")
for problem in problems:
    print(f"  differential: {problem}")
if problems:
    raise SystemExit(1)
print(f"     {name}: {len(reference)} vectors, identical verdicts from both artefacts")
PYCMP
  note "$name: verdicts identical across both artefacts"
done

# The comparison must have something to compare: rejections present in both runs,
# and vectors that both artefacts accepted, in each corpus.
python3 - "$tmp/ref-worked.log" "$tmp/ref-generated.log" <<'PYNONEMPTY' || exit 1
import json, pathlib, sys
problems = []
for path in sys.argv[1:]:
    verdicts = [json.loads(l) for l in pathlib.Path(path).read_text().splitlines() if l.strip()]
    kinds = {}
    for v in verdicts:
        kinds[v["kind"]] = kinds.get(v["kind"], 0) + 1
    # Non-vacuity, scaled to the corpus: a small worked-example corpus needs a couple
    # of rejections, the generated corpus must carry a substantial negative surface.
    # A fixed floor is wrong for either end — 8 is unreachable for 14 vectors, and
    # "any rejection at all" says nothing about a 67,124-vector corpus.
    floor = 2 if len(verdicts) < 100 else 100
    if kinds.get("reject", 0) < floor:
        problems.append(f"{pathlib.Path(path).name}: only {kinds.get('reject', 0)} rejection "
                        f"vectors, and this corpus must carry at least {floor}")
    if kinds.get("decode", 0) + kinds.get("encode", 0) < 4:
        problems.append(f"{pathlib.Path(path).name}: too few golden vectors to compare")
    if kinds.get("property", 0) + kinds.get("decode", 0) + kinds.get("encode", 0) < 10:
        problems.append(f"{pathlib.Path(path).name}: comparison too small to be meaningful")
for problem in problems:
    print(f"  differential: {problem}")
raise SystemExit(1 if problems else 0)
PYNONEMPTY
note "the comparison covers golden, rejection and property vectors"

# A control the committed corpus deliberately does not carry, because a 65,537-item
# JSON line is not worth committing: an *encode* request whose array exceeds the
# declared element limit, generated here and discarded with the temporary directory.
#
# It is an encode-direction refusal, which is the one thing the corpus vocabulary
# could not express until now — `kind: reject` is a decode expectation. An
# `expectError` on an encode vector means "the encoder must refuse this value", and
# the runner reports a pass when it does, so the ordinary verdict comparison covers
# it. This matters because the writer's domain has to sit inside what the reader
# accepts: a total reference encoder would emit 65,537 zero-width elements and then
# refuse to read its own output, which is the asymmetry this control exists to catch.
python3 - "$tmp/limit.ndjson" <<'PYLIMIT'
import json, sys

entry = {
    "vector": "generated-over-element-limit-encode",
    "kind": "encode",
    "clauses": ["amqp-core-types-v1.0-os.xml#amqp:types/section:encodings.1"],
    "value": {"type": "array", "constructor": "40", "items": [{"type": "null"}] * 65537},
    "expectError": {"condition": "amqp:decode-error", "reason": "limit",
                    "endpoint": "connection"},
    "note": "generated by the differential contract, never committed",
}
with open(sys.argv[1], "w") as handle:
    handle.write(json.dumps(entry, sort_keys=True) + "\n")
PYLIMIT

run amqp-ref "$tmp/limit.ndjson" "$tmp/ref-limit.log"
run amqp-spec "$tmp/limit.ndjson" "$tmp/spec-limit.log"
note "an encode request over the element limit is refused by both artefacts"

printf 's1_differential: PASS\n'
