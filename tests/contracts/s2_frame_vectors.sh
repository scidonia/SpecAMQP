#!/usr/bin/env bash
#
# S2 contract: the frame layer, as both artefacts see it.
#
#   tests/contracts/s2_frame_vectors.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. both executables build;
#   2. the frame corpora are well formed against `frame-vector.schema.json`: ids match
#      the pattern the schema declares, ids are unique, every cited clause or picture
#      exists in the ledger, and every declared SIZE equals that vector's octet count
#      — the check that has already caught two authoring errors, one of them a
#      hand-typed 21 against twenty octets and one a hand-typed SIZE on an encode
#      vector that a decode-only pass skipped;
#   3. each artefact passes both corpora on its own;
#   4. both artefacts agree vector by vector, and on the *reason class* of every
#      refusal, since agreement that something is refused is not agreement why;
#   5. the comparison is not vacuous: the corpora carry refusals, both artefacts refuse
#      them, and the extended-header vector is present — the one whose whole point is
#      that four ignored octets must not fail a frame;
#   6. a mutation control fires: perturbing the descriptor octet inside a golden
#      frame's performative must be refused by both artefacts, which is what catches a
#      codec that ignores the descriptor and reads the body as anonymous octets.
#
# Runs offline; writes only inside a temporary directory.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly positives="$root/vectors/frames.ndjson"
readonly negatives="$root/vectors/frames-negative.ndjson"
readonly schema="$root/tests/contracts/frame-vector.schema.json"
readonly ledger="$root/ledger/clauses.json"
readonly pictures="$root/ledger/pictures.json"

die() { printf 's2_frame_vectors: FAIL: %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"

( cd "$root/lean" && LAKE_NO_CACHE=1 lake build amqp-ref amqp-spec ) >"$tmp/build.log" 2>&1 ||
  die "building the executables failed: $(tail -3 "$tmp/build.log")"
note "both executables build from Lean"

for required in "$positives" "$negatives" "$schema" "$ledger" "$pictures"; do
  [ -f "$required" ] || die "missing $required"
done

# 2. Shape, ids, cited sources and the SIZE arithmetic. The schema is the authoring
#    contract; these are the checks that catch data drifting away from it, and every
#    one of them has been paid for at least once by a bug in this repository.
python3 - "$positives" "$negatives" "$schema" "$ledger" "$pictures" <<'PYSHAPE' || exit 1
import json, pathlib, re, sys

positives, negatives, schema_path, ledger_path, pictures_path = sys.argv[1:6]
schema = json.loads(pathlib.Path(schema_path).read_text())
id_pattern = re.compile(schema["properties"]["vector"]["pattern"])
kinds = set(schema["properties"]["kind"]["enum"])
reasons = set(schema["properties"]["expectError"]["properties"]["reason"]["enum"])
known = {entry["ref"] for entry in json.loads(pathlib.Path(ledger_path).read_text())["clauses"]}
known |= {entry["ref"] for entry in json.loads(pathlib.Path(pictures_path).read_text())["pictures"]}

problems: list[str] = []
summary = {}
for corpus in (positives, negatives):
    seen: set[str] = set()
    counts: dict[str, int] = {}
    for number, line in enumerate(pathlib.Path(corpus).read_text().splitlines(), 1):
        if not line.strip():
            continue
        entry = json.loads(line)
        ident = entry.get("vector", f"line {number}")
        where = f"{pathlib.Path(corpus).name}:{ident}"
        if not id_pattern.match(ident):
            problems.append(f"{where}: id breaks the schema's own pattern")
        if ident in seen:
            problems.append(f"{where}: duplicate vector id")
        seen.add(ident)
        counts[entry.get("kind", "?")] = counts.get(entry.get("kind", "?"), 0) + 1
        if entry.get("kind") not in kinds:
            problems.append(f"{where}: kind {entry.get('kind')!r} is not one of {sorted(kinds)}")
        for ref in entry.get("clauses", []):
            if ref not in known:
                problems.append(f"{where}: cites {ref}, which is not a clause or picture in the ledger")
        octets = len(entry["bytes"]) // 2
        frame = entry.get("frame")
        if frame and frame.get("size") is not None and frame["size"] != octets:
            problems.append(
                f"{where}: declares SIZE {frame['size']} and carries {octets} octets")
        if entry.get("kind") == "frame-reject":
            expected = entry.get("expectError") or {}
            if expected.get("reason") not in reasons:
                problems.append(f"{where}: pins reason {expected.get('reason')!r}, not a known class")
            if not str(expected.get("condition", "")).startswith("amqp:"):
                problems.append(f"{where}: pins no protocol condition")
    summary[pathlib.Path(corpus).name] = counts

if summary[pathlib.Path(positives).name].get("frame-decode", 0) < 3:
    problems.append("too few decoding vectors to compare")
if summary[pathlib.Path(negatives).name].get("frame-reject", 0) < 4:
    problems.append("too few refusals to compare")
if "frame-encode" not in summary[pathlib.Path(positives).name]:
    problems.append("no encoding vector: the write direction would be untested")

for problem in problems:
    print(f"  frame vectors: {problem}")
if problems:
    raise SystemExit(1)
counts = ", ".join(f"{name} {{{', '.join(f'{k}: {v}' for k, v in sorted(kinds.items()))}}}"
                   for name, kinds in sorted(summary.items()))
print(f"     {counts}")
PYSHAPE
note "both corpora are well formed, cite their sources, and declare the SIZE they carry"

# 3 and 4. Run both artefacts over both corpora and compare verdict by verdict.
for corpus in "$positives" "$negatives"; do
  name="$(basename "$corpus" .ndjson)"
  for exe in amqp-ref amqp-spec; do
    ( cd "$root/lean" && lake exe "$exe" "$corpus" ) >"$tmp/$exe-$name.log" 2>"$tmp/$exe-$name.err" ||
      die "$exe did not pass $name: $(tail -2 "$tmp/$exe-$name.err")"
    grep -q "0 failure(s)" "$tmp/$exe-$name.err" || die "$exe reported failures on $name"
  done
  python3 - "$tmp/amqp-ref-$name.log" "$tmp/amqp-spec-$name.log" "$name" "$corpus" <<'PYCMP' || exit 1
import json, pathlib, sys

CLASSES = ("truncated", "unassigned", "unsupported", "sizeMismatch", "malformed", "limit")

def verdicts(path):
    out = {}
    for line in pathlib.Path(path).read_text().splitlines():
        if line.strip().startswith("{"):
            entry = json.loads(line)
            out[entry["vector"]] = entry
    return out

def reason_class(entry):
    head = entry.get("detail", "").split(":", 1)[0].strip()
    return head if head in CLASSES else None

reference, specification, name, corpus = (verdicts(sys.argv[1]), verdicts(sys.argv[2]),
                                          sys.argv[3], sys.argv[4])
problems = []
missing = set(reference) ^ set(specification)
if missing:
    problems.append(f"{name}: the artefacts saw different vectors: {sorted(missing)[:4]}")
disagreements = [(ident, reference[ident]["status"], specification[ident]["status"])
                 for ident in sorted(set(reference) & set(specification))
                 if reference[ident]["status"] != specification[ident]["status"]]
for ident, left, right in disagreements[:8]:
    problems.append(f"{name}:{ident}: reference {left} vs specification {right}")
pinned = {}
for line in pathlib.Path(corpus).read_text().splitlines():
    if line.strip():
        entry = json.loads(line)
        if (entry.get("expectError") or {}).get("reason"):
            pinned[entry["vector"]] = entry["expectError"]["reason"]
for ident in sorted(set(reference) & set(specification)):
    left, right = reference[ident], specification[ident]
    if left["status"] != "reject":
        continue
    classes = (reason_class(left), reason_class(right))
    if None in classes:
        problems.append(f"{name}:{ident}: a refusal must name its class "
                        f"({left['detail'][:40]!r} / {right['detail'][:40]!r})")
    elif classes[0] != classes[1]:
        problems.append(f"{name}:{ident}: refused for different reasons: {classes[0]} vs {classes[1]}")
    elif ident in pinned and classes[0] != pinned[ident]:
        problems.append(f"{name}:{ident}: refused as {classes[0]} where the vector pins {pinned[ident]}")
for problem in problems:
    print(f"  frame differential: {problem}")
if problems:
    raise SystemExit(1)
print(f"     {name}: {len(reference)} vectors, identical verdicts and reason classes")
PYCMP
  note "$name: verdicts and reason classes identical across both artefacts"
done

# 5. Non-vacuity: the extended-header vector is present, because a codec that
#    validates the ignored octets passes every vector that has none.
python3 - "$positives" <<'PYNONVAC' || exit 1
import json, pathlib, sys
entries = [json.loads(l) for l in pathlib.Path(sys.argv[1]).read_text().splitlines() if l.strip()]
extended = [e for e in entries if e.get("frame", {}).get("extended")]
if not extended:
    print("  frame differential: no vector exercises the extended header, so nothing "
          "distinguishes ignoring it from rejecting it")
    raise SystemExit(1)
# An emptied extended header must not be what the vector is asserting: the octets must
# be non-empty and the frame must still decode.
for entry in extended:
    if len(entry["frame"]["extended"]) == 0:
        print(f"  frame differential: {entry['vector']} declares an empty extended header")
        raise SystemExit(1)
print(f"     {len(extended)} vector(s) exercise a non-empty extended header")
PYNONVAC
note "the extended header is exercised, not merely documented"

# 6. Mutation control: change the descriptor octet of a golden frame's performative to a
#    code no performative has. Clause `framing.3` requires the performative to be one of
#    those defined, so a descriptor naming none of them must be refused — and a codec
#    that skips the descriptor entirely is what this catches. Mutating it to *another
#    legal* performative is deliberately not the control: that frame is legal, so
#    accepting it is correct, and a control asserting a refusal there would be asserting
#    something the artifact does not say. The vector's committed bytes are untouched; the
#    mutation lives in the temporary directory and is never evidence.
python3 - "$positives" "$tmp/mutated.ndjson" <<'PYMUTATE'
import json, pathlib, sys

source = [json.loads(l) for l in pathlib.Path(sys.argv[1]).read_text().splitlines() if l.strip()]
golden = next(e for e in source if e["vector"] == "frame-open-empty-decode")
# The performative is the body's first octets: the descriptor prefix, then smallulong
# 0x53 and the descriptor code 0x10 for open. 0x7f is a code no performative has, and the
# body's length does not change.
body = golden["bytes"][16:]
assert body.startswith("005310"), body
mutated = golden["bytes"].replace("005310", "00537f", 1)
entry = dict(golden)
entry["vector"] = "mutated-descriptor-in-open-frame"
entry["kind"] = "frame-reject"
entry.pop("frame", None)
entry["bytes"] = mutated
entry["expectError"] = {"condition": "amqp:connection:framing-error", "reason": "unsupported",
                        "endpoint": "connection"}
entry["note"] = ("generated by the contract: the performative's descriptor octet names no "
                 "performative, which framing.3 forbids")
with open(sys.argv[2], "w") as handle:
    handle.write(json.dumps(entry, sort_keys=True) + "\n")
PYMUTATE

# The vector carries the pinned class, so the harness's own verdict is the check: it
# reports a pass only when the refusal happened *and* named that class. Reading the
# status alone would accept "the codec encoded it instead" as success, which is the
# mirror of measuring an exit status through a pipe.
for exe in amqp-ref amqp-spec; do
  # The harness exits non-zero when a vector fails, so the exit status is deliberately not
  # the check — the summary line is, and it is the one that also carries the class.
  ( cd "$root/lean" && lake exe "$exe" "$tmp/mutated.ndjson" ) >"$tmp/$exe-mut.log" 2>"$tmp/$exe-mut.err" || true
  grep -q "0 failure(s)" "$tmp/$exe-mut.err" ||
    die "$exe did not refuse a frame whose performative descriptor names none of the \
defined performatives, which framing.3 forbids: $(grep -o 'decoded .*' "$tmp/$exe-mut.log" | head -1 | cut -c1-120)"
done
printf '     the unassigned descriptor is refused, with its class, by both artefacts\n'

note "a perturbed descriptor octet is refused by both artefacts"

printf 's2_frame_vectors: PASS\n'
