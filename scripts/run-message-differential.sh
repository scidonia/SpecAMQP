#!/usr/bin/env bash
#
# The Part 3 differential: the specification and the reference implementation agree about
# messages, on the wire and about the error condition.
#
#   scripts/run-message-differential.sh              # inside the `spec` shell
#   scripts/run-message-differential.sh --keep        # leave the logs in place
#
# The two artefacts are independent: `lean/Ref/Message.lean` was written from the clauses
# and shares no definition with `lean/Spec/Message.lean`. This script runs both executables
# over the whole `vectors/message/` corpus and compares their verdicts vector by vector, so
# a disagreement is reported with the vector id, both details, and the condition each
# artefact named — rather than as a summary difference.
#
# Observable contract:
#
#   1. both executables build and each passes every vector in every corpus file on its own;
#   2. every vector gets the same status from both artefacts, and where a vector is a
#      refusal the two artefacts name the same error *condition* (the harness checks the
#      condition against the vector, so this is the cross-artefact reading of the same
#      clause rather than one artefact's private expectation);
#   3. the comparison is not vacuous: the corpus must contain vectors that are refused as
#      well as vectors that are admitted, and a corpus in which nothing is refused makes
#      this script fail rather than pass on an empty comparison.
#
# Runs offline; writes only inside a temporary directory unless --keep is given.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly corpus_dir="$root/vectors/message"
readonly corpora=(sections sections-negative messages messages-negative deliveries generated)

keep=false
[[ "${1:-}" == "--keep" ]] && keep=true

die() { printf 'FAIL %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"
for name in "${corpora[@]}"; do
  [[ -f "$corpus_dir/$name.ndjson" ]] || die "missing corpus file $corpus_dir/$name.ndjson"
done

tmp="$(mktemp -d)"
if $keep; then
  trap 'printf ' >/dev/null
  printf 'logs kept in %s\n' "$tmp"
else
  trap 'rm -rf "$tmp"' EXIT
fi

( cd "$root/lean" && LAKE_NO_CACHE=1 lake build amqp-spec amqp-ref ) >"$tmp/build.log" 2>&1 ||
  die "building the executables failed: $(tail -3 "$tmp/build.log")"
note "both executables build from Lean"

for name in "${corpora[@]}"; do
  for artefact in spec ref; do
    ( cd "$root/lean" && LAKE_NO_CACHE=1 lake exe "amqp-$artefact" "$corpus_dir/$name.ndjson" ) \
      >"$tmp/$artefact-$name.log" 2>"$tmp/$artefact-$name.err" ||
      die "amqp-$artefact did not pass $name.ndjson: $(tail -1 "$tmp/$artefact-$name.err")"
  done
  note "$name.ndjson: both artefacts pass every vector"
done

# The comparison. Both artefacts' verdicts are compared as (vector, status, condition), so a
# disagreement names the vector and both readings rather than a count, and a refusal is
# compared on the condition rather than on the prose each artefact writes.
python3 - "$tmp" "${corpora[@]}" <<'PYCOMPARE' || exit 1
import json, pathlib, sys

tmp = pathlib.Path(sys.argv[1])
corpora = sys.argv[2:]

def load(path):
    verdicts = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        entry = json.loads(line)
        verdicts[entry["vector"]] = entry
    return verdicts

problems = []
counts = {"pass": 0, "fail": 0}
for name in corpora:
    spec = load(tmp / f"spec-{name}.log")
    ref = load(tmp / f"ref-{name}.log")
    if not spec:
        problems.append(f"{name}: amqp-spec produced no verdicts")
        continue
    if set(spec) != set(ref):
        only_spec = sorted(set(spec) - set(ref))
        only_ref = sorted(set(ref) - set(spec))
        problems.append(
            f"{name}: the artefacts judged different vectors "
            f"(only specification: {only_spec[:4]}, only reference: {only_ref[:4]})")
    for vector in sorted(set(spec) & set(ref)):
        theirs, ours = spec[vector], ref[vector]
        counts[theirs["status"]] = counts.get(theirs["status"], 0) + 1
        if theirs["status"] != ours["status"]:
            problems.append(
                f"{name}: {vector}: specification says {theirs['status']} ({theirs['detail']}), "
                f"reference says {ours['status']} ({ours['detail']})")
            continue
        # A pass on a refusal vector carries the condition the artefact named, and the two
        # must name the same one; the harness already checked it against the vector, so a
        # difference here would mean the two artefacts agreed with the vector for different
        # reasons, which is the case this comparison exists to catch.
        if "refused" in theirs["detail"] and "refused" in ours["detail"]:
            spec_condition = theirs["detail"].split("refused with")[-1].split(" and ")[0].strip()
            ref_condition = ours["detail"].split("refused with")[-1].split(" and ")[0].strip()
            if spec_condition != ref_condition:
                problems.append(
                    f"{name}: {vector}: the artefacts refused under different conditions "
                    f"(specification {spec_condition}, reference {ref_condition})")

print(f"     verdicts compared: {counts.get('pass', 0)} pass, {counts.get('fail', 0)} fail")
for problem in problems:
    print(f"     {problem}", file=sys.stderr)
if problems:
    sys.exit(1)
PYCOMPARE

# Non-vacuity: the corpus must refuse something as well as admit something, or the
# comparison above would be comparing two artefacts' agreement about nothing.
python3 - "$corpus_dir" "${corpora[@]}" <<'PYVACUOUS' || exit 1
import json, pathlib, sys

directory = pathlib.Path(sys.argv[1])
names = sys.argv[2:]
refused = admitted = 0
negative_kinds = {"section-reject", "message-reject"}
for name in names:
    for line in (directory / f"{name}.ndjson").read_text().splitlines():
        if not line.strip():
            continue
        vector = json.loads(line)
        if vector["kind"] in negative_kinds:
            refused += 1
        else:
            admitted += 1
        if vector["kind"] == "delivery":
            for step in vector["steps"]:
                if step["expect"]["status"] == "refused":
                    refused += 1
                else:
                    admitted += 1
if refused == 0:
    print("     the corpus refuses nothing: the comparison is vacuous", file=sys.stderr)
    sys.exit(1)
if admitted == 0:
    print("     the corpus admits nothing: the comparison is vacuous", file=sys.stderr)
    sys.exit(1)
print(f"     one artefact's corpus: {admitted} admitted, {refused} refused expectation(s)")
PYVACUOUS
note "the corpus refuses as well as admits, so the comparison is not vacuous"

printf 'run-message-differential: PASS\n'
