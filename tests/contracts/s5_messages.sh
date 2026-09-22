#!/usr/bin/env bash
#
# S5 contract: the message layer's differential, and the observable it reports.
#
#   tests/contracts/s5_messages.sh        # inside the `spec` shell
#
# The message layer decides what a transfer's payload means. Its corpus is the common ground
# between the specification and the independently written reference, and the differential runs
# both artefacts over every vector and compares verdicts — status, and the condition each
# refusal names. A refusal nobody can name is not agreement, so the comparison is not only of
# whether a step was refused.
#
# Observable contract:
#
#   1. the driver runs to completion and reports PASS on its own terms;
#   2. the comparison is not vacuous: the corpus both admits and refuses, so a run that agreed
#      by admitting everything or refusing everything fails here;
#   3. zero failing verdicts and zero disagreements, read from the driver's counts rather than
#      inferred from its summary line;
#   4. every vector matches its branch of tests/contracts/message-vector.schema.json: one kind
#      per branch, the branch's required fields present, no field the branch does not name.
#
# Runs offline; writes only inside a temporary directory.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

die() { printf 's5_messages: FAIL: %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

readonly driver="$root/scripts/run-message-differential.sh"
readonly schema="$root/tests/contracts/message-vector.schema.json"
[ -f "$driver" ] || die "the differential driver is missing: $driver"
[ -f "$schema" ] || die "the vector schema is missing: $schema"

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

nix --extra-experimental-features 'nix-command flakes' develop --offline --no-update-lock-file .#spec \
  --command bash "$driver" >"$tmp/diff.log" 2>&1 ||
  die "the differential driver failed: $(tail -4 "$tmp/diff.log" | tr '\n' ' ')"
grep -q 'run-message-differential: PASS' "$tmp/diff.log" ||
  die "the driver did not report PASS: $(tail -4 "$tmp/diff.log" | tr '\n' ' ')"
note "the differential driver reports PASS"

python3 - "$tmp/diff.log" <<'CHECKDELTA' || exit 1
import re, sys
log = open(sys.argv[1]).read()
problems = []
compared = re.search(r'verdicts compared:\s*(\d+)\s*pass,\s*(\d+)\s*fail', log)
if not compared:
    problems.append("the driver's comparison line is absent, so its counts cannot be read")
else:
    passed, failed = int(compared.group(1)), int(compared.group(2))
    if failed:
        problems.append(f"{failed} verdict(s) failed, of {passed + failed}")
    if passed < 100:
        problems.append(f"only {passed} verdicts compared, which is too few to be this corpus")
    print(f"     {passed} verdicts agree, {failed} fail")
admitted = re.search(r'(\d+)\s*admitted,\s*(\d+)\s*refused', log)
if not admitted:
    problems.append("the admitted/refused split is absent, so non-vacuity is unverified")
else:
    a, r = int(admitted.group(1)), int(admitted.group(2))
    if not a or not r:
        problems.append(f"the corpus admits {a} and refuses {r}: one being zero makes the comparison vacuous")
    print(f"     {a} admitted, {r} refused")
if problems:
    for p in problems:
        print("problem: " + p)
    print(f"check FAILED: {len(problems)} problem(s)")
    sys.exit(1)
print("the comparison is non-vacuous and every verdict agrees")
CHECKDELTA

# Structural validation rather than a schema library: the pinned shell has no `jsonschema`, and a
# contract that needs one installed fails for a reason that is not the corpus's. This checks what
# the schema states — one branch per kind, the branch's required fields present, no field the
# branch does not name — which is the part a reader would check by hand anyway.
python3 - "$schema" <<'CHECKSCHEMA' || exit 1
import json, pathlib, sys
schema = json.load(open(sys.argv[1]))
branches = {b['properties']['kind']['const']: b for b in schema['oneOf']}
bad = total = 0
kinds = set()
for f in sorted(pathlib.Path('vectors/message').glob('*.ndjson')):
    for i, line in enumerate(f.read_text().splitlines(), 1):
        if not line.strip():
            continue
        vector = json.loads(line)
        total += 1
        kind = vector.get('kind')
        kinds.add(kind)
        branch = branches.get(kind)
        if branch is None:
            bad += 1
            print(f"problem: {f.name}:{i} kind {kind!r} has no branch in the schema")
            continue
        missing = [k for k in branch['required'] if k not in vector]
        unknown = [k for k in vector if k not in branch['properties']]
        if missing:
            bad += 1
            print(f"problem: {f.name}:{i} {vector.get('vector')} is missing {missing}")
        if unknown:
            bad += 1
            print(f"problem: {f.name}:{i} {vector.get('vector')} carries unknown field(s) {unknown}")
if kinds != set(branches):
    bad += 1
    print(f"problem: the corpus covers {sorted(kinds)}, the schema declares {sorted(branches)}")
if bad:
    print(f"check FAILED: {bad} problem(s) across {total} vectors")
    sys.exit(1)
print(f"{total} vectors match their branch of message-vector.schema.json, across {len(kinds)} kinds")
CHECKSCHEMA

echo "s5_messages: PASS"
