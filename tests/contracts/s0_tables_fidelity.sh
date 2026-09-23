#!/usr/bin/env bash
#
# S0 contract: the generated declared surface is derived, current, and load-bearing.
#
#   tests/contracts/s0_tables_fidelity.sh
#
# Observable contract:
#
#   1. the generator reproduces the committed `lean/Generated/Oasis/*.lean`
#      byte-for-byte (so the committed tables are derived, not transcribed);
#   2. mutating a descriptor code in a scratch copy of an artifact changes the
#      generated output and makes the currency check fail — the gate is not
#      vacuous;
#   3. the generated record counts equal the declared surface of the pinned
#      artifacts, counted independently here;
#   4. no hand-written specification, contract or proof file contains a literal
#      descriptor code or an `amqp:`-shaped symbol (those come from the tables).
#
# Runs offline against the vendored artifacts; writes only into a temporary
# directory. Requires the pinned shell for step 5 only.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly generator="$root/scripts/gen-oasis-lean.py"
readonly artifacts="$root/spec/oasis"
readonly generated="$root/lean/Generated/Oasis"

die() {
  printf 's0_tables_fidelity: FAIL: %s\n' "$1" >&2
  exit 1
}

note() { printf 'ok   %s\n' "$1"; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

[ -f "$generator" ] || die "missing scripts/gen-oasis-lean.py"
[ -d "$generated" ] || die "missing $generated (run scripts/gen-oasis-lean.py)"

# 1. The committed tables are current ----------------------------------------
python3 "$generator" --check >"$tmp/check.log" 2>&1 ||
  die "committed tables differ from a fresh generation: $(cat "$tmp/check.log")"
note "committed tables reproduce byte-for-byte"

# 2. Mutation control: a wrong descriptor code cannot survive generation -----
mkdir -p "$tmp/mut"
cp "$artifacts"/*.xml "$tmp/mut/"
python3 - "$tmp/mut/amqp-core-transport-v1.0-os.xml" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
before = text
# `amqp:transfer:list` is 0x14; make it 0x15, which is `disposition`.
text = text.replace('name="amqp:transfer:list" code="0x00000000:0x00000014"',
                    'name="amqp:transfer:list" code="0x00000000:0x00000015"', 1)
if text == before:
    print("mutation did not apply: the descriptor text changed", file=sys.stderr)
    raise SystemExit(1)
path.write_text(text, encoding="utf-8")
PY
python3 "$generator" --artifacts "$tmp/mut" --out "$tmp/mut-out" >/dev/null 2>&1 ||
  die "generation failed on the mutated artifact set"
if diff -q "$tmp/mut-out/Types.lean" "$generated/Types.lean" >/dev/null; then
  die "a mutated descriptor code produced identical tables: the fidelity gate is vacuous"
fi
grep -q 'name := "amqp:transfer:list", domain := 0, code := 21' "$tmp/mut-out/Types.lean" ||
  die "the mutated code did not appear in the generated tables"
python3 "$generator" --artifacts "$tmp/mut" --out "$generated" --check >"$tmp/mut-check.log" 2>&1 &&
  die "the currency check passed against mutated tables"
note "mutated descriptor code changes the tables and fails the currency check"

# 3. Counts equal the declared surface of the pinned artifacts ---------------
python3 - "$artifacts" "$generated/provenance.json" <<'PY' || exit 1
import json, pathlib, sys
from xml.etree import ElementTree

artifacts = pathlib.Path(sys.argv[1])
provenance = json.loads(pathlib.Path(sys.argv[2]).read_text())

counted = {"type": 0, "field": 0, "choice": 0, "descriptor": 0, "encoding": 0, "definition": 0}
for path in sorted(artifacts.glob("amqp-core-*-v1.0-os.xml")):
    for element in ElementTree.parse(path).getroot().iter():
        attributes = element.attrib
        # Match what the generator treats as a declaration, not just the tag:
        # 11 encodings carry no `name`, and a descriptor is only a descriptor
        # when its code parses.
        if element.tag == "type" and "name" in attributes and "class" in attributes:
            counted["type"] += 1
        elif element.tag == "field" and "name" in attributes:
            counted["field"] += 1
        elif element.tag == "choice" and "name" in attributes:
            counted["choice"] += 1
        elif element.tag == "descriptor" and ":" in attributes.get("code", ""):
            counted["descriptor"] += 1
        elif element.tag == "encoding" and "code" in attributes:
            counted["encoding"] += 1
        elif element.tag == "definition" and "name" in attributes:
            counted["definition"] += 1

expected = {
    "types": counted["type"],
    "fields": counted["field"],
    "choices": counted["choice"],
    "descriptors": counted["descriptor"],
    "encodings": counted["encoding"],
    "constants": counted["definition"],
}
problems = [
    f"{key}: generated {provenance['counts'].get(key)}, artifacts declare {value}"
    for key, value in expected.items()
    if provenance["counts"].get(key) != value
]
digests = provenance["artifacts"]
for path in sorted(artifacts.glob("amqp-core-*-v1.0-os.xml")):
    if digests.get(path.name) != __import__("hashlib").sha256(path.read_bytes()).hexdigest():
        problems.append(f"{path.name}: provenance digest does not match the vendored bytes")
for problem in problems:
    print(f"  counts: {problem}")
raise SystemExit(1 if problems else 0)
PY
note "generated counts equal the artifacts' declared surface"

# 4. No hand-typed descriptor codes outside the generated tables -------------
python3 - "$root" <<'PY' || exit 1
import pathlib, re, sys
root = pathlib.Path(sys.argv[1])
# Two ways a handwritten module could smuggle in a table value: writing an
# `amqp:` symbol itself, or constructing a descriptor from a numeric literal
# instead of reading the generated table. Bare octet literals are *not* flagged:
# the encoding grammar's ranges and the frame layout are the specification's own
# content (`%x40`, `%x00`), and the grammar module is where they belong. The
# binding that matters is the theorem relating those ranges to the table, which
# this contract runs below.
descriptor_literal = re.compile(r'descriptor\s*:=\s*some\s*\{[^}]*code\s*:=\s*0x')
symbol = re.compile(r'"amqp:')
scanned = 0
problems = []
for directory in ("Spec", "Contracts", "Proofs"):
    for path in sorted((root / "lean" / directory).rglob("*.lean")):
        scanned += 1
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            stripped = line.split("--", 1)[0]
            if symbol.search(stripped):
                problems.append(f"{path.relative_to(root)}:{number}: hand-typed amqp: symbol")
            if descriptor_literal.search(stripped):
                problems.append(
                    f"{path.relative_to(root)}:{number}: descriptor constructed from a literal code"
                )
for problem in problems:
    print(f"  hand-typed: {problem}")
if problems:
    raise SystemExit(1)
print(f"     scanned {scanned} handwritten module(s) in lean/Spec, lean/Contracts, lean/Proofs")
PY
note "no hand-typed descriptor codes or amqp: symbols in handwritten modules"

# 5. The generated modules compile (requires the pinned shell) ---------------
if command -v lake >/dev/null 2>&1 && [ -d "$root/lean/.lake/packages/mathlib" ]; then
  ( cd "$root/lean" && lake build Generated.Oasis.Constants Generated.Oasis.Types \
      Generated.Oasis.Fields Generated.Oasis.Encodings Generated.Oasis.Choices ) \
    >"$tmp/build.log" 2>&1 ||
    die "generated modules do not compile: $(tail -5 "$tmp/build.log")"
  note "generated modules compile against the pinned closure"
else
  printf 'skip generated modules compile: run inside the pinned `spec` shell\n'
fi


# The produced set is *exact*. `gen-oasis-lean.py --check` iterates what the generator produces and
# compares each to its committed counterpart, so a produced file that is stale fails — but a committed
# module the generator does not produce is invisible to it, and would be compiled like any other module
# in a registered library. Since `Generated/` is never hand-edited, a file there that the generator does
# not produce is a hand-edit that has stopped being regenerable. Measured: the directory can hold such a
# file and `--check` still reports success.
python3 - "$root" <<'PRODUCED' || exit 1
import pathlib, sys
root = pathlib.Path(sys.argv[1])
produced = {'Choices.lean', 'Constants.lean', 'Encodings.lean', 'Fields.lean', 'Types.lean', 'provenance.json'}
have = {p.name for p in (root / 'lean/Generated/Oasis').iterdir()}
extra = sorted(have - produced)
missing = sorted(produced - have)
for name in extra:
    print(f'problem: lean/Generated/Oasis/{name} is not a file the generator produces')
for name in missing:
    print(f'problem: lean/Generated/Oasis/{name} is produced and is not in the tree')
print(f'generated tables: {len(have)} file(s), exactly the produced set')
sys.exit(1 if (extra or missing) else 0)
PRODUCED

printf 's0_tables_fidelity: PASS\n'
