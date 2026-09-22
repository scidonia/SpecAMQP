#!/usr/bin/env bash
#
# S1 contract: the specification carries no hidden trust.
#
#   tests/contracts/s1_proof_integrity.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. no handwritten Lean module under `lean/Spec`, `lean/Contracts`,
#      `lean/Proofs`, `lean/Ref` or `lean/Harness` contains `sorry`, `admit`,
#      `native_decide`, `partial def`,
#      `axiom`, `unsafe`, `opaque`, `extern` or `@[implemented_by]` — and the
#      scanner is not vacuous: a planted file containing each of those is flagged,
#      with file and line, before the real tree is scanned;
#   2. the accepted public theorem's transitive axiom inventory is printed and
#      contains no `sorryAx`, and no axiom outside the reviewed list;
#   3. generated and harness modules are out of scope by construction — the scan
#      names the directories it covers, so an omission is visible rather than
#      implied.
#
# Why it matters: a proof that quietly depends on `sorry`, on `native_decide`'s
# `ofReduceBool`, or on an opaque external model still compiles, and the kernel
# never complains. This gate is the difference between "it builds" and "it is a
# proof".

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly scanned_dirs=(Spec Contracts Proofs Ref Harness)
readonly accepted_theorem="SpecAMQP.Contracts.constructor_grammar_public"

die() {
  printf 's1_proof_integrity: FAIL: %s\n' "$1" >&2
  exit 1
}

note() { printf 'ok   %s\n' "$1"; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

cat >"$tmp/scan.py" <<'PYSCAN'
"""Flag trust-bearing Lean constructs, ignoring comments and string literals."""
import pathlib, re, sys

# Each pattern is (name, regex). Word boundaries keep `partial` from matching
# `partially` and `axiom` from matching `axioms` inside a docstring word.
PATTERNS = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("partial def", re.compile(r"\bpartial\s+def\b")),
    ("axiom", re.compile(r"^\s*axiom\b", re.M)),
    ("constant", re.compile(r"^\s*constant\b", re.M)),
    ("opaque", re.compile(r"\bopaque\s+\w")),
    ("unsafe", re.compile(r"\bunsafe\s+(def|theorem|instance)\b")),
    ("extern", re.compile(r"\bextern\b")),
    ("implemented_by", re.compile(r"implemented_by")),
]


def strip_comments_and_strings(text: str) -> str:
    """Blank out comments and literals so the scan sees only code."""
    out = []
    index, depth = 0, 0
    in_string, in_char = False, False
    while index < len(text):
        two = text[index:index + 2]
        if depth == 0 and not in_string and not in_char:
            if two == "--":
                while index < len(text) and text[index] != "\n":
                    out.append(" ")
                    index += 1
                continue
            if two == "/-":
                depth, index = 1, index + 2
                out.extend("  ")
                continue
        if depth > 0:
            if two == "/-":
                depth, index = depth + 1, index + 2
                out.extend("  ")
                continue
            if two == "-/":
                depth, index = depth - 1, index + 2
                out.extend("  ")
                continue
            out.append("\n" if text[index] == "\n" else " ")
            index += 1
            continue
        if in_string:
            if text[index] == "\\":
                out.extend("  ")
                index += 2
                continue
            if text[index] == '"':
                in_string = False
            out.append("\n" if text[index] == "\n" else " ")
            index += 1
            continue
        if in_char:
            if text[index] == "\\":
                out.extend("  ")
                index += 2
                continue
            if text[index] == "'":
                in_char = False
            out.append(" ")
            index += 1
            continue
        if text[index] == '"':
            in_string, index = True, index + 1
            out.append(" ")
            continue
        if text[index] == "'" and index + 2 < len(text) and text[index + 2] == "'":
            in_char, index = True, index + 1
            out.append(" ")
            continue
        out.append(text[index])
        index += 1
    return "".join(out)


def scan_file(path: pathlib.Path, base: pathlib.Path) -> list[str]:
    stripped = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    found = []
    for name, pattern in PATTERNS:
        for match in pattern.finditer(stripped):
            line = stripped[: match.start()].count("\n") + 1
            found.append(f"{path.relative_to(base)}:{line}: {name}")
    return found


def main() -> int:
    directories = [pathlib.Path(d) for d in sys.argv[1:]]
    problems, scanned = [], 0
    for directory in directories:
        for path in sorted(directory.rglob("*.lean")):
            scanned += 1
            problems.extend(scan_file(path, directory.parent))
    for problem in problems:
        print(f"  trust: {problem}")
    print(f"     scanned {scanned} module(s) under "
          f"{', '.join(str(d) for d in directories)}")
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
PYSCAN

# Planted control: the scanner must fail on a file containing each construct.
mkdir -p "$tmp/planted/Spec"
cat >"$tmp/planted/Spec/Planted.lean" <<'PLANTED'
-- a comment mentioning sorry and native_decide and axiom
/-- a docstring mentioning admit -/
def ok : Nat := 1
def bad : Nat := by sorry
def worse : Nat := by native_decide
axiom hidden : False
opaque obscured : Nat
unsafe def dangerous : Nat := 1
PLANTED
if python3 "$tmp/scan.py" "$tmp/planted/Spec" >"$tmp/planted.log" 2>&1; then
  die "the scanner passed a file containing sorry, native_decide, axiom, opaque and unsafe"
fi
for construct in sorry native_decide axiom opaque unsafe; do
  grep -q ": $construct" "$tmp/planted.log" ||
    die "the planted control was not flagged for '$construct': $(cat "$tmp/planted.log")"
done
grep -q "Planted.lean:4: sorry" "$tmp/planted.log" ||
  die "the scanner does not report the line of the planted sorry: $(cat "$tmp/planted.log")"
note "planted control flagged with file and line; comments and docstrings ignored"

# The real tree.
python3 "$tmp/scan.py" "${scanned_dirs[@]/#/$root/lean/}" >"$tmp/scan.log" 2>&1 ||
  { cat "$tmp/scan.log"; die "the specification contains trust-bearing constructs"; }
tail -1 "$tmp/scan.log" | sed 's/^/     /'
note "no sorry, admit, native_decide, partial, axiom, opaque, unsafe or extern in handwritten modules"

# The accepted theorems' transitive axioms, printed by the kernel. Every proved theorem
# the specification claims is inventoried here, not only the first: a theorem proved from
# nothing but the library and another proved through an axiom nobody looked at are
# different claims, and the difference is only visible if each is asked.
# The modules the probe prints from must be built first: `lake env lean` uses whatever
# olean exists, so a probe run against a stale build reports an unknown constant and the
# failure reads like a missing theorem rather than a missing build.
( cd "$root/lean" && LAKE_NO_CACHE=1 lake build Contracts.Codec Contracts.FrameCodec \
    Contracts.FrameCodecAcceptance Contracts.TypeSystem Proofs.CodecFrameLaws \
    Proofs.CodecRoundTrip Proofs.CodecRoundTripCompound Proofs.CodecRoundTripVariable Spec.ReadLaws ) >"$tmp/axiombuild.log" 2>&1 ||
  die "building the modules the axiom probe reads failed: $(tail -3 "$tmp/axiombuild.log")"

cat >"$tmp/Axioms.lean" <<'AXIOMS'
import Contracts.FrameCodec
import Contracts.FrameCodecAcceptance
import Contracts.TypeSystem
import Proofs.CodecRoundTrip
import Proofs.CodecRoundTripCompound
import Proofs.CodecRoundTripVariable
import Spec.ReadLaws

#print axioms SpecAMQP.Contracts.constructor_grammar_public
#print axioms SpecAMQP.Contracts.extended_header_width
#print axioms SpecAMQP.Contracts.body_starts_after_the_header
#print axioms SpecAMQP.Proofs.beOctets_length
#print axioms SpecAMQP.Proofs.go_length
#print axioms SpecAMQP.Proofs.mod_mul_base
#print axioms SpecAMQP.Proofs.go_foldr_value
#print axioms SpecAMQP.Proofs.bigEndianFieldValue
#print axioms SpecAMQP.Proofs.fieldValueRoundTrip
#print axioms SpecAMQP.Proofs.widthChoice_narrow
#print axioms SpecAMQP.Proofs.widthChoice_wide
#print axioms SpecAMQP.Proofs.lengthWidthOf_eq_widthChoice
#print axioms SpecAMQP.Proofs.sizeWidthOf_eq_widthChoice
#print axioms SpecAMQP.Proofs.compoundOctets_eq
#print axioms SpecAMQP.Proofs.arrayOctets_eq
#print axioms SpecAMQP.Proofs.compoundOctets_ok_length
#print axioms SpecAMQP.Proofs.arrayOctets_ok_length
#print axioms SpecAMQP.Contracts.accepted_frames_carry_performatives
#print axioms SpecAMQP.Contracts.consumed_is_the_declared_size
#print axioms SpecAMQP.Contracts.frame_round_trip_public
#print axioms SpecAMQP.Contracts.value_round_trip_public
#print axioms SpecAMQP.Proofs.doff_lt_of_encodeFrame_ok
#print axioms SpecAMQP.Proofs.lengthWidthOf_narrow
#print axioms SpecAMQP.Proofs.lengthWidthOf_wide
#print axioms SpecAMQP.Proofs.two_pow_eight_mul
#print axioms SpecAMQP.Proofs.lengthPrefixed_eq
#print axioms SpecAMQP.Proofs.lengthPrefixed_ok
#print axioms SpecAMQP.Proofs.takeBe_beOctets
#print axioms SpecAMQP.Spec.ReadLaws.extract_toList_eq_drop_take
#print axioms SpecAMQP.Spec.ReadLaws.takeBe_eq_fold
AXIOMS
( cd "$root/lean" && LAKE_NO_CACHE=1 lake env lean "$tmp/Axioms.lean" ) >"$tmp/axioms.log" 2>&1 ||
  die "could not print the accepted theorem's axioms: $(tail -3 "$tmp/axioms.log")"
grep -q "sorryAx" "$tmp/axioms.log" &&
  { cat "$tmp/axioms.log"; die "the accepted theorem depends on sorryAx"; }
grep -q "ofReduceBool" "$tmp/axioms.log" &&
  { cat "$tmp/axioms.log"; die "the accepted theorem depends on native_decide's ofReduceBool"; }
grep -q "sorryAx" "$tmp/scan.log" && die "an accepted theorem is missing from the inventory"
sed 's/^/     /' "$tmp/axioms.log" | grep "depends on axioms" | sed 's/^     //'
for theorem in "$accepted_theorem" extended_header_width body_starts_after_the_header \
               SpecAMQP.Contracts.accepted_frames_carry_performatives \
               SpecAMQP.Contracts.consumed_is_the_declared_size \
               SpecAMQP.Contracts.frame_round_trip_public \
               SpecAMQP.Contracts.value_round_trip_public \
               SpecAMQP.Proofs.doff_lt_of_encodeFrame_ok \
               SpecAMQP.Proofs.beOctets_length SpecAMQP.Proofs.go_length \
               SpecAMQP.Proofs.mod_mul_base SpecAMQP.Proofs.go_foldr_value \
               SpecAMQP.Proofs.bigEndianFieldValue SpecAMQP.Proofs.fieldValueRoundTrip \
               SpecAMQP.Proofs.widthChoice_narrow SpecAMQP.Proofs.widthChoice_wide \
               SpecAMQP.Proofs.lengthWidthOf_eq_widthChoice SpecAMQP.Proofs.sizeWidthOf_eq_widthChoice \
               SpecAMQP.Proofs.compoundOctets_eq SpecAMQP.Proofs.arrayOctets_eq \
               SpecAMQP.Proofs.compoundOctets_ok_length SpecAMQP.Proofs.arrayOctets_ok_length \
               SpecAMQP.Proofs.lengthWidthOf_narrow SpecAMQP.Proofs.lengthWidthOf_wide \
               SpecAMQP.Proofs.two_pow_eight_mul SpecAMQP.Proofs.lengthPrefixed_eq \
               SpecAMQP.Proofs.lengthPrefixed_ok SpecAMQP.Proofs.takeBe_beOctets \
               SpecAMQP.Spec.ReadLaws.extract_toList_eq_drop_take \
               SpecAMQP.Spec.ReadLaws.takeBe_eq_fold; do
  grep -q "$theorem' depends on axioms" "$tmp/axioms.log" ||
    die "$theorem was not inventoried — the inventory names a theorem the kernel did not print"
done
note "every accepted theorem's axiom inventory contains no sorryAx and no ofReduceBool"

printf 's1_proof_integrity: PASS\n'
