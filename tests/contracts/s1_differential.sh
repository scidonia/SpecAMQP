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

for corpus in "$worked" "$generated"; do
  case "$corpus" in
    "$worked") name=worked ;;
    *) name=generated ;;
  esac
  run amqp-ref "$corpus" "$tmp/ref-$name.log"
  run amqp-spec "$corpus" "$tmp/spec-$name.log"
  python3 - "$tmp/ref-$name.log" "$tmp/spec-$name.log" "$name" <<'PYCMP' || exit 1
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

printf 's1_differential: PASS\n'
