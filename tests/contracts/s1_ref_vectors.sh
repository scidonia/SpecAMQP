#!/usr/bin/env bash
#
# S1 contract: the Lean reference implementation satisfies the worked-example corpus
# and the generated corpus, and both corpora are reproducible and discriminating.
#
#   tests/contracts/s1_ref_vectors.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. the reference implementation builds as a native executable from Lean with
#      no external translation step, and prints one JSON verdict per vector;
#   2. both corpora pass in full, exit status 0;
#   3. both corpora are well formed: every vector cites at least one clause or
#      figure, names a known kind, and carries the fields its kind requires;
#   4. the generated corpus reproduces byte-for-byte from its generator, and the
#      generator's own encoder reproduces the artifact's published examples —
#      otherwise the corpus would be hand-maintained data with no provenance;
#   5. the harness is not vacuous: corrupting one expected octet in a scratch
#      copy makes the run fail and names that vector;
#   6. the corpus retains the controls that make the checks bite: a compound size
#      raised by one octet, and the exhaustive property sweep over every one- and
#      two-octet input.
#
# Runs offline; writes only inside a temporary directory.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly worked="$root/vectors/primitives.ndjson"
readonly generated="$root/vectors/generated.ndjson"
readonly schema="$root/tests/contracts/value-vector.schema.json"

die() {
  printf 's1_ref_vectors: FAIL: %s\n' "$1" >&2
  exit 1
}

note() { printf 'ok   %s\n' "$1"; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"
for required in "$worked" "$generated" "$schema" "$root/scripts/gen-value-vectors.py"; do
  [ -f "$required" ] || die "missing $(realpath --relative-to="$root" "$required" 2>/dev/null || echo "$required")"
done
python3 -c "import json,sys; json.load(open(sys.argv[1]))" "$schema" ||
  die "value-vector.schema.json is not valid JSON"

# 1. Build the executable from Lean.
( cd "$root/lean" && LAKE_NO_CACHE=1 lake build amqp-ref ) >"$tmp/build.log" 2>&1 ||
  die "building amqp-ref failed: $(tail -3 "$tmp/build.log")"
note "reference implementation builds as a native executable from Lean"

# 3. Corpus shape, before running it.
python3 - "$worked" "$generated" "$schema" <<'PYSHAPE' || exit 1
import json, pathlib, re, sys
schema = json.loads(pathlib.Path(sys.argv[3]).read_text())
id_pattern = re.compile(schema["properties"]["vector"]["pattern"])
problems = []
for corpus in sys.argv[1:3]:   # argv[1:3] are the corpora; argv[3] is the schema, whose
                               # lines are not JSON lines and must not be walked as a corpus
    seen = set()
    lines = [l for l in pathlib.Path(corpus).read_text().splitlines() if l.strip()]
    for number, line in enumerate(lines, 1):
        entry = json.loads(line)
        where = f"{pathlib.Path(corpus).name}:{entry.get('vector', number)}"
        ident = entry.get("vector", f"line {number}")
        if ident in seen:
            problems.append(f"{where}: duplicate vector id")
        seen.add(ident)
        if not id_pattern.match(ident):
            problems.append(f"{where}: vector id breaks its own schema pattern "
                            f"({schema['properties']['vector']['pattern']})")
        if not entry.get("clauses"):
            problems.append(f"{where}: cites no clause or figure")
        kind = entry.get("kind")
        if kind not in ("decode", "encode", "reject", "property"):
            problems.append(f"{where}: unknown kind {kind!r}")
        if kind in ("decode", "encode") and "value" not in entry:
            problems.append(f"{where}: kind {kind} needs a value")
        if kind == "reject" and not entry.get("expectError", {}).get("condition"):
            problems.append(f"{where}: kind reject needs an expected error condition")
        if kind == "property" and not entry.get("property"):
            problems.append(f"{where}: kind property needs a property name")
        octets = entry.get("bytes", "")
        if not octets or len(octets) % 2 or any(c not in "0123456789abcdef" for c in octets):
            problems.append(f"{where}: bytes are not lowercase hex pairs")
    print(f"     {pathlib.Path(corpus).name}: {len(lines)} vectors, each citing a source")
for problem in problems[:20]:
    print(f"  corpus: {problem}")
if problems:
    raise SystemExit(1)
PYSHAPE
note "both corpora are well formed and cite their sources"

# 4. The generated corpus reproduces from its generator.
python3 "$root/scripts/gen-value-vectors.py" --out "$tmp/regenerated.ndjson" >"$tmp/gen.log" 2>&1 ||
  die "the generator failed: $(cat "$tmp/gen.log")"
cmp -s "$tmp/regenerated.ndjson" "$generated" ||
  die "vectors/generated.ndjson is not what the generator produces (regenerate it)"
grep -q "disagrees with the artifact" "$tmp/gen.log" &&
  die "the generator's encoder no longer reproduces the published examples"
note "generated corpus reproduces from its generator, which reproduces the artifact's examples"

# 2. Both corpora pass.
for corpus in "$worked" "$generated"; do
  name="$(basename "$corpus")"
  ( cd "$root/lean" && lake exe amqp-ref "$corpus" ) >"$tmp/$name.log" 2>"$tmp/$name.err" ||
    die "$name did not pass: $(tail -2 "$tmp/$name.err")"
  grep -q "0 failure(s)" "$tmp/$name.err" || die "unexpected summary for $name: $(cat "$tmp/$name.err")"
  python3 - "$tmp/$name.log" <<'PYVERDICT' || exit 1
import json, pathlib, sys
verdicts = [json.loads(l) for l in pathlib.Path(sys.argv[1]).read_text().splitlines() if l.strip()]
bad = [v for v in verdicts if v["status"] != "pass"]
if bad:
    for v in bad[:6]:
        print(f"  verdict: {v['vector']} {v['detail'][:120]}")
    raise SystemExit(1)
kinds = {}
for v in verdicts:
    kinds[v["kind"]] = kinds.get(v["kind"], 0) + 1
print(f"     {len(verdicts)} verdicts, all pass, by kind {kinds}")
PYVERDICT
  note "$name passes in full"
done

# 5. Mutation control: a corrupted expectation must be caught.
python3 - "$worked" "$tmp/mutated.ndjson" <<'PYMUT' || exit 1
import json, pathlib, sys
lines = [l for l in pathlib.Path(sys.argv[1]).read_text().splitlines() if l.strip()]
out = []
for line in lines:
    entry = json.loads(line)
    if entry["vector"] == "str8-hello-encode":
        entry["bytes"] = entry["bytes"].replace("1e", "1f", 1)
    out.append(json.dumps(entry, sort_keys=True))
pathlib.Path(sys.argv[2]).write_text("\n".join(out) + "\n")
PYMUT
set +e
( cd "$root/lean" && lake exe amqp-ref "$tmp/mutated.ndjson" ) >"$tmp/mut.log" 2>"$tmp/mut.err"
status=$?
set -e
[ "$status" = 1 ] || die "a corrupted expectation produced exit $status, expected 1"
grep -q '"vector":"str8-hello-encode"' "$tmp/mut.log" || die "the corrupted vector was not named"
grep -q '"status":"fail"' "$tmp/mut.log" || die "the corrupted vector was not reported as failing"
note "corrupted expectation caught, and the failing vector named"

# 6. The controls that make the checks bite are retained.
grep -q '"vector": "book-composite-wrong-size-rejected"' "$worked" ||
  die "the wrong-size control vector is missing"
grep -q 'c04103' "$worked" || die "the wrong-size control vector lost its raised size octet"
count_props=$(python3 -c "
import json,sys
print(sum(1 for l in open('$generated') if l.strip() and json.loads(l)['kind']=='property'))")
[ "$count_props" -ge 65000 ] ||
  die "the exhaustive property sweep shrank to $count_props vectors"
note "controls retained: raised-size rejection, and $count_props property vectors over short inputs"

printf 's1_ref_vectors: PASS\n'
