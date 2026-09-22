#!/usr/bin/env bash
#
# S1 contract: the Lean reference implementation satisfies the worked-example corpus.
#
#   tests/contracts/s1_ref_vectors.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. the reference implementation builds as a native executable from Lean with
#      no external translation step, and prints one JSON verdict per vector;
#   2. `vectors/primitives.ndjson` passes in full, exit status 0;
#   3. the corpus is well formed: every vector cites at least one clause or
#      figure, names a known kind, and carries the fields its kind requires;
#   4. the harness is not vacuous: corrupting one expected octet in a scratch
#      copy makes the run fail and names that vector;
#   5. the corpus is discriminating in the other direction too: a vector whose
#      bytes are one octet wrong must be rejected rather than tolerated.
#
# Runs offline; writes only inside a temporary directory.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly corpus="$root/vectors/primitives.ndjson"
readonly schema="$root/tests/contracts/value-vector.schema.json"

die() {
  printf 's1_ref_vectors: FAIL: %s\n' "$1" >&2
  exit 1
}

note() { printf 'ok   %s\n' "$1"; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"
[ -f "$corpus" ] || die "missing vectors/primitives.ndjson"
[ -f "$schema" ] || die "missing tests/contracts/value-vector.schema.json"
python3 -c "import json,sys; json.load(open(sys.argv[1]))" "$schema" ||
  die "value-vector.schema.json is not valid JSON"

# 1. Build the executable from Lean.
( cd "$root/lean" && LAKE_NO_CACHE=1 lake build amqp-ref ) >"$tmp/build.log" 2>&1 ||
  die "building amqp-ref failed: $(tail -3 "$tmp/build.log")"
note "reference implementation builds as a native executable from Lean"

# 3. Corpus shape, before running it.
python3 - "$corpus" <<'PY' || exit 1
import json, pathlib, sys
problems = []
lines = [l for l in pathlib.Path(sys.argv[1]).read_text().splitlines() if l.strip()]
seen = set()
for number, line in enumerate(lines, 1):
    entry = json.loads(line)
    ident = entry.get("vector", f"line {number}")
    if ident in seen:
        problems.append(f"{ident}: duplicate vector id")
    seen.add(ident)
    if not entry.get("clauses"):
        problems.append(f"{ident}: cites no clause or figure")
    kind = entry.get("kind")
    if kind not in ("decode", "encode", "reject"):
        problems.append(f"{ident}: unknown kind {kind!r}")
    if kind in ("decode", "encode") and "value" not in entry:
        problems.append(f"{ident}: kind {kind} needs a value")
    if kind == "reject" and not entry.get("expectError", {}).get("condition"):
        problems.append(f"{ident}: kind reject needs an expected error condition")
    bytes_ = entry.get("bytes", "")
    if not bytes_ or len(bytes_) % 2 or any(c not in "0123456789abcdef" for c in bytes_):
        problems.append(f"{ident}: bytes are not lowercase hex pairs")
for problem in problems:
    print(f"  corpus: {problem}")
if problems:
    raise SystemExit(1)
print(f"     {len(lines)} vectors, each citing at least one clause or figure")
PY
note "corpus is well formed and cites its sources"

# 2. The corpus passes.
( cd "$root/lean" && lake exe amqp-ref "$corpus" ) >"$tmp/run.log" 2>"$tmp/run.err" ||
  die "the corpus did not pass: $(cat "$tmp/run.err")"
grep -q "0 failure(s)" "$tmp/run.err" ||
  die "unexpected runner summary: $(cat "$tmp/run.err")"
python3 - "$tmp/run.log" <<'PY' || exit 1
import json, pathlib, sys
verdicts = [json.loads(l) for l in pathlib.Path(sys.argv[1]).read_text().splitlines() if l.strip()]
if not verdicts:
    print("  no verdicts produced")
    raise SystemExit(1)
bad = [v for v in verdicts if v["status"] != "pass"]
if bad:
    for v in bad:
        print(f"  verdict: {v['vector']} {v['detail']}")
    raise SystemExit(1)
kinds = {}
for v in verdicts:
    kinds[v["kind"]] = kinds.get(v["kind"], 0) + 1
print(f"     {len(verdicts)} verdicts, all pass, by kind {kinds}")
PY
note "every vector in the corpus passes"

# 4. Mutation control: a corrupted expectation must be caught.
python3 - "$corpus" "$tmp/mutated.ndjson" <<'PY'
import json, pathlib, sys
lines = [l for l in pathlib.Path(sys.argv[1]).read_text().splitlines() if l.strip()]
out = []
for line in lines:
    entry = json.loads(line)
    if entry["vector"] == "str8-hello-encode":
        # One octet of the expected encoding changed.
        entry["bytes"] = entry["bytes"].replace("1e", "1f", 1)
    out.append(json.dumps(entry, sort_keys=True))
pathlib.Path(sys.argv[2]).write_text("\n".join(out) + "\n")
PY
set +e
( cd "$root/lean" && lake exe amqp-ref "$tmp/mutated.ndjson" ) >"$tmp/mut.log" 2>"$tmp/mut.err"
status=$?
set -e
[ "$status" = 1 ] || die "a corrupted expectation produced exit $status, expected 1"
grep -q '"vector":"str8-hello-encode"' "$tmp/mut.log" ||
  die "the corrupted vector was not named in the verdicts"
grep -q '"status":"fail"' "$tmp/mut.log" || die "the corrupted vector was not reported as failing"
note "corrupted expectation caught, and the failing vector named"

# 5. The size check is load-bearing: one octet of a size field raised by one.
grep -q '"vector": "book-composite-wrong-size-rejected"' "$corpus" ||
  die "the wrong-size control vector is missing from the corpus"
grep -q 'c04103' "$corpus" || die "the wrong-size control vector does not carry the raised size octet"
note "the corpus retains the raised-size control that shows the size check bites"

printf 's1_ref_vectors: PASS\n'
