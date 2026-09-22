#!/usr/bin/env bash
#
# S0 contract: source identity, clause ledger, and disposition gates.
#
#   tests/contracts/s0_sources_ledger.sh
#
# Observable contract, in order:
#
#   1. the vendored OASIS artifacts match `toolchain/sources.toml`;
#   2. a one-byte mutation of a vendored copy is refused, with the hash named as
#      the reason (so the pin is not merely advisory);
#   3. the planted-control artifact is classified exactly as the ledger claims:
#      emphasis-wrapped keywords, a keyword pair split across lines, `<picture>`
#      and `revhistory` content excluded, lowercase prose not normative, an
#      adjective REQUIRED recorded, and a named constant resolved through `<xref>`;
#   4. disposition gates bite: a correct disposition passes, a stale text hash
#      fails, and an unknown clause reference fails;
#   5. the repository's own ledger, dispositions, audit and baseline
#      reconciliation check clean.
#
# Runs offline, writes only inside a temporary directory.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly ledger="$root/scripts/clause-ledger.py"
readonly fixtures="$root/tests/contracts/fixtures/ledger"

die() {
  printf 's0_sources_ledger: FAIL: %s\n' "$1" >&2
  exit 1
}

note() { printf 'ok   %s\n' "$1"; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

[ -f "$ledger" ] || die "missing scripts/clause-ledger.py"
command -v python3 >/dev/null || die "python3 is required"

# 1. Vendored identity --------------------------------------------------------
bash "$root/scripts/fetch-oasis.sh" --verify >"$tmp/verify.log" 2>&1 ||
  die "vendored artifacts do not match toolchain/sources.toml: $(cat "$tmp/verify.log")"
note "vendored artifacts match the pinned hashes"

# 2. Mutation control: same-size byte flip must be refused --------------------
mkdir -p "$tmp/mut/spec/oasis" "$tmp/mut/toolchain" "$tmp/mut/scripts"
cp "$root"/spec/oasis/*.xml "$tmp/mut/spec/oasis/"
cp "$root/toolchain/sources.toml" "$tmp/mut/toolchain/"
cp "$root/scripts/fetch-oasis.sh" "$tmp/mut/scripts/"
python3 - "$tmp/mut/spec/oasis/amqp-core-types-v1.0-os.xml" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
data = bytearray(path.read_bytes())
data[4096] ^= 0x01          # one bit, same length
path.write_bytes(bytes(data))
PY
if bash "$tmp/mut/scripts/fetch-oasis.sh" --verify >"$tmp/mut.log" 2>&1; then
  die "a one-bit mutation of a vendored artifact was accepted"
fi
grep -q 'sha256 mismatch' "$tmp/mut.log" ||
  die "mutation refused for the wrong reason: $(cat "$tmp/mut.log")"
note "one-bit mutation refused, with the hash mismatch named"

# 3. Planted classification controls -----------------------------------------
python3 "$ledger" generate --artifacts "$fixtures" --out "$tmp/planted" \
  --dispositions "$tmp/planted-dispositions" >"$tmp/planted.log" 2>&1 ||
  die "ledger generation on the planted artifact failed: $(cat "$tmp/planted.log")"
python3 - "$tmp/planted/clauses.json" "$tmp/planted/coverage.json" <<'PY' || exit 1
import json, pathlib, sys
clauses = json.loads(pathlib.Path(sys.argv[1]).read_text())["clauses"]
coverage = json.loads(pathlib.Path(sys.argv[2]).read_text())

problems = []
kinds = {}
for clause in clauses:
    kinds[clause["kind"]] = kinds.get(clause["kind"], 0) + 1

expected_kinds = {"MUST": 1, "MUST NOT": 1, "SHOULD": 1, "REQUIRED": 1}
if kinds != expected_kinds:
    problems.append(f"classification: expected {expected_kinds}, found {kinds}")

by_kind = {}
for clause in clauses:
    by_kind.setdefault(clause["kind"], []).append(clause)

# emphasis-wrapped keyword: read from <b>MUST</b>
if "The peer MUST send a header before any frame." not in [
    c["text"] for c in by_kind.get("MUST", [])
]:
    problems.append("emphasis-wrapped <b>MUST</b> was not read as a MUST clause")

# split-across-lines keyword pair, with the constant resolved through <xref>
must_not = [c["text"] for c in by_kind.get("MUST NOT", [])]
if must_not != ["It MUST NOT exceed 512 frames in one batch."]:
    problems.append(f"line-wrapped MUST NOT / <xref> resolution wrong: {must_not}")

# <picture> and revhistory content must not appear at all
joined = " ".join(c["text"] for c in clauses)
if "revision history" in joined:
    problems.append("a clause was taken from the revhistory section")
if "peer A" in joined or "peer B" in joined:
    problems.append("a clause was taken from a <picture> diagram")
if kinds.get("MUST", 0) != 1:
    problems.append("a non-normative MUST (picture/revhistory) was counted")

# lowercase prose is a review signal, never a clause
lowercase = json.loads((pathlib.Path(sys.argv[2]).parent / "lowercase-keywords.json").read_text())
if not any("must handle this case" in s["text"] for s in lowercase["statements"]):
    problems.append("lowercase normative-looking prose was not reported as a review signal")

audit = coverage["per_artifact"]["amqp-core-planted-v1.0-os.xml"]["audit"]
if audit["mismatches"]:
    problems.append(f"audit mismatch on the planted artifact: {audit['mismatches']}")
if audit["excluded"].get("MUST", 0) < 2:
    problems.append("excluded <picture> MUST tokens were not reported")

for problem in problems:
    print(f"  planted control: {problem}")
raise SystemExit(1 if problems else 0)
PY
note "planted controls classified as claimed"

# 4. Disposition gates --------------------------------------------------------
python3 - "$tmp/planted/clauses.json" "$tmp/planted/pictures.json" "$tmp/planted-dispositions" <<'PY' || exit 1
import json, pathlib, sys
clauses = json.loads(pathlib.Path(sys.argv[1]).read_text())["clauses"]
pictures = json.loads(pathlib.Path(sys.argv[2]).read_text())["pictures"]
out = pathlib.Path(sys.argv[3]); out.mkdir(parents=True, exist_ok=True)
target = next(c for c in clauses if c["kind"] == "MUST")
reviewable = [p for p in pictures if p["looks_normative"]]
if not reviewable:
    print("  planted control: the BNF picture was not flagged for review")
    raise SystemExit(1)
picture = reviewable[0]

def clause_disposition(digest):
    return {target["ref"]: {"disposition": "formalized:Spec.Planted.thing", "text_sha256": digest}}

def all_pictures(overrides=None, omit=()):
    overrides = overrides or {}
    return {
        p["ref"]: {
            "disposition": "formalized:Spec.Planted.picture",
            "text_sha256": overrides.get(p["ref"], p["content_sha256"]),
        }
        for p in reviewable
        if p["ref"] not in omit
    }

def write(name, entries):
    (out / name).write_text(json.dumps({"schema_version": 1, "dispositions": entries}) + "\n")

write("good.json", {**clause_disposition(target["text_sha256"]), **all_pictures()})
write("stale.json", {**clause_disposition("0" * 64), **all_pictures()})
write("unknown.json", {
    **clause_disposition(target["text_sha256"]),
    **all_pictures(),
    "amqp-core-planted-v1.0-os.xml#amqp:planted/section:nonexistent.1":
        {"disposition": "informative", "text_sha256": target["text_sha256"]},
})
write("picture-missing.json", {
    **clause_disposition(target["text_sha256"]),
    **all_pictures(omit={picture["ref"]}),
})
write("picture-stale.json", {
    **clause_disposition(target["text_sha256"]),
    **all_pictures(overrides={picture["ref"]: "0" * 64}),
})
PY
run_case() { # name expected-exit grep-pattern
  local name="$1" expected="$2" pattern="$3"
  mkdir -p "$tmp/case-$name"
  cp "$tmp/planted-dispositions/$name.json" "$tmp/case-$name/"
  set +e
  python3 "$ledger" check --artifacts "$fixtures" --out "$tmp/out-$name" \
    --dispositions "$tmp/case-$name" >"$tmp/case-$name.log" 2>&1
  local status=$?
  set -e
  [ "$status" = "$expected" ] ||
    die "disposition case '$name': expected exit $expected, got $status ($(cat "$tmp/case-$name.log"))"
  grep -q "$pattern" "$tmp/case-$name.log" ||
    die "disposition case '$name': diagnostic did not mention '$pattern': $(cat "$tmp/case-$name.log")"
  note "disposition case '$name' behaved as contracted (exit $status)"
}
run_case good 0 "check passed"
run_case stale 1 "STALE disposition"
run_case unknown 1 "no such clause"
run_case picture-missing 1 "has no disposition"
run_case picture-stale 1 "STALE picture disposition"

# 5. The repository's own ledger ---------------------------------------------
python3 "$ledger" check >"$tmp/repo.log" 2>&1 ||
  die "repository ledger check failed: $(tail -5 "$tmp/repo.log")"
grep -q "check passed" "$tmp/repo.log" || die "unexpected repository ledger output"
note "repository ledger, audit and reconciliation check clean"
grep -E '^(clauses|dispositions|undispositioned)' "$tmp/repo.log" | sed 's/^/     /'

printf 's0_sources_ledger: PASS\n'
