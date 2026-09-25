#!/usr/bin/env bash
#
# The value layer's rule-boundary corpus: the sweep that finds class divergences.
#
#   tests/contracts/value_boundaries.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. both executables build and both artefacts run both corpora;
#   2. every vector gets the same *status* from both artefacts, and every refusal names the same
#      reason class from both. Class rather than detail: four buffers in this family were found
#      where the two artefacts agree on the class and differ in wording (`truncated: 97 octets`
#      against `truncated: 97 octet(s) needed at offset 5 of 9`), so a detail comparison would
#      fail vectors for nothing while a status comparison would miss this family's whole subject;
#   3. the family is non-vacuous across the pair — it admits and it refuses — checked family-wide,
#      because the positives and the negatives live in two files;
#   4. **the one known failure is pinned rather than tolerated.** Two vectors carry the
#      duplicate-key rule (`type:map.u1`, "A map in which there exist two identical key values is
#      invalid"), which neither artefact enforces: both decode the map and admit it, so both
#      vectors fail. A gate that merely tolerated them would hide a stated rule nobody implements;
#      a gate that failed on them would be permanently red and teach its readers to ignore it. So
#      the gate requires them to fail, by name, and goes red the day they start passing — which is
#      what a disposition change should be signalled by;
#   5. nothing else fails. The set of failing vectors is exactly that pair, so a new divergence
#      cannot hide behind a tolerated one.
#
# Why this family exists: the differential compares two readings of the standard and is therefore
# blind to any defect both readings share, and to any defect that lives in a *parameter* of a
# corpus case rather than in the case itself. A sweep of a rule's boundary, crossed with the size
# accounting, is what reaches those, and it found six things on its first run — four of them its
# own author's mistakes.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly admitted="$root/vectors/value-boundaries.ndjson"
readonly refusals="$root/vectors/value-boundary-negatives.ndjson"
readonly corpora=("$admitted" "$refusals")

# The vectors that are expected to fail, because the rule they pin is stated by the artifact and
# enforced by neither artefact. Named individually rather than counted, so a second one appearing
# fails this gate instead of being absorbed.
# Closed: the duplicate-key rule is enforced in both artefacts since 22a9189, so these two ids are no
# longer allowances. They pass, and the checker below reports it if they stop.
die() { printf 'value_boundaries: FAIL: %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"
for corpus in "${corpora[@]}"; do
  [ -f "$corpus" ] || die "missing corpus: $corpus"
done

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

( cd "$root/lean" && LAKE_NO_CACHE=1 lake build amqp-ref amqp-spec ) >"$tmp/build.log" 2>&1 ||
  die "building the executables failed: $(grep -m1 -E '\.lean:[0-9]+:[0-9]+: error' "$tmp/build.log" || tail -3 "$tmp/build.log")"
note "both executables build from Lean"

capture() { # exe corpus outfile
  local exe="$1" corpus="$2" out="$3"
  set +e
  ( cd "$root/lean" && lake exe "$exe" "$corpus" ) >"$out" 2>"$out.err"
  echo "$?" >"$out.exit"
  set -e
}

for corpus in "${corpora[@]}"; do
  name="$(basename "$corpus" .ndjson)"
  capture amqp-ref "$corpus" "$tmp/ref-$name.log"
  capture amqp-spec "$corpus" "$tmp/spec-$name.log"
done

python3 - "$admitted" "$refusals" "$tmp" <<'COMPARE' || exit 1
import json, pathlib, re, sys

admitted, refusals, tmp = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[3])
problems = []


def verdicts(path):
    out = {}
    for line in path.read_text().splitlines():
        if line.strip():
            try:
                entry = json.loads(line)
            except json.JSONDecodeError:
                continue
            if "vector" in entry:
                out[entry["vector"]] = entry
    return out


def expected_class(corpus):
    """The reason class each vector expects, from the corpus rather than from a verdict."""
    out = {}
    for line in corpus.read_text().splitlines():
        if line.strip():
            entry = json.loads(line)
            want = (entry.get("expectError") or {}).get("reason")
            if want:
                out[entry["vector"]] = want
    return out


def klass(detail):
    """The class token a verdict's detail leads with, when it leads with one."""
    head = detail.split(":")[0].strip()
    return head if re.fullmatch(r"[A-Za-z]+", head) else ""


expected = {}
expected.update(expected_class(admitted))
expected.update(expected_class(refusals))

family = {}
for corpus in (admitted, refusals):
    name = corpus.stem
    reference, specification = verdicts(tmp / f"ref-{name}.log"), verdicts(tmp / f"spec-{name}.log")
    family.update({("ref", k): v for k, v in reference.items()})
    family.update({("spec", k): v for k, v in specification.items()})
    only_ref, only_spec = set(reference) - set(specification), set(specification) - set(reference)
    if only_ref or only_spec:
        problems.append(f"{name}: the artefacts saw different vectors "
                        f"({sorted(only_ref)[:3]} only in the reference, {sorted(only_spec)[:3]} only in the specification)")
    for ident in sorted(set(reference) & set(specification)):
        if reference[ident]["status"] != specification[ident]["status"]:
            problems.append(f"{name}: {ident} is {reference[ident]['status']} to the reference and "
                            f"{specification[ident]['status']} to the specification")
        elif reference[ident]["status"] == "fail":
            pass  # reported below, as a failing set, rather than twice
        else:
            left, right = klass(reference[ident].get("detail", "")), klass(specification[ident].get("detail", ""))
            if left and right and left != right:
                problems.append(f"{name}: {ident} is refused as {left} by the reference and {right} by the specification")

# The admitted corpus must pass in full, from both artefacts: a positive vector that fails is a
# regression in an artefact rather than a property of the family.
for side in ("ref", "spec"):
    failing = sorted(k for (s, k), v in family.items()
                     if s == side and k.startswith("boundary-") and not k.startswith("boundary-negative-")
                     and v["status"] != "pass")
    if failing:
        problems.append(f"the {side} artefact failed {len(failing)} admitted vector(s): {failing[:4]}")

# Family-level non-vacuity: across the pair, the family must both admit and refuse.
admitting = any(v["status"] == "pass" and k.startswith("boundary-") and not k.startswith("boundary-negative-")
                for (_, k), v in family.items())
refusing = any(v["status"] == "pass" and k.startswith("boundary-negative-") for (_, k), v in family.items())
if not admitting:
    problems.append("no admitted vector passes, so the family cannot show a rule being satisfied")
if not refusing:
    problems.append("the family's negatives are absent, so the comparison cannot see a refusal")

# Clause 4: the two rules that were once deferred are enforced, by name. Naming them is what catches a
# weakened vector or a reopened gap: a duplicate-key vector that stops being refused fails here, and the
# clause is stated over the negative corpus because that is where a refusal is the expected outcome.
for ident in ("boundary-negative-map-duplicate-string-keys", "boundary-negative-map-duplicate-null-keys"):
    for side, label in (("ref", "reference"), ("spec", "specification")):
        entry = family.get((side, ident))
        if entry is None:
            problems.append(f"{ident} is missing from the {label}'s verdicts")
        elif entry["status"] != "pass":
            problems.append(f"{ident} is not refused by the {label} any more: the duplicate-key rule went "
                            f"unenforced again, or the vector was weakened, and either way "
                            f"`ledger/dispositions/unkeyed-normative.json` and this gate have to change together")
        elif expected.get(ident) and klass(entry.get("detail", "")) != expected[ident]:
            problems.append(f"{ident} is refused by the {label} as {klass(entry.get('detail', ''))!r}, not the "
                            f"{expected[ident]!r} the vector expects: the rule is enforced, but not as its clause says")

# Clause 5: nothing else fails.
others = sorted({k for (_, k), v in family.items() if v["status"] != "pass"})
if others:
    problems.append(f"{len(others)} vector(s) fail outside the known pair: {others[:6]}")

if problems:
    for p in problems:
        print(f"problem: {p}", file=sys.stderr)
    print(f"check FAILED: {len(problems)} problem(s) in the value boundary family", file=sys.stderr)
    sys.exit(1)

total = {k for (_, k) in family}
print(f"     {len(total)} vectors: every one identical in status from both artefacts, "
      f"the the two duplicate-key vectors refused by name, and nothing else failing")
COMPARE

note "the sweep agrees across both artefacts, and the two rules that were once deferred are pinned as refused"
echo "value_boundaries: PASS"
