#!/usr/bin/env bash
# Every generated corpus is what its generator produces, byte for byte.
#
# AGENTS.md states this rule and two of the three corpora were checked inside their own
# contracts while the third was not — which is how a hand-edit to generated output sat in
# the tree for a whole session, invisible until the next regeneration would silently revert
# it. A corpus its generator does not reproduce is a corpus nobody can regenerate.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 scripts/gen-value-vectors.py --out "$tmp/values.ndjson" >"$tmp/v.log" 2>&1
python3 scripts/gen-value-vectors.py --frames "$tmp/frames.ndjson" >"$tmp/f.log" 2>&1
python3 scripts/gen-exchange-vectors.py --out "$tmp/exchanges.ndjson" >"$tmp/e.log" 2>&1
python3 scripts/gen-value-vectors.py --messages "$tmp/messages.ndjson" >"$tmp/m.log" 2>&1
python3 scripts/gen-value-vectors.py --flow "$tmp/flow.ndjson" --flow-negative "$tmp/flow-negative.ndjson" >"$tmp/fl.log" 2>&1
status=0
check() {  # name, generated, committed
  if cmp -s "$2" "$3"; then
    printf '%s: byte-identical to its generator\n' "$1"
  else
    printf 'problem: %s differs from what its generator produces — %s line(s)\n' \
      "$1" "$(diff "$2" "$3" | grep -c '^[<>]' || true)"
    status=1
  fi
}
check values    "$tmp/values.ndjson"    vectors/generated.ndjson
check frames    "$tmp/frames.ndjson"    vectors/generated-frames.ndjson
check exchanges "$tmp/exchanges.ndjson" vectors/generated-exchanges.ndjson
check messages  "$tmp/messages.ndjson"  vectors/message/generated.ndjson
check flow          "$tmp/flow.ndjson"          vectors/flow.ndjson
check flow-negative "$tmp/flow-negative.ndjson" vectors/flow-negative.ndjson
if [ "$status" -ne 0 ]; then
  echo "check FAILED: a generated corpus is not what its generator produces"
  echo "a hand-edit to generated output reverts at the next regeneration, and the gate that"
  echo "reads those files then fails for whoever regenerated. Fix the generator, not the corpus."
  exit 1
fi
echo "s0_generator_fidelity: PASS"
