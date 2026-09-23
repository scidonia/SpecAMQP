#!/usr/bin/env bash
# The two value readers name the same class for every buffer of a generated family, and the family is
# as broad as this contract requires.
#
# Why the floor lives here rather than in the driver: a check and its acceptance threshold are
# different decisions. The sweep prints what it read and exits non-zero on a divergence; how much it
# must have read in order for its silence to mean something is this file's business, and it is a
# decision that changes when someone decides the family should be wider.
#
# The vacuity clause is the one that matters most. A family where neither reader refuses anything
# reports "agreement" over an empty surface, and a family can shrink to exactly that state while every
# buffer in it still agrees — so the class floors alone would not catch it.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

die() { printf 'value_class_agreement: FAIL: %s\n' "$1" >&2; exit 1; }

readonly floor=100000
log="$(mktemp)"
trap 'rm -f "$log"' EXIT

bash scripts/run-class-divergence-sweep.sh >"$log" 2>&1 ||
  die "the sweep failed: $(tail -3 "$log")"

count() { sed -n "s/^$1: *\([0-9]*\)\$/\1/p" "$log" | head -1; }
swept="$(count 'buffers swept')"
mismatches="$(count 'class mismatches')"
refused="$(sed -n 's/^refused by spec: *\([0-9]*\), by ref: *\([0-9]*\)$/\1 \2/p' "$log" | head -1)"

[ -n "$swept" ] || die "the sweep printed no buffer count: $(tail -3 "$log")"
[ -n "$mismatches" ] || die "the sweep printed no mismatch count: $(tail -3 "$log")"
[ -n "$refused" ] || die "the sweep printed no refusal counts: $(tail -3 "$log")"

[ "$swept" -ge "$floor" ] ||
  die "the family swept $swept buffers and this contract requires at least $floor — the family shrank"
[ "$mismatches" -eq 0 ] ||
  die "$mismatches buffer(s) got a different class from each reader; the sweep names them above"
set -- $refused
[ "$1" -gt 0 ] && [ "$2" -gt 0 ] ||
  die "the family refused $(printf '%s and %s' "$1" "$2") buffer(s) — agreement over a family where neither reader refuses is not evidence"

printf 'value_class_agreement: PASS\n'
printf '     %s buffers, %s class mismatches, refused %s by each reader\n' "$swept" "$mismatches" "$1"
