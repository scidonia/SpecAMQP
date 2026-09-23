#!/usr/bin/env bash
#
# The class-divergence sweep: run a generated family of buffers through both value readers
# and compare the reason class each one names.
#
#   scripts/run-class-divergence-sweep.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. the value layer's two readers both build and both answer, since the sweep calls each
#      of them on every buffer;
#   2. every buffer of the family gets the same class from the specification's reader and
#      from the reference's; a buffer whose two classes differ is named, with both classes,
#      and the script fails;
#   3. the family is non-vacuous in the way that matters here: it must refuse as well as
#      accept, and the number of buffers swept and the number each side refused are
#      printed, so a family that shrank is visible rather than silently weaker. The floor
#      on that count is the contract's to require
#      (`tests/contracts/value_class_agreement.sh`), because a check and its acceptance
#      threshold are different decisions.
#
# The family and the comparison live in `scripts/class-divergence-sweep.lean`, next to each
# other so that reading one is reading the other; this script is the driver that runs that
# program in the pinned environment and turns its exit status into this one.
#
# Runs offline; writes nothing.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly sweep="$root/scripts/class-divergence-sweep.lean"

die() { printf 'run-class-divergence-sweep: FAIL: %s\n' "$1" >&2; exit 1; }
note() { printf 'ok   %s\n' "$1"; }

command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"
[[ -f "$sweep" ]] || die "missing $sweep"

( cd "$root/lean" && LAKE_NO_CACHE=1 lake build Spec.Codec Ref.Value Ref.Frame ) >/dev/null 2>&1 ||
  die "building the two value readers failed"

out="$(cd "$root/lean" && LAKE_NO_CACHE=1 lake env lean --run "$sweep" 2>&1)" ||
  die "the sweep found a class divergence (its output names the buffers)
$out"

printf '%s\n' "$out"
grep -q '^class mismatches: 0$' <<<"$out" ||
  die "the sweep's own count disagrees with its exit status"
grep -q '^refused by spec: 0, by ref: 0$' <<<"$out" &&
  die "the family refused nothing on either side, so the comparison is vacuous"
note "both value readers name the same class for every buffer swept"

printf 'run-class-divergence-sweep: PASS\n'
