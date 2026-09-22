#!/usr/bin/env bash
#
# S0 contract: the pinned Lean environment resolves offline and is not drifted.
#
#   tests/contracts/s0_lean_environment.sh        # inside the `spec` shell
#
# Observable contract:
#
#   1. the toolchain on `PATH` is the pinned Lean, and the project's
#      `lean-toolchain` agrees with both this repository's flake and TemperMint's
#      pin record, so the specification composes with downstream proof work;
#   2. mathlib is pinned to the same revision as TemperMint's flake, so a module
#      proved here can be required there;
#   3. the project resolves its mathlib closure from the provisioned, gitignored
#      `lean/.lake` and builds the generated modules with the remote cache
#      disabled;
#   4. a probe module importing the specification's mathlib surface compiles
#      offline, which is what every later `Spec` module depends on.
#
# Must run inside the pinned shell: `nix develop .#spec --command bash
# tests/contracts/s0_lean_environment.sh`.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
readonly upstream="${SPECAMQP_TEMPERMINT_ROOT:-$(cd "$root/.." && pwd)/TemperMint}"

die() {
  printf 's0_lean_environment: FAIL: %s\n' "$1" >&2
  exit 1
}

note() { printf 'ok   %s\n' "$1"; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

command -v lean >/dev/null || die "lean is not on PATH: run inside \`nix develop .#spec\`"
command -v lake >/dev/null || die "lake is not on PATH: run inside \`nix develop .#spec\`"

# 1. Toolchain identity -----------------------------------------------------
lean_version="$(lean --version 2>&1 | head -1)"
case "$lean_version" in
  *"4.31.0"*) note "lean on PATH is $lean_version" ;;
  *) die "lean is not the pinned 4.31.0: $lean_version" ;;
esac

readonly toolchain_file="$root/lean/lean-toolchain"
[ -f "$toolchain_file" ] || die "missing lean/lean-toolchain"
toolchain="$(tr -d '[:space:]' <"$toolchain_file")"
[ "$toolchain" = "leanprover/lean4:v4.31.0" ] ||
  die "lean/lean-toolchain is '$toolchain', expected 'leanprover/lean4:v4.31.0'"
[ "${SPECAMQP_LEAN_TOOLCHAIN:-}" = "$toolchain" ] ||
  die "the shell exposes SPECAMQP_LEAN_TOOLCHAIN='${SPECAMQP_LEAN_TOOLCHAIN:-}' but the project pins '$toolchain'"
note "project toolchain matches the shell: $toolchain"

if [ -f "$upstream/toolchain/pins.toml" ]; then
  upstream_toolchain="$(
    python3 - "$upstream/toolchain/pins.toml" <<'PY'
import sys, tomllib
with open(sys.argv[1], "rb") as handle:
    print(tomllib.load(handle)["lean"]["toolchain"])
PY
  )"
  [ "$upstream_toolchain" = "$toolchain" ] ||
    die "TemperMint pins '$upstream_toolchain' but this project pins '$toolchain'"
  note "TemperMint's pin record agrees: $upstream_toolchain"
else
  printf 'skip TemperMint pin record: %s not present\n' "$upstream/toolchain/pins.toml"
fi

# 2. mathlib revision agreement ---------------------------------------------
readonly our_mathlib="$(
  sed -n 's#.*mathlib4/\([0-9a-f]\{40\}\).*#\1#p' "$root/flake.nix" | head -1
)"
[ -n "$our_mathlib" ] || die "cannot read the mathlib revision from flake.nix"
if [ -f "$upstream/flake.nix" ]; then
  upstream_mathlib="$(sed -n 's#.*mathlib4/\([0-9a-f]\{40\}\).*#\1#p' "$upstream/flake.nix" | head -1)"
  [ "$upstream_mathlib" = "$our_mathlib" ] ||
    die "mathlib drift: this project pins $our_mathlib, TemperMint pins $upstream_mathlib"
  note "mathlib revision matches TemperMint: ${our_mathlib:0:12}"
else
  printf 'skip TemperMint flake comparison: %s/flake.nix not present\n' "$upstream"
fi

# 3. Offline resolution and generated modules -------------------------------
readonly lake_dir="$root/lean/.lake"
[ -d "$lake_dir/packages/mathlib" ] ||
  die "lean/.lake/packages/mathlib is missing: the shell did not provision the workspace"
[ -f "$root/lean/lake-manifest.json" ] || die "missing lean/lake-manifest.json"

# The committed manifest is the resolution record the prewarm was built with.
# If a pin changes, the prewarmed workspace's manifest changes with it and this
# check fails, rather than letting the project silently resolve against a
# different closure than the one it was compiled with.
if [ -f "$lake_dir/workspace/lake-manifest.json" ]; then
  cat >"$tmp/manifest_check.py" <<'PY'
import json, sys
committed = json.load(open(sys.argv[1]))
prewarm = json.load(open(sys.argv[2]))

def shape(manifest):
    return sorted((entry["name"], entry["type"], entry.get("rev")) for entry in manifest["packages"])

problems = []
if committed.get("name") != prewarm.get("name"):
    problems.append(f"package name: committed {committed.get('name')}, prewarm {prewarm.get('name')}")
if shape(committed) != shape(prewarm):
    problems.append(f"package set differs: committed {shape(committed)}, prewarm {shape(prewarm)}")
for problem in problems:
    print(f"  manifest: {problem}")
raise SystemExit(1 if problems else 0)
PY
  python3 "$tmp/manifest_check.py" "$root/lean/lake-manifest.json" \
    "$lake_dir/workspace/lake-manifest.json" ||
    die "lean/lake-manifest.json has drifted from the prewarmed workspace's resolution record"
  note "committed lake-manifest.json matches the prewarmed resolution record"
else
  printf 'skip manifest drift check: %s/workspace/lake-manifest.json not provisioned\n' "$lake_dir"
fi

(
  cd "$root/lean"
  LAKE_NO_CACHE=1 lake build Generated.Oasis.Constants Generated.Oasis.Types \
    Generated.Oasis.Fields Generated.Oasis.Encodings Generated.Oasis.Choices
) >"$tmp/build.log" 2>&1 || die "building the generated modules failed: $(tail -5 "$tmp/build.log")"
note "generated modules build against the provisioned closure (remote cache disabled)"

# 4. The specification's mathlib surface resolves offline -------------------
# These imports mirror the `Prewarm` module in `flake.nix`: if the prewarm list
# loses a module the specification needs, this probe fails rather than letting
# the gap surface later as a slow lazy build.
cat >"$tmp/Probe.lean" <<'PROBE'
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Basic

/-- The aggregation bound the specification's later arguments rely on: the sum of
a filtered list is bounded by the sum of the whole list, over integers under a
non-negativity hypothesis. -/
example (values : List Int) (nonneg : ∀ value ∈ values, 0 ≤ value) :
    (values.filter (fun value => 0 ≤ value)).sum ≤ values.sum :=
  List.Sublist.sum_le_sum (List.filter_sublist (p := fun value : Int => 0 ≤ value)) nonneg
PROBE
(
  cd "$root/lean"
  LAKE_NO_CACHE=1 lake env lean "$tmp/Probe.lean"
) >"$tmp/probe.log" 2>&1 || die "mathlib probe failed: $(tail -5 "$tmp/probe.log")"
note "mathlib probe compiles offline against the prewarmed closure"

printf 's0_lean_environment: PASS\n'
