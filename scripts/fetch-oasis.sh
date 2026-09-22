#!/usr/bin/env bash
#
# Populate and verify the vendored OASIS AMQP 1.0 artifacts.
#
#   scripts/fetch-oasis.sh            # fetch any missing artifact, then verify all
#   scripts/fetch-oasis.sh --verify    # verify only; never touches the network
#
# Identity lives in `toolchain/sources.toml`; this script is the only thing that
# writes into `spec/oasis/`, and it refuses to continue on any size or hash
# mismatch. A copy that exists but does not match its pin is an error, not
# something to silently overwrite: the vendored bytes are what every clause id,
# disposition and vector citation refers to.

set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly sources="$root/toolchain/sources.toml"
readonly dest="$root/spec/oasis"

die() {
  printf '%s: %s\n' "${BASH_SOURCE[0]}" "$1" >&2
  exit 1
}

mode=fetch
case "${1-}" in
  --verify) mode=verify ;;
  "") ;;
  *) die "unknown argument '${1}'; usage: fetch-oasis.sh [--verify]" ;;
esac

[ -f "$sources" ] || die "missing pin record at $sources"
command -v python3 >/dev/null || die "python3 is required to read the pin record"
command -v sha256sum >/dev/null || die "sha256sum is required"

# Emit one `name<TAB>sha256<TAB>bytes` line per artifact, deterministically.
read_pins() {
  python3 - "$sources" <<'PY'
import sys, tomllib
with open(sys.argv[1], "rb") as handle:
    record = tomllib.load(handle)
for name in sorted(record["artifacts"]):
    entry = record["artifacts"][name]
    print(f"{name}\t{entry['sha256']}\t{entry['bytes']}")
PY
}

base_url() {
  python3 - "$sources" <<'PY'
import sys, tomllib
with open(sys.argv[1], "rb") as handle:
    print(tomllib.load(handle)["base_url"].rstrip("/"))
PY
}

verify_one() {
  local name="$1" want_sha="$2" want_bytes="$3" path="$dest/$1"
  [ -f "$path" ] || die "missing artifact $name (run without --verify to fetch it)"
  local have_bytes have_sha
  have_bytes="$(wc -c <"$path" | tr -d ' ')"
  [ "$have_bytes" = "$want_bytes" ] ||
    die "$name: size mismatch, expected $want_bytes bytes, found $have_bytes"
  have_sha="$(sha256sum "$path" | cut -d' ' -f1)"
  [ "$have_sha" = "$want_sha" ] ||
    die "$name: sha256 mismatch
  expected $want_sha
  found    $have_sha
The vendored copy is not the pinned artifact. Do not edit these files; restore
the pinned bytes deliberately rather than patching them."
  printf 'ok   %s (%s bytes)\n' "$name" "$want_bytes"
}

fetch_one() {
  local name="$1" want_sha="$2" want_bytes="$3" path="$dest/$1"
  local url; url="$(base_url)/$name"
  printf 'fetch %s\n' "$url"
  local tmp; tmp="$(mktemp "$dest/.fetch-XXXXXX")"
  trap 'rm -f "$tmp"' RETURN
  curl --proto '=https' --tlsv1.2 -sSfL -o "$tmp" "$url" ||
    die "$name: download failed from $url"
  local have_sha have_bytes
  have_sha="$(sha256sum "$tmp" | cut -d' ' -f1)"
  have_bytes="$(wc -c <"$tmp" | tr -d ' ')"
  [ "$have_sha" = "$want_sha" ] ||
    die "$name: downloaded artifact does not match the pin
  expected $want_sha
  found    $have_sha"
  mv -f "$tmp" "$path"
  printf 'ok   %s (%s bytes)\n' "$name" "$have_bytes"
}

mkdir -p "$dest"
checked=0
while IFS=$'\t' read -r name sha bytes; do
  [ -n "$name" ] || continue
  checked=$((checked + 1))
  if [ "$mode" = verify ]; then
    verify_one "$name" "$sha" "$bytes"
  elif [ -f "$dest/$name" ]; then
    verify_one "$name" "$sha" "$bytes"
  else
    fetch_one "$name" "$sha" "$bytes"
  fi
done < <(read_pins)

[ "$checked" -gt 0 ] || die "pin record lists no artifacts"
printf '%s: %d artifact(s) verified against %s\n' "${mode}" "$checked" \
  "${sources#"$root"/}"
