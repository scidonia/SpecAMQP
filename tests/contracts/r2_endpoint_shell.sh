#!/usr/bin/env bash
# The shipped endpoint is driven over the socket, and the run is *forced* rather than merely green.
#
# `Shell/Driver.lean` states three obligations that no proof in this tree covers: that the shell loops on a
# short read, that it writes exactly what the core returns and all of it, and that it treats `recv`'s `none`
# as the peer's orderly close. `scripts/run-endpoint-shell.sh` is the tier that forces them; this file is
# the contract that says what a passing run has to have shown.
#
# Why the four descriptions below are pinned by wording, when this repository prefers not to pin log text:
# they are not incidental output, they are the *forcing conditions*. The read sizes are 3 and 5, so a shell
# that assumed one read is one frame cannot produce a reassembly line, and a run that stopped asserting
# reassembly would pass while testing that assumption's absence. The write loop's own report is the same
# thing on the write side: the shim caps `send` at 1024 octets, so a shell that wrote only the first chunk
# leaves the server waiting and the case times out rather than passing. Asserting that these four lines
# exist is asserting the run was non-vacuous, which is the one property the driver cannot assert about
# itself.
#
# The driver reports a case whose listener could not bind as INVALID and exits non-zero for it, so the
# "the port was busy" failure can never satisfy this gate. It does collide, though, and systematically rather
# than rarely: the driver derives its port base from its own pid, which cannot collide with itself but does
# collide with the *previous* gate in filename order, since `r1_transport_shell.sh` runs immediately before
# this one and leaves servers alive inside their timeouts. Measured once by running the suite in that order.
# The driver's own fix — try the next port on a bind failure, deterministically, and print which port it took
# — is owed; until it lands, a full-suite run reports this gate as INVALID and the reason is not the shell.

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"

die() { printf 'r2_endpoint_shell: FAIL: %s\n' "$1" >&2; exit 1; }

log="$(mktemp)"
trap 'rm -f "$log"' EXIT

if ! bash scripts/run-endpoint-shell.sh >"$log" 2>&1; then
  # INVALID gets its own message because it is a different failure from a failed assertion, and the
  # difference decides what to do next: a collision means the run never tested the shell and a re-run is
  # the right response, while a failed assertion means the shell is wrong. The driver cannot collide with
  # itself — its port base comes from its own process id — but it can collide with a previous run's
  # server still inside its `timeout`, which is what happened on this gate's first run.
  if grep -q '^INVALID' "$log"; then
    die "a case never tested the shell (port collision), so this run is not evidence: $(grep -m1 '^INVALID' "$log") — re-run"
  fi
  die "the driver failed: $(tail -5 "$log")"
fi
grep -q '^endpoint-shell: PASS' "$log" ||
  die "the driver exited zero without reporting PASS: $(tail -3 "$log")"

while IFS= read -r forcing; do
  grep -qF "$forcing" "$log" ||
    die "the run never asserted '$forcing' — the case passed without forcing what it claims"
done <<'FORCING'
server reassembled the peer's header across 3-octet reads
client reassembled the peer's header across 5-octet reads
the write loop reported a write the kernel took in pieces
server read the looped write whole and accepted it
FORCING

printf 'r2_endpoint_shell: PASS\n'
printf '     both cases forced: the header reassembled across 3- and 5-octet reads, a 3 kB frame written in 1024-octet sends\n'
