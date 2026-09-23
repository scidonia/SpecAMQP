#!/usr/bin/env bash
#
# R1's evidence: the transport shell, exercised by two processes over loopback.
#
# `PLAN.md` §23.1's first rung exists to answer one question — does the `@[extern]`
# boundary and its C shim deliver the octets it is given, in order, in full — and
# the only honest way to answer it is to run two Lean binaries and compare bytes.
# This script is that run: it starts `amqp-loopback-server`, waits for its readiness
# line, runs `amqp-loopback-client` against it, and checks what both reported.
#
# Run inside the pinned shell, from the repository root:
#
#   shell bash scripts/run-transport-loopback.sh
#
# What each case asserts, and why each is here:
#
#   * the client's octet-for-octet comparison says MATCH — the payload is
#     position-dependent (`i % 251`), so a reordered or truncated transfer cannot
#     pass it by accident;
#   * both processes exit zero, so the verdict is the process's rather than a line
#     someone has to read;
#   * the server's payload arrived in at least `ceil(octets / chunk)` `recv` calls.
#     This is the multi-buffer assertion: `recv` promises at most the octets asked
#     for, so a shim that quietly returned more, or a loop that asked once and
#     stopped, would show up as fewer calls. The `chunk 7` case drives that into the
#     thousands, which is where a reordering shim cannot hide;
#   * the same for the client's read of the echo, measured against *its* read size —
#     which the runner sets differently from the server's on purpose. A shim that
#     reorders within each read can cancel itself out when both directions happen to
#     read in identical windows; that is not hypothetical, it is what an early
#     planted control did, and differing read sizes are what removed the coincidence;
#   * the server saw the peer's orderly close (`none`, not an error), which is the
#     other half of the boundary's contract.
#
# The readiness line is *read*, not polled: the server's stdout goes through a FIFO
# and this script blocks on it, so an unflushed readiness line hangs the case instead
# of passing it — that is the buffering failure's assertion, not a timeout's.
#
# A failure prints what was seen and exits non-zero. Nothing here contacts a network
# service, a clock or a random source: ports are fixed per case, the payload is
# generated, and the only ordering is process start-up.

set -u

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root/lean"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

if ! command -v timeout >/dev/null; then
  echo "loopback: 'timeout' is required to bound a hung dialogue" >&2
  exit 1
fi

failures=0

check() {
  description=$1
  if [ "$2" = 0 ]; then
    printf 'ok   %s\n' "$description"
  else
    printf 'FAIL %s\n' "$description"
    failures=$((failures + 1))
  fi
}

# One dialogue. `$1` label, `$2` port, `$3` payload octets, `$4` the server's read
# size, `$5` the client's. The two sizes differ on purpose: a shim that reorders
# *within* each read can cancel itself out when both directions happen to read in
# identical windows, and giving the two processes different windows removes that
# coincidence from the evidence.
run_case() {
  label=$1
  port=$2
  octets=$3
  chunk=$4
  client_chunk=$5
  fifo="$work/$label.fifo"
  log="$work/$label.log"
  client_log="$work/$label.client.log"
  mkfifo "$fifo"

  printf '\n=== case %s: %s octets, server chunk %s, client chunk %s, port %s ===\n' \
    "$label" "$octets" "$chunk" "$client_chunk" "$port"
  printf '$ lake exe amqp-loopback-server %s %s\n' "$port" "$chunk"

  timeout 120 lake exe amqp-loopback-server "$port" "$chunk" >"$fifo" 2>&1 &
  server_pid=$!

  # Holding the read end open lets the readiness line be read and the rest be drained
  # afterwards, without reopening a FIFO that has already reached end of file.
  exec 3<"$fifo"
  IFS= read -r readiness <&3
  printf '%s\n' "$readiness"

  printf '$ lake exe amqp-loopback-client %s %s %s\n' "$port" "$octets" "$client_chunk"
  client_out=$(timeout 120 lake exe amqp-loopback-client "$port" "$octets" "$client_chunk" 2>&1)
  client_status=$?
  printf '%s\n' "$client_out"
  printf '%s\n' "$client_out" >"$client_log"

  # Drain before waiting: if the server were blocked on a full pipe, waiting first
  # would deadlock. The bounded `timeout` above is what makes this terminate anyway.
  { printf '%s\n' "$readiness"; cat <&3; } >"$log"
  exec 3<&-
  wait "$server_pid"
  server_status=$?
  cat "$log"

  check "server exit status is 0 (saw $server_status)" \
    "$([ "$server_status" = 0 ] && echo 0 || echo 1)"
  check "client exit status is 0 (saw $client_status)" \
    "$([ "$client_status" = 0 ] && echo 0 || echo 1)"
  check "client reported an octet-for-octet MATCH" \
    "$(grep -q 'byte-for-byte comparison: MATCH' "$client_log" && echo 0 || echo 1)"
  check "server echoed every announced octet" \
    "$(grep -q "server: echoed $octets octets" "$log" && echo 0 || echo 1)"
  check "server saw the peer's orderly close" \
    "$(grep -q 'peer closed the connection (orderly)' "$log" && echo 0 || echo 1)"

  if [ "$octets" -gt 0 ]; then
    # ceil(octets / chunk) reads is the fewest the boundary's contract permits, in
    # both directions: the server's read of the request, and the client's read of
    # the echo, each measured against its own read size.
    least=$(( (octets + chunk - 1) / chunk ))
    calls=$(sed -n "s/^server: received $octets octets in \([0-9]*\) recv call(s)$/\1/p" "$log")
    if [ -n "$calls" ] && [ "$calls" -ge "$least" ]; then
      check "server's $octets octets spanned $calls recv calls (at least $least)" 0
    else
      check "server's $octets octets spanned at least $least recv calls (saw '${calls:-none}')" 1
    fi
    client_least=$(( (octets + client_chunk - 1) / client_chunk ))
    echoed=$(sed -n "s/^client: received $octets octets in \([0-9]*\) recv call(s)$/\1/p" "$client_log")
    if [ -n "$echoed" ] && [ "$echoed" -ge "$client_least" ]; then
      check "client's $octets echoed octets spanned $echoed recv calls (at least $client_least)" 0
    else
      check "client's $octets echoed octets spanned at least $client_least recv calls (saw '${echoed:-none}')" 1
    fi
  fi
}

# The small case: one dialogue, and a read size that does not divide it evenly.
run_case single 47311 64 64 3
# The multi-buffer case the acceptance names: the payload cannot fit one read, and
# the echo's read size differs from the request's by three octets so that no
# within-read fault can cancel itself across the two directions.
run_case multi 47312 300000 4096 4093
# Extreme fragmentation: thousands of small reads, where a shim that reorders cannot
# hide behind the lengths.
run_case fragmented 47313 20000 7 5
# The empty dialogue, which the boundary's contract has to survive as well.
run_case empty 47314 0 1024 1024

printf '\n'
if [ "$failures" -eq 0 ]; then
  printf 'loopback: all cases passed\n'
  exit 0
fi
printf 'loopback: %s check(s) failed\n' "$failures"
exit 1
