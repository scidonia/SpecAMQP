#!/usr/bin/env bash
#
# R1's evidence: the transport shell, exercised by two processes over loopback, and
# the controls that make that evidence attackable.
#
# `PLAN.md` §23.1's first rung exists to answer one question — does the `@[extern]`
# boundary and its C shim deliver the octets it is given, in order, in full — and the
# only honest way to answer it is to run two Lean binaries and compare bytes.
#
# Run inside the pinned shell, from the repository root:
#
#   shell bash scripts/run-transport-loopback.sh                    # the four clean cases
#   shell bash scripts/run-transport-loopback.sh --mutant <name>    # plant a fault, expect it caught
#
# ## The clean run
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
# ## The controls
#
# The passing run above proves nothing on its own: a harness that has never detected
# a planted fault cannot distinguish a correct shim from one it fails to test. So the
# same cases run again against `amqp-loopback-control-{server,client}`, which are the
# same Lean binaries linked against `scripts/loopback/mutants/shim_controls.c` — the
# real shim with wrappers that plant one fault, chosen by `SPECAMQP_SHIM_CONTROL`:
#
#   --mutant truncating-recv   every read loses one octet          expect: caught
#   --mutant reordering-recv   the first two octets of every read swap  expect: caught
#   --mutant short-send        every write offers at most 1024 octets   expect: *passes*
#
# `short-send` is the one control whose expected result is success, and it is here
# because it is the only way to exercise `Wire.sendAll`'s loop: a positive short write
# is legal, and Linux's blocking `send` never produces one on its own. It fails if the
# loop drops the remainder, and the send-call counts are the evidence that the loop ran
# — hundreds of calls where the clean run makes one.
#
# In control mode the exit status means "the control behaved as documented": zero when
# every case behaved as that control's reach predicts, non-zero when one escaped.
#
# The predictions differ per control, and the difference is a fact about the control
# rather than a concession. Both `recv` controls act on every read — and the eight-octet
# length header is a read, on every case, whatever the dialogue carries — so neither is
# confined to the payload. The truncation shortens that header, which breaks the dialogue
# before it starts; the reordering swaps its first two octets, and for the empty dialogue
# those are both zero, so that one case genuinely cannot be caught and is asserted to
# *pass* instead. Calling it a detection would be a vacuous pass of exactly the kind this
# rung exists to prevent; calling it a failure would be a harness that cannot tell one
# control's reach from another's.
#
# Nothing here contacts a network service, a clock or a random source: ports are fixed
# per case, the payload is generated, and the only ordering is process start-up.

set -u

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root/lean"

# Evidence builds set LAKE_NO_CACHE=1 (see AGENTS.md): without it the build may consult
# a remote cache and rest on artifacts that arrived over the wire.
export LAKE_NO_CACHE="${LAKE_NO_CACHE:-1}"

usage() {
  printf 'usage: %s [--mutant truncating-recv|reordering-recv|short-send]\n' "$0" >&2
}

mutant=""
case "${1:-}" in
  "") ;;
  -h | --help)
    usage
    exit 0
    ;;
  --mutant)
    mutant="${2:-}"
    if [ -z "$mutant" ]; then
      usage
      exit 2
    fi
    ;;
  *)
    printf 'unknown argument: %s\n' "$1" >&2
    usage
    exit 2
    ;;
esac

case "$mutant" in
  "") server_exe=amqp-loopback-server client_exe=amqp-loopback-client ;;
  truncating-recv | reordering-recv | short-send)
    server_exe=amqp-loopback-control-server
    client_exe=amqp-loopback-control-client
    export SPECAMQP_SHIM_CONTROL="$mutant"
    ;;
  *)
    printf 'unknown control: %s\n' "$mutant" >&2
    usage
    exit 2
    ;;
esac

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

if ! command -v timeout >/dev/null; then
  echo "loopback: 'timeout' is required to bound a hung dialogue" >&2
  exit 1
fi

# The cap the short-send control applies, in octets; kept in step with
# CONTROL_SHORT_SEND_CAP in scripts/loopback/mutants/shim_controls.c.
short_send_cap=1024

failures=0
escaped=0

check() {
  description=$1
  if [ "$2" = 0 ]; then
    printf 'ok   %s\n' "$description"
  else
    printf 'FAIL %s\n' "$description"
    failures=$((failures + 1))
  fi
}

# Reported separately from `check`: in control mode a case that was *supposed* to fail
# must not also increment the failure count that decides the run's status.
control_check() {
  description=$1
  if [ "$2" = 0 ]; then
    printf 'caught  %s\n' "$description"
  else
    printf 'ESCAPED %s\n' "$description"
    escaped=$((escaped + 1))
  fi
}

# For a control whose expected result is success rather than detection: same bookkeeping,
# honest wording. The status argument defaults to 0 so a call site that has nothing to
# report but success does not have to pass one.
documented() {
  description=$1
  if [ "${2:-0}" = 0 ]; then
    printf 'ok      %s\n' "$description"
  else
    printf 'ESCAPED %s\n' "$description"
    escaped=$((escaped + 1))
  fi
}

# Globals set by run_case and read by the caller that knows the expectation.
case_failed=0
case_named=0

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
  printf '$ lake exe %s %s %s\n' "$server_exe" "$port" "$chunk"

  timeout 120 lake exe "$server_exe" "$port" "$chunk" >"$fifo" 2>&1 &
  server_pid=$!

  # Holding the read end open lets the readiness line be read and the rest be drained
  # afterwards, without reopening a FIFO that has already reached end of file.
  exec 3<"$fifo"
  IFS= read -r readiness <&3
  printf '%s\n' "$readiness"

  printf '$ lake exe %s %s %s %s\n' "$client_exe" "$port" "$octets" "$client_chunk"
  client_out=$(timeout 120 lake exe "$client_exe" "$port" "$octets" "$client_chunk" 2>&1)
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

  case_failed=0
  [ "$server_status" = 0 ] || case_failed=1
  [ "$client_status" = 0 ] || case_failed=1

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
      case_failed=1
    fi
    client_least=$(( (octets + client_chunk - 1) / client_chunk ))
    echoed=$(sed -n "s/^client: received $octets octets in \([0-9]*\) recv call(s)$/\1/p" "$client_log")
    if [ -n "$echoed" ] && [ "$echoed" -ge "$client_least" ]; then
      check "client's $octets echoed octets spanned $echoed recv calls (at least $client_least)" 0
    else
      check "client's $octets echoed octets spanned at least $client_least recv calls (saw '${echoed:-none}')" 1
      case_failed=1
    fi
  fi

  # A failing case is only useful evidence if it says *why*. These are the diagnostics
  # the harness and the shim produce, each naming the place rather than the fact: a
  # differing octet, a short transfer, a length disagreement, octets after the
  # dialogue, or the syscall that failed.
  if grep -qE 'MISMATCH|peer closed after|length differs|accepted no octets|returned [0-9]+ octets for a request|peer sent [0-9]+ octets after the dialogue|transport shim:' \
    "$log" "$client_log"; then
    case_named=1
  else
    case_named=0
  fi
}

# The four cases, with the read sizes the clean run uses.
run_all_cases() {
  run_case single 47311 64 64 3
  run_case multi 47312 300000 4096 4093
  run_case fragmented 47313 20000 7 5
  run_case empty 47314 0 1024 1024
}

printf 'building %s and %s\n' "$server_exe" "$client_exe"
lake build "$server_exe" "$client_exe" 2>&1 | tail -3

if [ -z "$mutant" ]; then
  run_all_cases
  if [ "$failures" -eq 0 ]; then
    printf '\nloopback: all cases passed\n'
    exit 0
  fi
  printf '\nloopback: %s check(s) failed\n' "$failures"
  exit 1
fi

printf '\n# control mode: SPECAMQP_SHIM_CONTROL=%s\n' "$mutant"
printf '# The binaries under test are linked against scripts/loopback/mutants/shim_controls.c.\n'
printf '# FAILs below are the control being caught, which is the expected result.\n'

# Each control reaches what it reaches, and the difference is stated rather than
# smoothed over. Both `recv` controls act on every read, and the length header is a
# read — so neither is limited to the payload. What differs is whether the header can
# be corrupted: the truncation shortens it, which is visible; the reordering swaps its
# first two octets, which for the empty dialogue are both zero and therefore unchanged.
# That is why the empty case is caught by one control and not the other, and the
# expectation below says so instead of asserting a symmetry that does not exist.

# `$1` label, `$2` port, `$3` octets, `$4` server chunk, `$5` client chunk.
control_case_caught() {
  label=$1
  port=$2
  octets=$3
  chunk=$4
  client_chunk=$5
  run_case "$label" "$port" "$octets" "$chunk" "$client_chunk"
  if [ "$case_failed" = 1 ] && [ "$case_named" = 1 ]; then
    control_check "case $label ($octets octets) was caught, with a named diagnostic" 0
  elif [ "$case_failed" = 1 ]; then
    control_check "case $label ($octets octets) failed without a named diagnostic" 1
  else
    control_check "case $label ($octets octets) escaped: the run passed" 1
  fi
}

# `$1` label, `$2` port, `$3` octets, `$4` server chunk, `$5` client chunk, `$6` why.
control_case_still_passes() {
  label=$1
  port=$2
  octets=$3
  chunk=$4
  client_chunk=$5
  reason=$6
  run_case "$label" "$port" "$octets" "$chunk" "$client_chunk"
  if [ "$case_failed" = 0 ]; then
    documented "case $label passes, and cannot be caught: $reason"
  else
    documented "case $label failed although it cannot be caught: $reason" 1
  fi
}

if [ "$mutant" = "short-send" ]; then
  # Expected: every case passes, with the loop making many calls where the clean run
  # makes one. The count is the assertion — a loop that dropped the remainder would
  # either fail to deliver the payload or report a single call.
  short_send_case() {
    label=$1
    port=$2
    octets=$3
    chunk=$4
    client_chunk=$5
    run_case "$label" "$port" "$octets" "$chunk" "$client_chunk"
    if [ "$case_failed" = 1 ]; then
      control_check "case $label ($octets octets) failed under short-send, which must not happen" 1
      return
    fi
    if [ "$octets" -le "$short_send_cap" ]; then
      printf 'n/a     case %s: %s octets is within one %s-octet write, so this control cannot bite\n' \
        "$label" "$octets" "$short_send_cap"
      return
    fi
    server_least=$(( (octets + short_send_cap - 1) / short_send_cap ))
    client_least=$(( 1 + (octets + short_send_cap - 1) / short_send_cap ))
    server_sends=$(sed -n "s/^server: echoed $octets octets in \([0-9]*\) send call(s)$/\1/p" "$log")
    client_sends=$(sed -n "s/^client: sent $((octets + 8)) octets in \([0-9]*\) send call(s)$/\1/p" "$client_log")
    printf '     server echoed in %s send call(s) (at least %s), client sent in %s (at least %s)\n' \
      "${server_sends:-none}" "$server_least" "${client_sends:-none}" "$client_least"
    if [ -n "$server_sends" ] && [ "$server_sends" -ge "$server_least" ] &&
      [ -n "$client_sends" ] && [ "$client_sends" -ge "$client_least" ]; then
      documented "case $label ($octets octets) completed through the short-write loop"
    else
      documented "case $label ($octets octets) did not show the short-write loop running" 1
    fi
  }
  short_send_case single 47311 64 64 3
  short_send_case multi 47312 300000 4096 4093
  short_send_case fragmented 47313 20000 7 5
  short_send_case empty 47314 0 1024 1024
elif [ "$mutant" = "truncating-recv" ]; then
  # Every read loses an octet, and the length header is a read (always exactly eight
  # octets, whatever the dialogue carries), so all four cases are caught — the empty
  # dialogue included, because its header is what gets shortened.
  control_case_caught single 47311 64 64 3
  control_case_caught multi 47312 300000 4096 4093
  control_case_caught fragmented 47313 20000 7 5
  control_case_caught empty 47314 0 1024 1024
else
  # `reordering-recv` also acts on the header, but cannot corrupt it here: the empty
  # dialogue's header is eight zero octets, so swapping its first two changes nothing.
  control_case_caught single 47311 64 64 3
  control_case_caught multi 47312 300000 4096 4093
  control_case_caught fragmented 47313 20000 7 5
  control_case_still_passes empty 47314 0 1024 1024 \
    "its header is eight zero octets, and swapping two of them is not a change"
fi

printf '\n'
if [ "$escaped" -eq 0 ]; then
  printf 'loopback: control %s behaved as documented in every case\n' "$mutant"
  exit 0
fi
printf 'loopback: control %s escaped in %s case(s)\n' "$mutant" "$escaped"
exit 1
