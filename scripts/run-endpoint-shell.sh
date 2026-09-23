#!/usr/bin/env bash
#
# R2's shell evidence: the shipped endpoint, driven over the socket.
#
# `Shell/Driver.lean` states three obligations that no proof in this tree covers — it loops on a short
# read, it writes exactly what the core returns and all of it, and it treats `recv`'s `none` as the peer's
# orderly close — and this script is the tier that *forces* them rather than arguing them. R1's runner is
# the shape it follows: two Lean binaries over loopback, a readiness line that is read rather than polled,
# and the exit statuses as the verdict.
#
#   shell bash scripts/run-endpoint-shell.sh
#
# ## The two cases, and what each one forces
#
# **open-close — a short read, and an orderly close.** Both processes are the shipped `amqp-endpoint`. The
# server's read size is 3 and the client's is 5, so the eight-octet protocol header cannot arrive in one
# read whichever way the kernel splits it: the server must see it in at least three reads and the client in
# at least two. The case asserts that both wrote the header, both answered the other's — which cannot
# happen unless the octets were reassembled across those reads — and that the server, which never finishes
# of its own accord, ended on `recv`'s `none` and said so. A shell that assumed one read is one frame, or
# that treated `none` as a fault, fails this case.
#
# **short-write — a write the kernel accepts in pieces.** Both sides are `amqp-endpoint-probe`, the same
# shell with a harness application (`scripts/endpoint/EndpointProbe/Client.lean`): the server declares a
# `max-frame-size` large enough for the frame, the client then sends a ~3 kB `open`, and the probe is linked
# against R1's control shim with `SPECAMQP_SHIM_CONTROL=short-send`, which caps every `send` at 1024
# octets. So `sendAll` must loop, and the server must read the frame whole: the case asserts the write was
# reported as several `send` calls and that the server *accepted* the frame, which it can only do after
# delimiting one of the size the header declares. A shell that wrote only the first chunk leaves the server
# waiting for the rest, and the case times out rather than passing. (The declaration is not decoration: the
# core refuses to *send* a frame above the peer's a priori limit, `MIN-MAX-FRAME-SIZE`, 512.)
#
# Nothing here contacts a network service, a clock or a random source: both processes are local binaries,
# and the only ordering is process start-up.
#
# ## Ports: why a scan, and why it is bounded
#
# The port range starts at a value derived from this script's process id, and the server **scans forward
# until it binds**, printing the port it took. The scan exists because the derivation is not enough on its
# own: in the gate suite's documented order (`r1_transport_shell` sorts immediately before
# `r2_endpoint_shell`) R1's servers are still alive inside their own `timeout`s, so a pid-derived port
# collides *systematically* with the previous gate rather than rarely. The scan is bounded, deterministic
# and prints what it chose, so a recorded run stays reproducible; `SPECAMQP_ENDPOINT_PORT_BASE` pins where
# the scan starts and `SPECAMQP_ENDPOINT_PORT_ATTEMPTS` bounds it.
#
# A case whose server could not bind any port in the range never tested the shell: it is reported as
# INVALID and cannot satisfy anything. That is the honest "this run tested nothing", and it is what turned
# the collision above into a named failure rather than a flaky pass.

set -u

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root/lean"

# Evidence builds set LAKE_NO_CACHE=1 (see AGENTS.md).
export LAKE_NO_CACHE="${LAKE_NO_CACHE:-1}"

if ! command -v timeout >/dev/null; then
  echo "endpoint-shell: 'timeout' is required to bound a hung dialogue" >&2
  exit 1
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

port_base="${SPECAMQP_ENDPOINT_PORT_BASE:-$((48100 + ($$ % 300)))}"
port_attempts="${SPECAMQP_ENDPOINT_PORT_ATTEMPTS:-40}"

failures=0
invalid_runs=0

# Set by `start_endpoint_server` on success: the server's pid, its FIFO (still open on fd 3), its log, the
# port it took, and the readiness line it printed.
srv_pid=""
srv_fifo=""
srv_log=""
port=""
readiness=""

check() {
  if [ "$2" = 0 ]; then
    printf 'ok   %s\n' "$1"
  else
    printf 'FAIL %s\n' "$1"
    failures=$((failures + 1))
  fi
}

# `has <file> <pattern> <description>`: the file mentions the pattern.
has() {
  if grep -qE "$2" "$1"; then check "$3" 0; else check "$3 (not found in $(basename "$1"))" 1; fi
}

# Start the shipped server on the first port in `[first, first + port_attempts)` that it can bind, with a
# FIFO for its readiness line so that a server which blocks before flushing hangs this script instead of
# passing it. Returns non-zero when no port in the range binds (the caller reports INVALID).
start_endpoint_server() {
  label=$1
  first=$2
  read_size=$3
  exe=$4
  attempt=0
  while [ "$attempt" -lt "$port_attempts" ]; do
    port=$((first + attempt))
    srv_fifo="$work/$label.$attempt.fifo"
    srv_log="$work/$label.$attempt.log"
    mkfifo "$srv_fifo"
    printf '$ lake exe %s server %s %s\n' "$exe" "$port" "$read_size"
    timeout 120 lake exe "$exe" server "$port" "$read_size" >"$srv_fifo" 2>&1 &
    srv_pid=$!
    exec 3<"$srv_fifo"
    # the readiness line is the *server's own announcement*, not merely a first line: a server that fails
    # to bind prints the shim's error and exits, and reading that as readiness would carry a dead server
    # into the case and turn a port collision into ten confusing assertion failures
    if IFS= read -r readiness <&3 && printf '%s' "$readiness" | grep -q 'listening port='; then
      printf '%s\n' "$readiness"
      printf '     (took port %s)\n' "$port"
      return 0
    fi
    exec 3<&-
    wait "$srv_pid" 2>/dev/null
    printf '     port %s did not bind: %s\n' "$port" "${readiness:-the server exited without a line}"
    attempt=$((attempt + 1))
  done
  return 1
}

# Drain the server's remaining output into its log and close the FIFO. The readiness line is put back in
# front of it so the log reads as one transcript.
collect() {
  { printf '%s\n' "$readiness"; cat <&3; } >"$srv_log"
  exec 3<&-
}

# ---------------------------------------------------------------- case 1: short reads, orderly close

printf '\n=== case open-close: header split across reads, then the peer closes ===\n'
if start_endpoint_server open-close "$port_base" 3 amqp-endpoint; then
  printf '$ lake exe amqp-endpoint client %s 5\n' "$port"
  timeout 120 lake exe amqp-endpoint client "$port" 5 >"$work/open-close.client.log" 2>&1
  cli_status=$?
  cli="$work/open-close.client.log"
  collect
  wait "$srv_pid"
  srv_status=$?

  printf -- '--- server\n'; cat "$srv_log"
  printf -- '--- client\n'; cat "$cli"

  check "server exit status is 0 (saw $srv_status)" "$([ "$srv_status" = 0 ] && echo 0 || echo 1)"
  check "client exit status is 0 (saw $cli_status)" "$([ "$cli_status" = 0 ] && echo 0 || echo 1)"
  has "$srv_log" 'took HDR_SENT' 'server wrote its own header'
  has "$srv_log" 'took HDR_EXCH' 'server reassembled the header across 3-octet reads'
  has "$cli" 'took HDR_EXCH' 'client reassembled the header across 5-octet reads'
  has "$srv_log" 'the peer closed the stream \(orderly\)' 'server ended on the orderly close, not on a fault'
else
  printf 'INVALID open-close: no port in [%s, %s) could be bound, so nothing was tested\n' \
    "$port_base" "$((port_base + port_attempts))"
  invalid_runs=$((invalid_runs + 1))
fi

# ---------------------------------------------------------------- case 2: a short write, forced

printf '\n=== case short-write: a ~3 kB open in 1024-octet sends ===\n'
if start_endpoint_server short-write "$((port_base + 100))" 7 amqp-endpoint-probe; then
  printf '$ SPECAMQP_SHIM_CONTROL=short-send lake exe amqp-endpoint-probe client %s 13\n' "$port"
  SPECAMQP_SHIM_CONTROL=short-send timeout 120 lake exe amqp-endpoint-probe client "$port" 13 \
    >"$work/short-write.client.log" 2>&1
  cli_status=$?
  cli="$work/short-write.client.log"
  collect
  wait "$srv_pid"
  srv_status=$?

  printf -- '--- server\n'; cat "$srv_log"
  printf -- '--- client\n'; cat "$cli"

  check "server exit status is 0 (saw $srv_status)" "$([ "$srv_status" = 0 ] && echo 0 || echo 1)"
  check "client exit status is 0 (saw $cli_status)" "$([ "$cli_status" = 0 ] && echo 0 || echo 1)"
  has "$cli" 'wrote [0-9]+ octets in [0-9]+ send call\(s\)' 'the write loop reported a write the kernel took in pieces'
  has "$srv_log" 'took OPEN_SENT' 'server declared limits large enough for the frame'
  has "$srv_log" 'took OPENED' 'server read the looped write whole and accepted it'
  has "$srv_log" 'the peer closed the stream \(orderly\)' 'server ended on the orderly close'
  # the client is the one that closes here (its application is finished), so it has no orderly-close line:
  # what its log proves is that it ended in the state the accepted frame leaves it in
  has "$cli" 'the connection ended in OPENED' 'client ended where the accepted frame left it'
else
  printf 'INVALID short-write: no port in [%s, %s) could be bound, so nothing was tested\n' \
    "$((port_base + 100))" "$((port_base + 100 + port_attempts))"
  invalid_runs=$((invalid_runs + 1))
fi

printf '\n'
if [ "$invalid_runs" != 0 ]; then
  printf 'endpoint-shell: %s case(s) never tested the shell (no port could be bound)\n' "$invalid_runs"
fi
if [ "$failures" = 0 ] && [ "$invalid_runs" = 0 ]; then
  printf 'endpoint-shell: PASS\n'
  exit 0
fi
printf 'endpoint-shell: FAIL (%s failed assertion(s), %s invalid case(s))\n' "$failures" "$invalid_runs"
exit 1
