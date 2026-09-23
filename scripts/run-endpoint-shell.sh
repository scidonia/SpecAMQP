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
# **short-write — a write the kernel accepts in pieces.** The peer is `amqp-endpoint-probe`, the same shell
# with a harness application (`scripts/endpoint/EndpointProbe/Client.lean`) that asks it to send one `open`
# frame of about three kilobytes, linked against R1's control shim with `SPECAMQP_SHIM_CONTROL=short-send`,
# which caps every `send` at 1024 octets. So `sendAll` must loop at least three times, and the server must
# read the frame whole: the case asserts the server *refused* it for `limit`, which a reader reaches only
# after it has delimited a frame of the size the header declares. A shell that wrote only the first chunk
# leaves the server waiting for the rest, and the case times out rather than passing.
#
# Nothing here contacts a network service, a clock or a random source: both processes are local binaries,
# and the only ordering is process start-up.
#
# A case whose listener could not bind, or whose client could not connect, never tested the shell. It is
# reported as INVALID and cannot satisfy anything — the failure being caught would otherwise be "the port
# was busy", which is the vacuous pass this rung exists to prevent.

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

# Ports are derived from this script's own process id so that two concurrent runs cannot collide, and the
# base is printable so a run can be recorded. Pin it with SPECAMQP_ENDPOINT_PORT_BASE.
port_base="${SPECAMQP_ENDPOINT_PORT_BASE:-$((48100 + ($$ % 300)))}"

failures=0
invalid_runs=0

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

# A process's log, with its readiness line put back in front of it: the line is read from a FIFO so that a
# server that has not flushed it hangs this script instead of passing it.
collect() {
  readiness=$1
  fifo=$2
  log=$3
  { printf '%s\n' "$readiness"; cat <&3; } >"$log"
  exec 3<&-
}

valid_case() {
  if grep -qE 'Address already in use|Connection refused' "$@"; then
    invalid_runs=$((invalid_runs + 1))
    return 1
  fi
  return 0
}

# ---------------------------------------------------------------- case 1: short reads, orderly close

printf '\n=== case open-close: header split across reads, then the peer closes ===\n'
port="$port_base"
fifo="$work/open-close.fifo"
srv="$work/open-close.server.log"
cli="$work/open-close.client.log"
mkfifo "$fifo"

printf '$ lake exe amqp-endpoint server %s 3\n' "$port"
timeout 120 lake exe amqp-endpoint server "$port" 3 >"$fifo" 2>&1 &
srv_pid=$!
exec 3<"$fifo"
IFS= read -r readiness <&3
printf '%s\n' "$readiness"

printf '$ lake exe amqp-endpoint client %s 5\n' "$port"
timeout 120 lake exe amqp-endpoint client "$port" 5 >"$cli" 2>&1
cli_status=$?

collect "$readiness" "$fifo" "$srv"
wait "$srv_pid"
srv_status=$?

printf -- '--- server\n'; cat "$srv"
printf -- '--- client\n'; cat "$cli"

if valid_case "$srv" "$cli"; then
  check "server exit status is 0 (saw $srv_status)" "$([ "$srv_status" = 0 ] && echo 0 || echo 1)"
  check "client exit status is 0 (saw $cli_status)" "$([ "$cli_status" = 0 ] && echo 0 || echo 1)"
  has "$srv" 'took HDR_SENT' 'server wrote its own header'
  has "$srv" 'took HDR_EXCH' 'server reassembled the peer'"'"'s header across 3-octet reads'
  has "$cli" 'took HDR_EXCH' 'client reassembled the peer'"'"'s header across 5-octet reads'
  has "$srv" 'the peer closed the stream \(orderly\)' 'server ended on the orderly close, not on a fault'
else
  printf 'INVALID open-close: the listener could not bind or the client could not connect\n'
fi

# ---------------------------------------------------------------- case 2: a short write, forced

printf '\n=== case short-write: a ~3 kB open in 1024-octet sends ===\n'
port="$((port_base + 1))"
fifo="$work/short-write.fifo"
srv="$work/short-write.server.log"
cli="$work/short-write.client.log"
mkfifo "$fifo"

# Both sides are the probe: the server declares a `max-frame-size` the large frame fits in, the client then
# sends it. The specification refuses to *send* a frame above the peer's a priori limit (512,
# MIN-MAX-FRAME-SIZE), so the declaration is not decoration — without it the client's write is refused and
# the case would be measuring a refusal instead of a looped write.
printf '$ SPECAMQP_SHIM_CONTROL=short-send lake exe amqp-endpoint-probe server %s 7\n' "$port"
SPECAMQP_SHIM_CONTROL=short-send timeout 120 lake exe amqp-endpoint-probe server "$port" 7 >"$fifo" 2>&1 &
srv_pid=$!
exec 3<"$fifo"
IFS= read -r readiness <&3
printf '%s\n' "$readiness"

printf '$ SPECAMQP_SHIM_CONTROL=short-send lake exe amqp-endpoint-probe client %s 13\n' "$port"
SPECAMQP_SHIM_CONTROL=short-send timeout 120 lake exe amqp-endpoint-probe client "$port" 13 >"$cli" 2>&1
cli_status=$?

collect "$readiness" "$fifo" "$srv"
wait "$srv_pid"
srv_status=$?

printf -- '--- server\n'; cat "$srv"
printf -- '--- client\n'; cat "$cli"

if valid_case "$srv" "$cli"; then
  check "server exit status is 0 (saw $srv_status)" "$([ "$srv_status" = 0 ] && echo 0 || echo 1)"
  check "client exit status is 0 (saw $cli_status)" "$([ "$cli_status" = 0 ] && echo 0 || echo 1)"
  has "$cli" 'wrote [0-9]+ octets in [0-9]+ send call\(s\)' 'the write loop reported a write the kernel took in pieces'
  has "$srv" 'took OPEN_SENT' 'server declared limits large enough for the frame'
  has "$srv" 'took OPENED' 'server read the looped write whole and accepted it'
  has "$srv" 'the peer closed the stream \(orderly\)' 'server ended on the orderly close'
  # the client is the one that closes here (its application is finished), so it has no orderly-close line
  # to show: what its log has to prove is that it ended in the state the protocol leaves after the write
  has "$cli" 'the connection ended in OPENED' 'client ended where the accepted frame left it'
else
  printf 'INVALID short-write: the listener could not bind or the client could not connect\n'
fi

printf '\n'
if [ "$invalid_runs" != 0 ]; then
  printf 'endpoint-shell: %s case(s) never tested the shell (port collision)\n' "$invalid_runs"
fi
if [ "$failures" = 0 ] && [ "$invalid_runs" = 0 ]; then
  printf 'endpoint-shell: PASS\n'
  exit 0
fi
printf 'endpoint-shell: FAIL (%s failed assertion(s), %s invalid case(s))\n' "$failures" "$invalid_runs"
exit 1
