#!/usr/bin/env bash
# The shipped endpoint is driven over the socket, and the run is *forced* rather than merely green.
#
# `Shell/Driver.lean` states three obligations that no proof in this tree covers: that the shell loops on a
# short read, that it writes exactly what the core returns and all of it, and that it treats `recv`'s `none`
# as the peer's orderly close. `scripts/run-endpoint-shell.sh` is the tier that forces them; this file is
# the contract that says what a passing run has to have shown.
#
# The forcing is asserted *structurally*, and the first version of this file got that wrong: it pinned four
# sentences the driver printed, on the reasoning that they name forcing conditions rather than incidental
# output. A refactor in the driver reworded one of them — "the header" for "the peer's header" — and this
# gate failed while the forcing was intact, which is the failure mode the repository's own rule warns about.
# Verdicts, named conditions and exit statuses are contract; sentences are not. So what is asserted here is
# the *shape of the run*: the read sizes each case forced, the send cap the short-write case requires, how
# many sends the kernel took the frame in, and a floor on the number of assertions that passed. Each of those
# catches a driver that stopped forcing without caring how it words an assertion. The read sizes are asserted
# from the *invocations* the driver echoes, because only the server announces its size on startup — the client's
# appears nowhere else, which the first attempt at this got wrong and this gate then said so precisely.
#
# The driver reports a case whose listener could not bind as INVALID and exits non-zero for it, so the
# "the port was busy" failure can never satisfy this gate. That collision was real and systematic rather than
# rare — a pid-derived base cannot collide with itself but does collide with the *previous* gate in filename
# order, since `r1_transport_shell.sh` runs immediately before this one and leaves servers alive inside their
# timeouts — and the driver's arbitration has since landed. It now scans forward over a bounded range, reads
# the readiness line as the server's *own* announcement, prints the port it took, and exhausts the range into
# the INVALID path. So an INVALID from a full-suite run means what it says: the range was exhausted, nothing
# was tested, and that is worth reading before a re-run rather than waved through.

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

grep -qF 'read-octets=3' "$log" ||
  die "no server ran with 3-octet reads: the header could arrive whole and the case would force nothing"
grep -qE 'amqp-endpoint client [0-9]+ 5' "$log" ||
  die "the client was not started with 5-octet reads: the forcing is absent on that side"
grep -qE 'amqp-endpoint server [0-9]+ 3' "$log" ||
  die "the server was not started with 3-octet reads"
grep -qF 'SPECAMQP_SHIM_CONTROL=short-send' "$log" ||
  die "the short-write case did not run through the send cap, so the write loop was never forced"
sends="$(grep -oE 'in [0-9]+ send' "$log" | grep -oE '[0-9]+' | sort -n | tail -1)"
[ -n "$sends" ] || die "no case reported how many sends the kernel took: the write forcing is unobserved"
[ "$sends" -ge 2 ] ||
  die "the largest write took $sends send(s): the loop never iterated, so the cap did not bite"
assertions="$(grep -c '^ok ' "$log" || true)"
[ "$assertions" -ge 13 ] ||
  die "only $assertions assertion(s) passed: the driver has stopped checking what it used to"

printf 'r2_endpoint_shell: PASS\n'
printf '     %s assertions passed; the write loop iterated %s send(s); reads forced at 3 and 5 octets\n' "$assertions" "$sends"
