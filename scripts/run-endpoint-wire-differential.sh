#!/usr/bin/env bash
#
# R4: the wire differential — the corpus replayed against the shipped endpoint *over a socket*,
# compared per vector with `amqp-spec`'s in-process answer.
#
#   shell bash scripts/run-endpoint-wire-differential.sh [corpus]
#
# The whole corpus is replayed in process today. Nothing drives the shipped process through it, so
# "the endpoint speaks AMQP" is demonstrated at the connection level and one `open` deep. This script is
# the tier that raises it to whatever the corpus covers, and it is a *differential*: for each vector it
# asks two things and compares them —
#
#   * **in process** — `lake exe amqp-spec <corpus>` says whether the specification admits the vector's
#     steps, and with which reason class if it refuses;
#   * **over the socket** — the shipped `amqp-endpoint` is started, a peer plays the vector's steps from
#     the other end, and the endpoint's own narration (`took <state>` / `refused …`, which is the
#     corpus's vocabulary, emitted by `Shell.Driver.reportAnswer`) plus the octets the peer received are
#     read as the endpoint's answer.
#
# The comparison is the one `s1_differential.sh` uses in process: the same status, and the same reason
# class where a refusal names one. A divergence is reported with the step it happened at, because "the
# endpoint disagrees with the specification" is not a finding — "it diverges at step 3, where the vector
# expects the endpoint to write 20 octets and it wrote none" is.
#
# ## What this tier cannot yet reach, stated rather than hidden
#
# The endpoint's *application* is fixed in `Shell.Main`: it announces the protocol header (the shell does,
# on every connection) and then sends nothing, ending the client side once both headers are exchanged.
# `Shell.Driver.App` is the seam a corpus-driven application goes through, and until one exists the send
# steps beyond the header cannot be taken by the shipped process. Those steps are therefore expected to
# diverge here, and each one is reported as the application's absence rather than as a protocol defect —
# the distinction matters, because the first is a missing programme and the second would be a bug.
#
# ## The two lessons this driver is built on
#
# The readiness line is **read**, not polled, and it must be the server's own announcement: a server that
# failed to bind prints the shim's error and exits, and reading that as readiness carries a dead server
# into the case. Ports are **scanned** from a pid-derived base rather than fixed: the gate suite runs its
# scripts back to back, so a derivation alone collides systematically with the previous gate's still-live
# servers. Both follow `scripts/run-endpoint-shell.sh`, which learned them at the other end of the socket.
#
# Offline: both processes are local binaries and the only ordering is process start-up.

set -u

root=$(cd "$(dirname "$0")/.." && pwd)
readonly root
corpus="${1:-vectors/slice.ndjson}"

# Evidence builds set LAKE_NO_CACHE=1 (see AGENTS.md).
export LAKE_NO_CACHE="${LAKE_NO_CACHE:-1}"

command -v timeout >/dev/null || { echo "wire-differential: 'timeout' is required" >&2; exit 1; }
[ -f "$root/$corpus" ] || { echo "wire-differential: no corpus at $corpus" >&2; exit 1; }

work=$(mktemp -d)
if [ -n "${SPECAMQP_WIRE_KEEP:-}" ]; then
  # the run's raw evidence — the peer's per-step reports and the endpoint's own log — is what makes
  # a divergence attributable; keeping it on request is how the open question stays answerable
  printf 'work dir kept: %s\n' "$work"
else
  trap 'rm -rf "$work"' EXIT
fi

# `lake exe` runs from the package directory, and the endpoint functions below are called
# directly rather than in a subshell so that the port they took and the descriptor they hold on
# the server's readiness FIFO survive into the caller — a subshell would lose both.
cd "$root/lean"

port_base="${SPECAMQP_WIRE_PORT_BASE:-$((49100 + ($$ % 300)))}"
port_attempts="${SPECAMQP_WIRE_PORT_ATTEMPTS:-40}"
read_octets="${SPECAMQP_WIRE_READ_OCTETS:-64}"

# ---------------------------------------------------------------- in-process: the specification's answer

printf 'building amqp-spec and amqp-wire-app\n'
( cd "$root/lean" && lake build amqp-spec amqp-wire-app ) >"$work/build.log" 2>&1 ||
  { echo "wire-differential: build failed: $(tail -3 "$work/build.log")"; exit 1; }

printf 'in process: lake exe amqp-spec %s\n' "$corpus"
( cd "$root/lean" && lake exe amqp-spec "$root/$corpus" ) >"$work/spec.log" 2>"$work/spec.err"
spec_status=$?
printf '     in-process exit status: %s (its own verdict is the per-vector lines below)\n' "$spec_status"

# ---------------------------------------------------------------- over the socket, vector by vector

# Which vectors a *wire* replay can compare: one whose every step fixes its octets. A step that
# carries `value` instead asks the endpoint to send a described value, whose encoding is the
# implementation's own choice — comparing those is the in-process differential's job, not this
# one's, and driving them here would compare a harness's encoder with itself.
selection=$(python3 - "$root/$corpus" <<'PYSELECT'
import json, pathlib, sys
playable, excluded = [], []
for line in pathlib.Path(sys.argv[1]).read_text().splitlines():
    if not line.strip():
        continue
    entry = json.loads(line)
    steps = entry.get("steps", [])
    if steps and all("bytes" in step and "direction" in step for step in steps):
        playable.append(entry["vector"])
    else:
        why = "a step carries `value` rather than octets" if any("value" in s for s in steps) \
            else "a step is not a wire step"
        excluded.append(f"{entry['vector']} ({why})")
print("\n".join(playable))
print("---")
print("\n".join(excluded))
PYSELECT
)
vectors=$(printf '%s\n' "$selection" | sed '/^---$/,$d' | grep -v '^$')
excluded=$(printf '%s\n' "$selection" | sed -n '/^---$/,$p' | grep -v '^---$' | grep -v '^$')

printf '\nplayable over the socket: %s vector(s)\n' "$(printf '%s\n' "$vectors" | grep -c . || echo 0)"
if [ -n "$excluded" ]; then
  printf 'not wire-comparable, and why:\n'
  printf '%s\n' "$excluded" | sed 's/^/     /'
fi

srv_pid=""
srv_fifo=""
ready=""
port=""

# Start the endpoint — with R4's corpus-driven application — on the first port in `[first, first +
# port_attempts)` that it can bind, with a FIFO so that a server which blocks before flushing hangs this
# script rather than passing it.
#
# The shape is one convention with per-driver ranges, stated in the plan: a candidate port derived from
# this process's own pid, a **forward scan** over a bounded range, and **the server's own announcement**
# as readiness — scanned for in its output rather than assumed to be the first line it writes. The
# derivation is a blind starting point and the *bind* is what arbitrates, which is why there is no lock,
# no registry and no shared base: two drivers scanning at once take different ports, and a lock would
# serialise them to buy nothing. The environment variables that pin the start and the bound are named per
# driver (`SPECAMQP_WIRE_*` here, `SPECAMQP_ENDPOINT_*` in the shell's driver) for the same reason — a
# shared base would make two suites race for one window instead of settling it by bind.
#
# Returns 0 when the endpoint announced the port it took, 1 when the range is exhausted — a **named
# invalid**: this run tested nothing — and 2 when the endpoint started and refused the vector, since a
# vector the application cannot play is a loud failure of its own and retrying it on forty ports would
# report a bind collision that never happened.
start_endpoint() {
  label=$1
  first=$2
  attempt=0
  while [ "$attempt" -lt "$port_attempts" ]; do
    port=$((first + attempt))
    srv_fifo="$work/$label.$attempt.fifo"
    mkfifo "$srv_fifo"
    timeout 120 lake exe amqp-wire-app server "$port" "$root/$corpus" "$label" "$read_octets" \
      >"$srv_fifo" 2>&1 &
    srv_pid=$!
    exec 3<"$srv_fifo"
    readiness=""
    announced=0
    while IFS= read -r line <&3; do
      readiness=$(printf '%s\n%s' "$readiness" "$line")
      if printf '%s' "$line" | grep -q 'listening port='; then
        announced=1
        break
      fi
    done
    if [ "$announced" = 1 ]; then
      ready="$readiness"
      return 0
    fi
    if printf '%s' "$readiness" | grep -qE 'carries no vector|no start state|send a .value|asked to send'; then
      printf '%s\n' "$readiness" >"$work/$label.startup.log"
      exec 3<&-
      wait "$srv_pid" 2>/dev/null
      return 2
    fi
    exec 3<&-
    wait "$srv_pid" 2>/dev/null
    attempt=$((attempt + 1))
  done
  return 1
}

: >"$work/socket.log"
vector_count=0
for id in $vectors; do
  vector_count=$((vector_count + 1))
  peer_report="$work/$id.peer.jsonl"
  endpoint_log="$work/$id.endpoint.log"

  start_endpoint "$id" "$port_base"
  start_status=$?
  if [ "$start_status" != 0 ]; then
    if [ "$start_status" = 2 ]; then
      printf '%s\n' "$id INVALID endpoint-refused-the-vector" >>"$work/socket.log"
    else
      printf '%s\n' "$id INVALID no-port-in-the-scan-range" >>"$work/socket.log"
    fi
    port_base=$((port_base + port_attempts))
    continue
  fi

  timeout 120 python3 "$root/scripts/endpoint/wire_peer.py" \
    --port "$port" --corpus "$root/$corpus" --vector "$id" --report "$peer_report" \
    >"$work/$id.peer.stdout" 2>&1
  peer_status=$?

  { printf '%s\n' "$ready"; cat <&3; } >"$endpoint_log"
  exec 3<&-
  wait "$srv_pid"
  endpoint_status=$?

  printf '%s %s %s %s\n' "$id" "$peer_status" "$endpoint_status" "$peer_report" >>"$work/socket.log"
done

# ---------------------------------------------------------------- the comparison

python3 - "$root/$corpus" "$work/spec.log" "$work/socket.log" "$work" <<'PY' 
import json, pathlib, re, sys

corpus, spec_log, socket_log, work = sys.argv[1], sys.argv[2], sys.argv[3], pathlib.Path(sys.argv[4])

vectors = {}
for line in pathlib.Path(corpus).read_text().splitlines():
    if line.strip():
        entry = json.loads(line)
        vectors[entry["vector"]] = entry

spec = {}
for line in pathlib.Path(spec_log).read_text().splitlines():
    line = line.strip()
    if not line.startswith("{"):
        continue
    try:
        entry = json.loads(line)
    except json.JSONDecodeError:
        continue
    if "vector" in entry and "status" in entry:
        spec[entry["vector"]] = entry

CLASSES = ("truncated", "unassigned", "unsupported", "sizeMismatch", "malformed", "limit")

def reason_class(detail):
    for name in CLASSES:
        if name in detail:
            return name
    return None

def narration(lines):
    """The endpoint's own answers, in the corpus's vocabulary: `took <state>` / `refused <state>`."""
    out = []
    for line in lines:
        m = re.match(r"^(took|refused) (\S+)", line.strip())
        if m:
            out.append((m.group(1), m.group(2)))
    return out

rows = []
for record in pathlib.Path(socket_log).read_text().splitlines():
    parts = record.split()
    if len(parts) == 3 and parts[1] == "INVALID":
        reason = parts[2].replace("-", " ")
        startup = pathlib.Path(work / f"{parts[0]}.startup.log")
        if startup.exists():
            reason += " — " + startup.read_text().strip()
        rows.append((parts[0], "INVALID", "the endpoint did not serve this vector", [reason]))
        continue
    if len(parts) != 4:
        continue
    vector_id, peer_status, endpoint_status, peer_path = parts[0], int(parts[1]), int(parts[2]), parts[3]
    vector = vectors[vector_id]
    steps = vector.get("steps", [])
    peer = {}
    peer_file = pathlib.Path(peer_path)
    if peer_file.exists():
        for line in peer_file.read_text().splitlines():
            if line.strip():
                entry = json.loads(line)
                peer[entry["step"]] = entry
    endpoint_lines = pathlib.Path(work / f"{vector_id}.endpoint.log").read_text().splitlines()
    answers = narration(endpoint_lines)

    # What the endpoint narrated, and how it lines up with the vector's steps. A `took <state>` is one
    # answer to one step and names the state the peer is in after it. A **refusal is two answers** — the
    # protocol condition, then the reason class — because that is the vocabulary the corpus compares on,
    # and neither names a state: a refused step leaves the peer where the last `took` already said it was.
    # So a step consumes every consecutive refusal it produced, and otherwise exactly one answer. This is
    # why a positional one-answer-per-step reading was wrong, and why it is replaced rather than widened.
    problems = []
    answer_index = 0
    in_state = ""
    # The endpoint narrates its own preamble — the header it announces and the exchange that follows —
    # before the vector's first step, exactly as it puts those octets on the wire. A vector that begins
    # after the exchange says so in `start`, so the answers up to and including the one naming that state
    # belong to the preamble and not to any step of the vector.
    start_state = (vector.get("start") or "").split(":")[-1]
    if start_state:
        for index, (verb, word) in enumerate(answers):
            if verb == "took" and word == start_state:
                answer_index = index + 1
                in_state = start_state
                break
    for number, step in enumerate(steps, 1):
        expect = step.get("expect") or {}
        status = expect.get("status", "admitted")
        state = expect.get("state")
        observed = peer.get(number, {})
        step_problems = []
        if step["direction"] == "send" and status == "refused":
            if observed.get("got"):
                step_problems.append("the endpoint wrote octets the vector says it must refuse")
        elif step["direction"] == "send":
            if not observed.get("matched"):
                wrote = observed.get("got", "")
                detail = f"the vector expects the endpoint to write {len(step['bytes']) // 2} octets"
                if wrote:
                    detail += (f"; it wrote {len(wrote) // 2}: {wrote[:64]}"
                               + ("…" if len(wrote) > 64 else "")
                               + f" where the vector's are {step['bytes'][:64]}"
                               + ("…" if len(step["bytes"]) > 64 else ""))
                else:
                    detail += (f"; {observed.get('observed', 'no observation')} — the endpoint was in "
                               f"{in_state or 'no state it narrated'}, where the vector asks for no send")
                step_problems.append(detail)
        # the endpoint's own answer to this step
        if status == "refused":
            consumed = []
            while answer_index < len(answers) and answers[answer_index][0] == "refused":
                consumed.append(answers[answer_index][1])
                answer_index += 1
            if not consumed:
                step_problems.append(
                    "the endpoint narrated no refusal: the vector expects it to offer these octets and be "
                    "refused, and no refusal reached the wire")
            else:
                said = " ".join(consumed)
                if (expect.get("condition") or "") not in said:
                    step_problems.append(
                        f"the endpoint refused as `{said}`; the vector names {expect.get('condition')}")
                if (expect.get("reason") or "") not in said:
                    step_problems.append(
                        f"the endpoint refused as `{said}`; the vector names {expect.get('reason')}")
            if state and in_state and in_state != state.split(":")[-1]:
                step_problems.append(
                    f"the vector expects the peer in {state}; the endpoint is in {in_state}")
        elif state and answer_index < len(answers) and answers[answer_index][0] == "took":
            in_state = answers[answer_index][1]
            answer_index += 1
            if in_state != state.split(":")[-1]:
                step_problems.append(
                    f"the vector expects the peer in {state}; the endpoint said {in_state}")
        elif state:
            step_problems.append(
                f"the vector expects the peer in {state}, and the endpoint narrated nothing for this "
                f"step: it is in {in_state or 'no state it narrated'}")
        elif answer_index < len(answers) and answers[answer_index][0] == "took":
            # The step names no state, so the vector compares nothing about where the peer is — and it
            # must not be read as demanding an answer either: a step that says nothing about the state is
            # a step that leaves it alone. The endpoint's answer to it is still consumed, because it
            # advances the state the next step is read from, and whether that answer arrives here or is
            # folded into the step before it depends only on how the peer's writes coalesced in the
            # endpoint's reads — a verdict must not turn on that.
            in_state = answers[answer_index][1]
            answer_index += 1
        # and the differential itself: this step's socket verdict against the specification's
        spec_entry = spec.get(f"{vector_id}#{number}")
        if spec_entry is not None:
            step_socket = "pass" if not step_problems else "fail"
            if step_socket != spec_entry["status"]:
                spec_class = reason_class(spec_entry.get("detail", ""))
                step_problems.append(
                    f"over the socket this step is {step_socket}; the specification says "
                    f"{spec_entry['status']}"
                    + (f" ({spec_class})" if spec_class else ""))
        for problem in step_problems:
            problems.append(f"step {number}: {problem}")

    socket_verdict = "pass" if not problems else "fail"
    spec_entry = spec.get(f"{vector_id}#1") or next(
        (spec[f"{vector_id}#{n}"] for n in range(1, len(steps) + 1) if f"{vector_id}#{n}" in spec), None)
    if spec_entry is None:
        rows.append((vector_id, socket_verdict, "amqp-spec has no verdict for this vector", problems))
        continue
    spec_status = spec_entry["status"]
    spec_class = reason_class(spec_entry.get("detail", ""))
    rows.append((vector_id, socket_verdict,
                 f"amqp-spec {spec_status}" + (f" ({spec_class})" if spec_class else ""),
                 problems))

print()
print(f"{'vector':<46} {'socket':<7} {'in process':<22} divergence")
agree = 0
for vector_id, verdict, spec_text, problems in rows:
    first = problems[0] if problems else ""
    print(f"{vector_id:<46} {verdict:<7} {spec_text:<22} {first[:70]}")
    for extra in problems[1:3]:
        print(f"{'':<46} {'':<7} {'':<22} {extra[:70]}")
    if verdict == "pass" and spec_text.startswith("amqp-spec pass"):
        agree += 1
print()
print(f"{len(rows)} vector(s): {agree} agree with the specification, "
      f"{sum(1 for r in rows if r[1] == 'fail')} diverge over the socket")
sys.exit(1 if any(r[1] != "pass" for r in rows) else 0)
PY
compare_status=$?

printf '\n'
printf 'wire-differential: socket replay of %s against the shipped endpoint (%s vector(s))\n' \
  "$corpus" "$vector_count"
if [ "$compare_status" = 0 ]; then
  printf 'wire-differential: PASS\n'
  exit 0
fi
printf 'wire-differential: FAIL (the divergences are named above, each with its step)\n'
exit 1
