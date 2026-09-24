#!/usr/bin/env bash
#
# R4: the wire differential — the corpus replayed against the shipped endpoint *over a socket*,
# compared per vector with `amqp-spec`'s in-process answer.
#
#   shell bash scripts/run-endpoint-wire-differential.sh [--report PATH] [corpus]
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
# ## The application seam, and what closing it changed
#
# The application the differential runs is `scripts/endpoint/WireApp`: a corpus-driven application at the
# `Shell.Driver.App` seam, beside its peer `wire_peer.py` and shipped by neither. Two properties of *that
# seam* used to keep some `send` steps out of the application's reach, and both were the seam's rather than
# either artefact's:
#
#   * the shell asked the application only after a **unit** of the peer's octets arrived, so the second of
#     two sends played from one state, with nothing arriving between them, was never prompted;
#   * the shell announced the protocol header itself before the core's first read, so a step whose pre-state
#     was `START` was not the application's to play.
#
# **Both are closed.** `Shell.Driver.serveApp` re-asks the application after each step it takes — bounded,
# and loud when the bound is exhausted — and the protocol header is the application's opening move, with the
# shell starting the connection at the specification's own `START`. The three vectors those two properties
# kept out of reach now agree with the specification end to end. There is consequently no seam label left to
# reach for: a divergence this run reports is a divergence of the **endpoint**, or of the harness in front of
# it, and the report says so rather than naming a seam that no longer exists. Which is why the closed set of
# causes below now holds `unknown` alone — a remaining divergence is one nobody has attributed, and the gate
# is what catches it.
#
# ## The machine-readable report, and the closed set of causes
#
# `--report PATH` writes a JSON document beside the table — for the contract that asserts over this tier
# rather than over its prose:
#
#   {"corpus": "<as given>",
#    "vectors": [{"vector": "<id>",
#                 "socket": "pass" | "fail" | "INVALID",
#                 "in_process": "pass" | "fail" | "unreported",
#                 "divergences": [{"step": <int>, "cause": "<label>", "detail": "<the line the table printed>"}]}]}
#
# `divergences` is one entry per **step**, not per problem line: a step whose divergence produced three
# sentences is one divergence, and its `detail` is those sentences joined by newlines — the same text the
# table prints, so the two can be read against each other without the prose being re-derived here.
#
# A divergence's `cause` is drawn from a **closed set** rather than left to the sentence, because a
# contract cannot assert over prose. That set holds `unknown` alone now that the two `app-seam-` causes have
# been closed — an unattributable divergence is exactly what the gate exists to catch, and a label invented
# for one would hide it. A `core-…` cause can still be admitted later as a deliberate, reviewed addition
# rather than by accident.
#
# A row that never ran — the port range exhausted, a listener that could not bind — carries
# `"socket": "INVALID"` and a row-level `detail`, and **no** `divergences` at all: nothing diverged, so
# `unknown` is not borrowed for it. Two failure modes that must not read alike — the endpoint disagreeing
# for an unnameable reason, and the run never having tested anything — stay distinguishable.
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

# The corpus is the one positional argument it has always been; `--report PATH` (also `--report=PATH`) is
# the option that writes the machine-readable document the contract reads. An option this driver does not
# know is refused **by name** rather than ignored: a run whose report option was silently dropped would
# look like a run that produced no report, which is the near-silent failure this option exists to avoid.
usage() {
  printf 'usage: %s [--report PATH] [corpus]\n' "$0" >&2
  exit 2
}
report=""
corpus=""
while [ $# -gt 0 ]; do
  case "$1" in
    --report)
      [ $# -ge 2 ] && [ -n "$2" ] || { printf 'wire-differential: --report needs a non-empty path\n' >&2; usage; }
      report=$2
      shift 2
      ;;
    --report=*)
      report=${1#--report=}
      [ -n "$report" ] || { printf 'wire-differential: --report needs a non-empty path\n' >&2; usage; }
      shift
      ;;
    -*)
      printf 'wire-differential: unknown option %s\n' "$1" >&2
      usage
      ;;
    *)
      [ -z "$corpus" ] || { printf 'wire-differential: more than one corpus given\n' >&2; usage; }
      corpus=$1
      shift
      ;;
  esac
done
corpus="${corpus:-vectors/slice.ndjson}"

# The report path is resolved against the caller's directory **before** the `cd "$root/lean"` below: a
# relative path meant for the caller's shell must not land inside the package.
if [ -n "$report" ]; then
  case "$report" in
    /*) : ;;
    *) report="$PWD/$report" ;;
  esac
  [ -d "$(dirname "$report")" ] ||
    { printf 'wire-differential: --report directory does not exist: %s\n' "$(dirname "$report")" >&2; exit 2; }
fi

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

# The peer's write grouping is this driver's **control** over the one condition the endpoint's reads cannot
# be trusted to vary: `SPECAMQP_WIRE_COALESCE=1` writes each run of consecutive `receive` steps in one
# `sendall`, so both frames arrive in the endpoint as a single read and are consumed by a single `feed`.
# Without it, whether they do is a race nothing here samples differently — a reader already blocked in
# `recv` takes back-to-back loopback writes as separate arrivals, run after run — which is precisely how a
# verdict that turns on the difference went unnoticed. Two runs of one condition are a sample; this is the
# other condition.
coalesce_flag=""
if [ -n "${SPECAMQP_WIRE_COALESCE:-}" ]; then
  coalesce_flag="--coalesce"
fi

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
# Returns 0 when the endpoint announced the port it took — and it is **printed**, in the shape and for
# the reason the shell's driver prints it, because a run that leaves no visible record of the port it
# took cannot be reproduced from its own output; 1 when the range is exhausted, a **named invalid**: this
# run tested nothing; 2 when the endpoint started and refused the vector; and 3 when it failed to start
# for a reason this driver does not recognise.
#
# Classes 2 and 3 are **not** retried: a vector the application cannot play, and a start-up failure that
# is not a bind collision, are each a loud failure of their own, and retrying either across forty ports
# would report a collision that never happened — which is the whole reason the two are named rather than
# left to fall through. **Only a failed bind is retried**, and that is decided by the transport's own
# words (`transport shim: bind failed: …`) rather than by "the server did not announce": the derived port
# may be held by the gate that ran before this one, and the *next* port is the answer to that, but
# nothing else about a failure to start is a fact about the port.
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
    # The endpoint's own output up to (and including) its readiness line, one whole line at a time: the
    # separator goes *after* each line rather than before it, so a failure's first line is not preceded by
    # a blank one in the message this driver prints.
    readiness=""
    announced=0
    while IFS= read -r line <&3; do
      readiness="${readiness}${line}"$'\n'
      if printf '%s' "$line" | grep -q 'listening port='; then
        announced=1
        break
      fi
    done
    if [ "$announced" = 1 ]; then
      ready="$readiness"
      printf '     (took port %s for %s)\n' "$port" "$label"
      return 0
    fi
    exec 3<&-
    wait "$srv_pid" 2>/dev/null
    printf '%s' "$readiness" >"$work/$label.startup.log"
    # The endpoint's own words, as one message: no trailing blank line, and a stand-in when it said nothing
    # at all — a server the `timeout` killed before it printed still fails loudly rather than silently.
    startup_words="${readiness%$'\n'}"
    startup_words="${startup_words:-the endpoint exited without saying anything}"
    if printf '%s' "$readiness" | grep -qE 'transport shim: bind failed'; then
      printf '     port %s did not bind: %s\n' "$port" "$startup_words"
      attempt=$((attempt + 1))
      continue
    fi
    if printf '%s' "$readiness" | grep -qE 'carries no vector|names no start state|send a .value'; then
      # The three messages the endpoint can print **before** its readiness line, and the only three:
      # `asked to send` is deliberately not among them, because it is raised inside `serveApp`, which
      # runs strictly after the announcement has been printed and read — a branch that cannot fire here
      # is a branch that would make the class look wider than it is.
      printf '     the endpoint refused %s: %s\n' "$label" "$startup_words"
      return 2
    fi
    printf '     %s: the endpoint did not start: %s\n' "$label" "$startup_words"
    return 3
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
    # Three named classes, and each one says which it is: the range was exhausted, the endpoint refused
    # the vector, or the endpoint failed to start for a reason that is not a bind collision. Only the
    # first is about the port; the comparator quotes the endpoint's own words for the other two.
    if [ "$start_status" = 2 ]; then
      printf '%s\n' "$id INVALID endpoint-refused-the-vector" >>"$work/socket.log"
    elif [ "$start_status" = 3 ]; then
      printf '%s\n' "$id INVALID endpoint-failed-to-start" >>"$work/socket.log"
    else
      printf '%s\n' "$id INVALID no-port-in-the-scan-range" >>"$work/socket.log"
    fi
    port_base=$((port_base + port_attempts))
    continue
  fi

  timeout 120 python3 "$root/scripts/endpoint/wire_peer.py" \
    --port "$port" --corpus "$root/$corpus" --vector "$id" --report "$peer_report" \
    $coalesce_flag >"$work/$id.peer.stdout" 2>&1
  peer_status=$?

  # the readiness the server announced, then the rest of its own output: `ready` already ends in its
  # newline, so the two halves join without a blank line between them
  { printf '%s' "$ready"; cat <&3; } >"$endpoint_log"
  exec 3<&-
  wait "$srv_pid"
  endpoint_status=$?

  printf '%s %s %s %s\n' "$id" "$peer_status" "$endpoint_status" "$peer_report" >>"$work/socket.log"
done

# ---------------------------------------------------------------- the comparison

python3 - "$root/$corpus" "$work/spec.log" "$work/socket.log" "$work" "$report" "$corpus" <<'PY'
import json, pathlib, re, sys

corpus_path, spec_log, socket_log, work, report_path, corpus_given = (
    sys.argv[1], sys.argv[2], sys.argv[3], pathlib.Path(sys.argv[4]), sys.argv[5], sys.argv[6])

vectors = {}
for line in pathlib.Path(corpus_path).read_text().splitlines():
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

def ended_state(lines):
    """The state the endpoint's own application reported the connection ended in.

    `WireApp.main` prints it as its last word — `endpoint: the connection ended in {state}` — and it is
    the only statement anywhere of where a refusal that **ended** the connection left the peer: the
    narration vocabulary carries no state on a refusal, by design. Reading it here is what lets a vector
    whose refused step names a state be compared at all, rather than diverge by construction.
    """
    for line in reversed(lines):
        m = re.match(r"^endpoint: the connection ended in (\S+)$", line.strip())
        if m:
            return m.group(1)
    return None

def bare_state(name):
    """A corpus state name without its layer prefix: `connection:HDR_EXCH` is `HDR_EXCH`."""
    return name.split(":")[-1] if name else ""

# The **closed set** a divergence's cause is drawn from, so a contract can assert over it rather than over
# the sentence above. It holds `unknown` alone: the two `app-seam-` causes this tier's docstring once named
# are closed, and no other cause for a divergence has been established — an unattributed divergence is
# exactly what the gate exists to catch, so a label invented for one would hide it rather than explain it.
CAUSE_UNKNOWN = "unknown"


def in_process_verdict(vector_id, steps):
    """The vector's in-process verdict, as the table's `in process` column reads it.

    The status of the step-1 entry `amqp-spec` printed, or of the first entry present. `unreported` is the
    case where `amqp-spec` printed nothing for the vector at all — a value a contract must not read as
    `fail`, because "the specification refused this" and "the specification said nothing" are not the same
    statement. The second return value is the column's own text, which carries the reason class.
    """
    entry = spec.get(f"{vector_id}#1") or next(
        (spec[f"{vector_id}#{n}"] for n in range(1, len(steps) + 1) if f"{vector_id}#{n}" in spec), None)
    if entry is None:
        return "unreported", "amqp-spec has no verdict for this vector"
    klass = reason_class(entry.get("detail", ""))
    return entry["status"], f"amqp-spec {entry['status']}" + (f" ({klass})" if klass else "")


def divergence_lines(problems):
    """The problems as the table prints them, and the per-step divergences the report carries.

    A divergence is **per step**: a step whose divergence produced three sentences is one divergence of
    that step, not three, and its report `detail` is those sentences joined by newlines — the same text the
    table prints, so the two can be read against each other. The step's `cause` is the structured cause any
    of its problems carried, or `unknown`: a divergence nothing attributable explains is what the gate
    exists to catch, and a step whose problems are unattributed says so rather than borrowing a cause.
    """
    lines = [f"step {number}: {text}" for number, text, _ in problems]
    divergences = []
    for number, text, cause in problems:
        if divergences and divergences[-1]["step"] == number:
            divergences[-1]["detail"] += "\n" + text
            if divergences[-1]["cause"] == CAUSE_UNKNOWN and cause:
                divergences[-1]["cause"] = cause
        else:
            divergences.append({"step": number, "cause": cause or CAUSE_UNKNOWN, "detail": text})
    return lines, divergences

rows = []
for record in pathlib.Path(socket_log).read_text().splitlines():
    parts = record.split()
    if len(parts) == 3 and parts[1] == "INVALID":
        reason = parts[2].replace("-", " ")
        startup = pathlib.Path(work / f"{parts[0]}.startup.log")
        if startup.exists():
            reason += " — " + startup.read_text().strip()
        # A row that never ran: `socket` says INVALID, the reason is a row-level `detail`, and there are no
        # divergences at all — nothing diverged, so `unknown` is not borrowed for a run that tested nothing.
        # A contract can then tell "the endpoint disagreed for an unnameable reason" from "the listener
        # never bound", which are different failures that must not read alike.
        steps = vectors.get(parts[0], {}).get("steps", [])
        in_process, _ = in_process_verdict(parts[0], steps)
        rows.append({"vector": parts[0], "socket": "INVALID", "in_process": in_process,
                     "in_process_text": "the endpoint did not serve this vector",
                     "lines": [], "detail": reason, "divergences": None})
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
    ended = ended_state(endpoint_lines)

    # What the endpoint narrated, and how it lines up with the vector's steps. A `took <state>` is one
    # answer to one step and names the state the peer is in after it. A **refusal is two answers** — the
    # protocol condition, then the reason class — because that is the vocabulary the corpus compares on,
    # and neither names a state: where a refusal leaves the peer is read from the endpoint's own narration
    # (the `ended` line above) rather than assumed.
    # So a step consumes every consecutive refusal it produced, and otherwise exactly one answer. This is
    # why a positional one-answer-per-step reading was wrong, and why it is replaced rather than widened.
    problems = []
    answer_index = 0
    in_state = ""
    # The endpoint narrates its own preamble — the header it announces and the exchange that follows —
    # before the vector's first step, exactly as it puts those octets on the wire. A vector that begins
    # after the exchange says so in `start`, so the answers up to and including the one naming that state
    # belong to the preamble and not to any step of the vector.
    start_state = bare_state(vector.get("start") or "")
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
                step_problems.append(("the endpoint wrote octets the vector says it must refuse", None))
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
                step_problems.append((detail, None))
        # the endpoint's own answer to this step
        if status == "refused":
            consumed = []
            while answer_index < len(answers) and answers[answer_index][0] == "refused":
                consumed.append(answers[answer_index][1])
                answer_index += 1
            if not consumed:
                step_problems.append((
                    "the endpoint narrated no refusal: the vector expects it to offer these octets and be "
                    "refused, and no refusal reached the wire", None))
            else:
                said = " ".join(consumed)
                if (expect.get("condition") or "") not in said:
                    step_problems.append((
                        f"the endpoint refused as `{said}`; the vector names {expect.get('condition')}",
                        None))
                if (expect.get("reason") or "") not in said:
                    step_problems.append((
                        f"the endpoint refused as `{said}`; the vector names {expect.get('reason')}", None))
            if state:
                # **Where a refusal leaves the peer is stated by the endpoint, not assumed here.** The
                # narration vocabulary carries no state on a refusal, so this comparison used to read the
                # state the *last* `took` named — which is right only while the refusal changed nothing,
                # and made every vector whose refused step names a state diverge by construction. The
                # endpoint's own words decide it: the state it narrated last stands (`in_state`), unless
                # the refusal is the last thing it narrated, in which case the state its **application**
                # reported the connection ended in is the only statement of where it went.
                if answer_index >= len(answers) and ended:
                    after, told_by = ended, "the state its application reported the connection ended in"
                else:
                    after, told_by = in_state, f"what the endpoint narrated last, `took {in_state}`"
                if after and after != bare_state(state):
                    step_problems.append((
                        f"the vector expects the peer in {state}; the endpoint's own last word was {after} "
                        f"({told_by})", None))
        elif state and answer_index < len(answers) and answers[answer_index][0] == "took":
            in_state = answers[answer_index][1]
            answer_index += 1
            if in_state != state.split(":")[-1]:
                step_problems.append((
                    f"the vector expects the peer in {state}; the endpoint said {in_state}", None))
        elif state:
            step_problems.append((
                f"the vector expects the peer in {state}, and the endpoint narrated nothing for this "
                f"step: it is in {in_state or 'no state it narrated'}", None))
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
                step_problems.append((
                    f"over the socket this step is {step_socket}; the specification says "
                    f"{spec_entry['status']}"
                    + (f" ({spec_class})" if spec_class else ""), None))
        for text, cause in step_problems:
            problems.append((number, text, cause))

    socket_verdict = "pass" if not problems else "fail"
    in_process, in_process_text = in_process_verdict(vector_id, steps)
    lines, divergences = divergence_lines(problems)
    rows.append({"vector": vector_id, "socket": socket_verdict, "in_process": in_process,
                 "in_process_text": in_process_text, "lines": lines, "divergences": divergences})

print()
print(f"{'vector':<46} {'socket':<7} {'in process':<22} divergence")
agree = 0
for row in rows:
    # Every problem is printed **in full**, one per line, where it used to be cut at seventy columns and
    # capped at two: the part that says *which* it is — the endpoint's own last word quoted, the octets it
    # wrote against the vector's — lands at the end of the line, and a fixed-width cut hides exactly that.
    # Whoever reads this table and nothing else is the reader the report is for.
    lines = row["lines"]
    first = lines[0] if lines else row.get("detail", "")
    print(f"{row['vector']:<46} {row['socket']:<7} {row['in_process_text']:<22} {first}")
    for extra in lines[1:]:
        print(f"{'':<46} {'':<7} {'':<22} {extra}")
    if row["socket"] == "pass" and row["in_process_text"].startswith("amqp-spec pass"):
        agree += 1
print()
print(f"{len(rows)} vector(s): {agree} agree with the specification, "
      f"{sum(1 for r in rows if r['socket'] == 'fail')} diverge over the socket")

# The report, when asked for: written **before** the exit status is decided, so a diverging run — the run
# this tier is for — still leaves the document the contract reads. `corpus_given` is the path the caller
# passed rather than the absolute one the reading above uses: the report should name what was asked for, so
# it stays reproducible from the invocation. A row that never ran carries a row-level `detail` and no
# `divergences`, which is what keeps `unknown` meaning "the cause is unnameable" rather than "nothing ran".
if report_path:
    document = {"corpus": corpus_given, "vectors": []}
    for row in rows:
        entry = {"vector": row["vector"], "socket": row["socket"], "in_process": row["in_process"]}
        if row.get("detail"):
            entry["detail"] = row["detail"]
        if row["divergences"] is not None:
            entry["divergences"] = row["divergences"]
        document["vectors"].append(entry)
    try:
        pathlib.Path(report_path).write_text(json.dumps(document, indent=2) + "\n")
    except OSError as exc:
        print(f"wire-differential: could not write the report to {report_path}: {exc}", file=sys.stderr)
        sys.exit(3)

sys.exit(1 if any(row["socket"] != "pass" for row in rows) else 0)
PY
compare_status=$?

# A report that was asked for and **not** produced is a loud failure of this run, checked before the exit
# status is read: a `--report` invocation whose contract input silently did not appear would be exactly the
# near-silent failure this option exists to prevent. The comparator's own message (on stderr) says why. The
# confirmation that follows goes to stderr too, so the table and summary on stdout are byte-for-byte the
# run without the option.
if [ -n "$report" ]; then
  [ -s "$report" ] ||
    { printf 'wire-differential: FAIL: --report was given but no report was written to %s\n' "$report" >&2; exit 1; }
  printf 'wire-differential: report written to %s\n' "$report" >&2
fi

printf '\n'
printf 'wire-differential: socket replay of %s against the shipped endpoint (%s vector(s))\n' \
  "$corpus" "$vector_count"
if [ "$compare_status" = 0 ]; then
  printf 'wire-differential: PASS\n'
  exit 0
fi
printf 'wire-differential: FAIL (the divergences are named above, each with its step)\n'
exit 1
