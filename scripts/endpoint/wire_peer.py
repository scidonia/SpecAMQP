#!/usr/bin/env python3
"""The peer for R4's wire differential: one vector's other end, over a socket.

The endpoint under test is the shipped process; this is the peer it talks to. The driver
starts the endpoint, this script plays the vector's steps from the peer's side — writing
what the endpoint is meant to receive, reading (and comparing) what it is meant to send —
and reports one JSON line per step, so the driver can say *which* step diverged rather
than that the vector did.

A step is a JSON object in the exchange vocabulary:

    {"direction": "send",    "bytes": "…", "expect": {"state": "connection:HDR_SENT", "status": "admitted"}}
    {"direction": "receive", "bytes": "…", "expect": {"state": "connection:HDR_EXCH", "status": "admitted"}}

`direction` is from the **endpoint's** point of view: a `send` step is octets the endpoint
puts on the wire (this peer reads and compares them), a `receive` step is octets the peer
puts on the wire (this peer writes them). `expect.status` says whether the endpoint is
meant to accept the step or refuse it; a refused `send` step is one the endpoint must
*decline to write*, so the peer expects no octets and the refusal is looked for in the
endpoint's own narration, which is the corpus's vocabulary (`took <state>` / `refused …`).

Nothing here decides whether the endpoint was right: this script reports what happened,
and the driver compares that with the vector and with `amqp-spec`'s in-process answer.

`--coalesce` writes each maximal run of consecutive `receive` steps in **one** `sendall`, so
that two frames the vector puts on the wire back to back arrive in the endpoint as one read.
It exists because whether they do is otherwise a race the driver cannot vary: back-to-back
loopback writes issued by one process reach a reader that is already blocked in `recv` as
separate segments run after run, which is exactly why a verdict that turns on the difference
went unnoticed for as long as it did. Writing them as one segment is a peer the vector does
not forbid — the steps are semantic, not a segmentation — and it is what makes the difference
observable on demand rather than by chance.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import socket
import sys
import time

READ_TIMEOUT = 5.0  # a send step that does not arrive within this is reported, not waited for


def connect(port: int, deadline: float = 10.0) -> socket.socket:
    """Connect, retrying until the deadline: the endpoint is started by the driver, so a
    connection that arrives before the listener does is a race, not a failure."""
    end = time.monotonic() + deadline
    last: OSError | None = None
    while time.monotonic() < end:
        try:
            sock = socket.create_connection(("127.0.0.1", port), timeout=READ_TIMEOUT)
            sock.settimeout(READ_TIMEOUT)
            return sock
        except OSError as error:  # the listener is not up yet, or not yet accepting
            last = error
            time.sleep(0.05)
    raise SystemExit(f"peer: could not connect to 127.0.0.1:{port}: {last}")


def read_exactly(sock: socket.socket, count: int) -> tuple[bytes, bool]:
    """Read up to `count` octets, returning what arrived and whether the read timed out.

    A timeout is not an error here: it is the observation "the endpoint sent nothing", which
    is exactly what a divergent step looks like, and reporting it as a crash would lose the
    distinction between "sent the wrong octets" and "sent none".
    """
    got = bytearray()
    while len(got) < count:
        try:
            chunk = sock.recv(count - len(got))
        except socket.timeout:
            return bytes(got), True
        except OSError:
            return bytes(got), False
        if not chunk:
            return bytes(got), False
        got += chunk
    return bytes(got), False


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--port", type=int, required=True)
    parser.add_argument("--corpus", required=True, help="the vector file")
    parser.add_argument("--vector", required=True, help="the vector id to play")
    parser.add_argument("--report", required=True, help="where to write the per-step JSON lines")
    parser.add_argument("--coalesce", action="store_true",
                        help="write each run of consecutive `receive` steps in one sendall")
    args = parser.parse_args(argv)

    vectors = {}
    for line in pathlib.Path(args.corpus).read_text(encoding="utf-8").splitlines():
        if line.strip():
            entry = json.loads(line)
            vectors[entry["vector"]] = entry
    vector = vectors.get(args.vector)
    if vector is None:
        raise SystemExit(f"peer: {args.vector} is not in {args.corpus}")

    report = pathlib.Path(args.report)
    lines: list[str] = []
    # Which `receive` steps are written together. `group` maps the step that carries a run's write (1-based,
    # as the report numbers steps) to the octets of the whole run, and `joined` names, for every later step
    # of that run, the step whose write it went out in — so each step still reports itself, and one of them
    # reports the write.
    group: dict[int, bytes] = {}
    joined: dict[int, int] = {}
    alongside: dict[int, list[int]] = {}
    if args.coalesce:
        own = vector.get("steps", [])
        index = 0
        while index < len(own):
            if own[index].get("direction") == "receive":
                end = index
                while end + 1 < len(own) and own[end + 1].get("direction") == "receive":
                    end += 1
                if end > index:
                    group[index + 1] = b"".join(
                        bytes.fromhex(own[k]["bytes"]) for k in range(index, end + 1))
                    alongside[index + 1] = [k + 1 for k in range(index, end + 1)]
                    for k in range(index + 1, end + 1):
                        joined[k + 1] = index + 1
                index = end + 1
            else:
                index += 1
    sock = connect(args.port)
    try:
        # The shell announces the protocol header on **every** connection, so it is on the wire
        # before the vector's first step whatever the vector says. Reading it here, rather than
        # letting the first step read it, is what keeps the two cases apart: a vector whose first
        # step *is* the header compares against this read, and a vector that never mentions the
        # header does not have an unexplained eight octets arrive mid-dialogue.
        preamble, preamble_timeout = read_exactly(sock, 8)
        lines.append(json.dumps({
            "step": 0, "direction": "send", "status": "preamble", "observed": "endpoint header",
            "got": preamble.hex(), "timed_out": preamble_timeout, "bytes": "414d515000010000",
            "matched": preamble.hex() == "414d515000010000",
        }, sort_keys=True))
        # The header exchange is symmetric, and a vector may begin *after* it (`start: HDR_EXCH`): the
        # in-process runner has already sent its own header by then, so a peer that only reads the
        # endpoint's leaves the endpoint in HDR_SENT and the vector's first step unreachable. Send ours
        # when no step of the vector does — the header is eight octets opening `AMQP`, and which protocol
        # layer's header it is (the SASL layer's carries protocol id 3) is the vector's business, not this
        # prologue's.
        plain_header = "414d515000010000"
        sends_own_header = any(
            step.get("direction") == "receive" and (step.get("bytes") or "")[:8] == "414d5150"
            and len(step["bytes"]) == 16
            for step in vector.get("steps", []))
        if not sends_own_header:
            sock.sendall(bytes.fromhex(plain_header))
            lines.append(json.dumps({
                "step": 0, "direction": "receive", "status": "preamble", "observed": "sent own header",
                "bytes": plain_header, "written": 8,
                "note": "the vector begins after the header exchange; the peer sends its header first",
            }, sort_keys=True))
        for number, step in enumerate(vector.get("steps", []), 1):
            wire = bytes.fromhex(step["bytes"])
            expect = step.get("expect") or {}
            direction = step["direction"]
            if direction == "receive":
                if number in group:
                    sock.sendall(group[number])
                elif number in joined:
                    pass  # this step's octets went out in the same write as `joined[number]`'s
                else:
                    sock.sendall(wire)
                record = {
                    "step": number, "direction": direction, "status": expect.get("status", "admitted"),
                    "state": expect.get("state"), "bytes": step["bytes"],
                    "written": len(wire), "observed": "written",
                }
                if number in joined:
                    record["one_write_with_step"] = joined[number]
                elif number in group:
                    record["one_write_for_steps"] = alongside[number]
            elif direction == "send":
                if number == 1 and len(wire) == 8 and preamble:
                    # the vector's first step is the header, which was just read as the preamble
                    record = {
                        "step": number, "direction": direction,
                        "status": expect.get("status", "admitted"), "state": expect.get("state"),
                        "bytes": step["bytes"], "got": preamble.hex(),
                        "matched": preamble == wire,
                        "observed": "matched" if preamble == wire else "different octets",
                    }
                elif expect.get("status") == "refused":
                    # the endpoint must decline to write these octets; it must not send them
                    got, timed_out = read_exactly(sock, len(wire))
                    record = {
                        "step": number, "direction": direction, "status": "refused",
                        "state": expect.get("state"), "bytes": step["bytes"],
                        "got": got.hex(), "timed_out": timed_out,
                        "observed": "no octets" if not got else "octets written",
                    }
                else:
                    got, timed_out = read_exactly(sock, len(wire))
                    record = {
                        "step": number, "direction": direction, "status": "admitted",
                        "state": expect.get("state"), "bytes": step["bytes"],
                        "got": got.hex(), "timed_out": timed_out,
                        "matched": got == wire,
                        "observed": "matched" if got == wire else ("nothing arrived"
                                                                  if not got else "different octets"),
                    }
            else:
                raise SystemExit(f"peer: step {number} has direction {direction!r}")
            lines.append(json.dumps(record, sort_keys=True))
    finally:
        sock.close()
        report.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
