#!/usr/bin/env python3
"""Author the session settle/count probe corpus, and write it into `scripts/`.

    python3 scripts/gen/probe-session-settle-counts.py

The probe family exercises the sentences this slice carried that the staged corpus either does not
reach at all or reaches in one direction only:

  * `flow/field:delivery-count.4` — a receiver whose flow sets the field before the link's sender
    has attached (refused), and the same flow with the field omitted (the conforming form);
  * `.2`/`.3`'s presence half in the sending direction — our own flow naming the link and stopping
    before the delivery-count;
  * `.2`/`.3`'s value half in the sending direction — a flow whose count is not this endpoint's;
  * `transfer/field:settled.6`'s exemption — under our own `unsettled` negotiation a transfer we
    write may carry the flag when the delivery is aborted, and may not when it is not.

The vectors cite the clauses they are authored from, are deterministic, and are replayed by hand
rather than by a gate: this is a coder-owned probe, like `probe-link-flow-field-without-handle.ndjson`
beside it, and a promotion into `vectors/` is the planner's movement.
"""

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

from gen import slices, write_ndjson  # noqa: E402
from gen.slices import AMQP_FRAME  # noqa: E402

TRANSFER = "amqp-core-transport-v1.0-os.xml"
FLOW_COUNT_4 = f"{TRANSFER}#amqp:transport/section:performatives/type:flow/field:delivery-count.4"
FLOW_COUNT_2 = f"{TRANSFER}#amqp:transport/section:performatives/type:flow/field:delivery-count.2"
FLOW_COUNT_3 = f"{TRANSFER}#amqp:transport/section:performatives/type:flow/field:delivery-count.3"
SETTLED_6 = f"{TRANSFER}#amqp:transport/section:performatives/type:transfer/field:settled.6"
END_ON_ERROR = f"{TRANSFER}#amqp:transport/section:sessions.5"
SESSION_ERRORS = f"{TRANSFER}#amqp:transport/section:sessions.6"
INVALID = "amqp:invalid-field"


def s(state: str) -> str:
    return f"session:{state}"


def windows() -> dict:
    return {"next-incoming-id": {"type": "uint", "value": 0},
            "incoming-window": {"type": "uint", "value": 1000},
            "next-outgoing-id": {"type": "uint", "value": 0},
            "outgoing-window": {"type": "uint", "value": 1000}}


def main() -> int:
    t = slices.Corpus()
    unsettled = t.settle_mode("sender-settle-mode", "unsettled")
    vectors = []

    # `.4`: the peer is the link's receiver and this endpoint (the link's sender) has not attached,
    # so the peer's flow MUST NOT set the delivery-count.
    peer_receiver = t.receive_frame(AMQP_FRAME, t.attach_body(role=True, handle=0),
                                    state=s("MAPPED"), channel=1)
    vectors.append(slices.exchange(
        "probe-flow-count-before-sender-attach-set", start=s("MAPPED"),
        clauses=[FLOW_COUNT_4, END_ON_ERROR, SESSION_ERRORS],
        steps=[peer_receiver,
               t.refused("receive", reason="malformed", condition=INVALID, state=s("DISCARDING"),
                         body=t.body("flow", **windows(), handle={"type": "uint", "value": 0},
                                     **{"delivery-count": {"type": "uint", "value": 0},
                                        "link-credit": {"type": "uint", "value": 0}}),
                         channel=1)],
        note="`delivery-count.4`: the receiving link endpoint has not yet seen the sender's attach, "
             "so its flow MUST NOT set the field — it carries the field it must omit"))

    vectors.append(slices.exchange(
        "probe-flow-count-before-sender-attach-absent", start=s("MAPPED"),
        clauses=[FLOW_COUNT_4, FLOW_COUNT_3],
        steps=[peer_receiver,
               t.receive_frame(AMQP_FRAME,
                               t.body("flow", **windows(), handle={"type": "uint", "value": 0}),
                               state=s("MAPPED"), channel=1)],
        note="`delivery-count.4`'s conforming form: the same receiver's flow with the field omitted "
             "is what the clause requires before the sender's attach is seen"))

    # `.2`/`.3` in the sending direction: our own attach as the link's sender, then a flow naming
    # the link. The field is required, and what it carries is this endpoint's current count.
    own_sender = t.send_frame(AMQP_FRAME, t.attach_body(role=False, handle=0), state=s("MAPPED"),
                              channel=1)
    vectors.append(slices.exchange(
        "probe-flow-count-sent-absent", start=s("MAPPED"),
        clauses=[FLOW_COUNT_2, FLOW_COUNT_3, END_ON_ERROR, SESSION_ERRORS],
        steps=[own_sender,
               t.refused("send", reason="malformed", condition=INVALID, state=s("MAPPED"),
                         body=t.body("flow", **windows(), handle={"type": "uint", "value": 0}),
                         channel=1)],
        note="`delivery-count.2`/`.3`'s presence half, in the direction the corpus never reaches: a "
             "flow this endpoint writes that names the link MUST set the field"))

    vectors.append(slices.exchange(
        "probe-flow-count-sent-not-its-current", start=s("MAPPED"),
        clauses=[FLOW_COUNT_2, FLOW_COUNT_3, END_ON_ERROR, SESSION_ERRORS],
        steps=[own_sender,
               t.refused("send", reason="malformed", condition=INVALID, state=s("MAPPED"),
                         body=t.body("flow", **windows(), handle={"type": "uint", "value": 0},
                                     **{"delivery-count": {"type": "uint", "value": 5},
                                        "link-credit": {"type": "uint", "value": 0}}),
                         channel=1)],
        note="`delivery-count.2`/`.3`'s value half, same direction: the field MUST be this "
             "endpoint's current count, and five is not it"))

    # `settled.6`, in the direction this endpoint owns: our own attach negotiated `unsettled`, so a
    # transfer we write may carry the flag only when the delivery is aborted.
    own_unsettled = t.send_frame(AMQP_FRAME,
                                 t.attach_body(role=False, handle=0, snd_settle_mode=unsettled),
                                 state=s("MAPPED"), channel=1)
    peer_attach = t.receive_frame(AMQP_FRAME, t.attach_body(role=True, handle=0),
                                  state=s("MAPPED"), channel=1)
    peer_credit = t.receive_frame(AMQP_FRAME,
                                  t.flow_body(handle=0, delivery_count=0, link_credit=1),
                                  state=s("MAPPED"), channel=1)

    vectors.append(slices.exchange(
        "probe-settled-6-sent-aborted-exempt", start=s("MAPPED"),
        clauses=[SETTLED_6, END_ON_ERROR, SESSION_ERRORS],
        steps=[own_unsettled, peer_attach, peer_credit,
               t.send_frame(AMQP_FRAME, t.transfer_body(settled=True, aborted=True),
                            state=s("MAPPED"), channel=1, payload=b"a message")],
        note="`settled.6`'s own exemption: the flag is forbidden on a transfer under the "
             "`unsettled` choice unless the delivery is aborted, and this one is"))

    vectors.append(slices.exchange(
        "probe-settled-6-sent-refused", start=s("MAPPED"),
        clauses=[SETTLED_6, END_ON_ERROR, SESSION_ERRORS],
        steps=[own_unsettled, peer_attach, peer_credit,
               t.refused("send", reason="malformed", condition=INVALID, state=s("MAPPED"),
                         body=t.transfer_body(settled=True), channel=1, payload=b"a message")],
        note="`settled.6` in the direction this endpoint owns: the same transfer with no abort "
             "carries the flag the clause forbids"))

    # `links/doc:flow-control.u1`/`.u3` and `field:link-credit.u1` in the direction this endpoint
    # writes: as the link's sender, a flow it writes echoes the receiver's last known credit.
    vectors.append(slices.exchange(
        "probe-link-credit-echo-sent-not-the-last-known", start=s("MAPPED"),
        clauses=[f"{TRANSFER}#amqp:transport/section:links/doc:flow-control.u1",
                 f"{TRANSFER}#amqp:transport/section:links/doc:flow-control.u3",
                 f"{TRANSFER}#amqp:transport/section:performatives/type:flow/field:link-credit.u1",
                 END_ON_ERROR, SESSION_ERRORS],
        steps=[own_sender,
               t.receive_frame(AMQP_FRAME, t.attach_body(role=True, handle=0),
                               state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME,
                               t.flow_body(handle=0, delivery_count=0, link_credit=3),
                               state=s("MAPPED"), channel=1),
               t.refused("send", reason="malformed", condition=INVALID, state=s("MAPPED"),
                         body=t.body("flow", **windows(), handle={"type": "uint", "value": 0},
                                     **{"delivery-count": {"type": "uint", "value": 0},
                                        "link-credit": {"type": "uint", "value": 5}}),
                         channel=1)],
        note="link-credit's ownership in the sending direction: the sender's value is always the "
             "last known value indicated by the receiver, and five is not the three it was sent"))

    vectors.append(slices.exchange(
        "probe-link-credit-echo-sent-the-last-known", start=s("MAPPED"),
        clauses=[f"{TRANSFER}#amqp:transport/section:links/doc:flow-control.u1",
                 f"{TRANSFER}#amqp:transport/section:performatives/type:flow/field:link-credit.u1"],
        steps=[own_sender,
               t.receive_frame(AMQP_FRAME, t.attach_body(role=True, handle=0),
                               state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME,
                               t.flow_body(handle=0, delivery_count=0, link_credit=3),
                               state=s("MAPPED"), channel=1),
               t.send_frame(AMQP_FRAME,
                            t.body("flow", **windows(), handle={"type": "uint", "value": 0},
                                   **{"delivery-count": {"type": "uint", "value": 0},
                                      "link-credit": {"type": "uint", "value": 3}}),
                            state=s("MAPPED"), channel=1)],
        note="the same sentence's conforming form: the sender's flow echoes the three the receiver "
             "last indicated"))

    out = ROOT / "scripts" / "probe-session-settle-counts.ndjson"
    digest = write_ndjson(out, vectors)
    print(f"wrote {len(vectors)} probe vectors to {out.relative_to(ROOT)}")
    print(f"  sha256: {digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
