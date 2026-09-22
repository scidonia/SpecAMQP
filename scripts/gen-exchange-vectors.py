#!/usr/bin/env python3
"""The exchange corpus: the connection lifecycle as ordered steps.

    scripts/gen-exchange-vectors.py [--out vectors/generated-exchanges.ndjson]
                                    [--mutations PATH]

An exchange vector is not a frame vector with more frames: what a peer may send
depends on what it has already sent and received, so each step carries the direction,
the frame or octets, and the state the peer must be left in. The expectations here are
authored from the pinned artifacts' own tables — the Connection State Table (picture
24), the Connection State Diagram (picture 23), the Frame Dispatch Table (picture 10),
the Protocol Header Layout (picture 11) and the security section's SASL exchange
(pictures 3 and 6) — and never from the executable specification.

What the corpus covers:

  * the negotiation paths the state table permits, in both orders (client first,
    server first, pipelined open, and the pipelined close that walks OC_PIPE and
    CLOSE_PIPE), and both orders of the close handshake;
  * version negotiation's refusals: a header whose protocol id this peer does not
    speak, a version it does not speak, a header that is not a header, and a
    truncated one — each with the reason class the ambiguity register adopts
    (`unsupported` for a protocol id or version, `malformed` for octets that are not
    a header, `truncated` for too few octets);
  * the frame-ordering rules: `open` before the header exchange, a second `open`, two
    headers, a frame where the header belongs, a SASL frame outside the SASL dialogue,
    an AMQP frame inside it, and a frame refused in a state whose legal sends are `-`;
  * the `**` column, which is not the `*` column: a frame is admitted in OPEN_SENT or
    OPEN_PIPE because it conforms to the limits expected of every implementation (512
    octets, channel 0, before any negotiation), and exactly the same frame is admitted
    in OPENED once the peer's own `open` has raised those limits — so collapsing the
    two columns would lose the only place the table makes the peer's capabilities
    constrain the send;
  * the SASL ANONYMOUS phase on both sides, through the second header exchange to
    `open`, and the mechanism comparison the symbol type forces (exact, not
    case-folded);
  * the connection error conditions, all of them the one the artifact uses for
    wire-level refusals, with the specific cause in the reason class.

`--mutations` writes the control family to a separate path: a vector that asserts a
mutated state-table row (END permits a send) and which the peer must therefore refuse,
and a vector whose own expected state is wrong so that the harness's failure path is
exercised. Those are controls, not corpus: they are meant to fail, so they are written
where the operator asks for them rather than into the passing corpus.

Runs offline; the only input is the vendored artifacts under `spec/oasis/`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from xml.etree import ElementTree

ROOT = pathlib.Path(__file__).resolve().parent.parent
SPEC = ROOT / "spec" / "oasis"
TRANSPORT = "amqp-core-transport-v1.0-os.xml"
MESSAGING = "amqp-core-messaging-v1.0-os.xml"
SECURITY = "amqp-core-security-v1.0-os.xml"

STATE_TABLE = f"{TRANSPORT}#picture.24"
SESSION_STATES = f"{TRANSPORT}#amqp:transport/section:sessions.7"
SESSION_TRANSITIONS = f"{TRANSPORT}#picture.30"
BEGIN_ESTABLISHES = f"{TRANSPORT}#amqp:transport/section:sessions.3"
BEGIN_REMOTE_CHANNEL = f"{TRANSPORT}#amqp:transport/section:performatives/type:begin/field:remote-channel.2"
END_DISASSOCIATES = f"{TRANSPORT}#amqp:transport/section:sessions.5"
SESSION_ERRORS = f"{TRANSPORT}#amqp:transport/section:sessions.6"
IDLE_DISCARDS = f"{TRANSPORT}#amqp:transport/section:sessions.12"
TRANSFER_ONE_SECTION = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer.1"
DATA_SECTION = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:aborted.2"
ATTACH_MANDATORY = f"{TRANSPORT}#amqp:transport/section:performatives/type:attach/field:handle.1"
ATTACH_DEFAULTS = f"{TRANSPORT}#amqp:transport/section:performatives/type:attach/field:snd-settle-mode.1"
ATTACH_SETTLE_DEFAULT = f"{TRANSPORT}#amqp:transport/section:performatives/type:attach/field:rcv-settle-mode.1"
FLOW_NEXT_INCOMING_ID = f"{TRANSPORT}#amqp:transport/section:performatives/type:flow/field:next-incoming-id.1"

WINDOW_REMOTE_INCOMING = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.3"
WINDOW_INCOMING = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.5"
WINDOW_AFTER_SENDING = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.5"
WINDOW_AFTER_FLOW = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.7"
WINDOW_AFTER_RECEIVING = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.6"

CHANNEL_MAP = f"{TRANSPORT}#amqp:transport/section:connections.1"
STATE_DIAGRAM = f"{TRANSPORT}#picture.23"
DISPATCH_TABLE = f"{TRANSPORT}#picture.10"
HEADER_LAYOUT = f"{TRANSPORT}#picture.11"
SASL_HEADER_LAYOUT = f"{SECURITY}#picture.3"
SASL_EXCHANGE = f"{SECURITY}#picture.6"


def transport(anchor: str, index: int) -> str:
    return f"{TRANSPORT}#amqp:transport/section:{anchor}.{index}"


def security(anchor: str, index: int) -> str:
    return f"{SECURITY}#amqp:security/section:{anchor}.{index}"


HEADER_FIRST = transport("version-negotiation", 1)
HEADER_MISMATCH = transport("version-negotiation", 3)
UNSUPPORTED_VERSION = transport("version-negotiation", 9)
UNPARSABLE_HEADER = transport("version-negotiation", 12)
UNACCEPTABLE_PROTOCOL = transport("version-negotiation", 13)
PRE_NEGOTIATION_LIMITS = transport("connections", 1)
OPEN_ON_CHANNEL_ZERO = transport("connections", 2)
CLOSE_WRITTEN = transport("connections", 5)
CLOSE_LAST = transport("connections", 6)
CLOSE_ANY_CHANNEL = transport("connections", 9)
DISCARD_ON_ERROR = transport("connections", 16)
MAX_FRAME_SIZE = f"{TRANSPORT}#amqp:transport/section:performatives/type:open/field:max-frame-size.1"
OVERSIZED_FRAME = f"{TRANSPORT}#amqp:transport/section:performatives/type:open/field:max-frame-size.2"
CHANNEL_MAX = f"{TRANSPORT}#amqp:transport/section:performatives/type:open/field:channel-max.1"
CHANNEL_RANGE = f"{TRANSPORT}#amqp:transport/section:performatives/type:open/field:channel-max.2"
SASL_HEADER = security("sasl", 1)
SASL_FRAMES = security("sasl", 4)
SASL_SERVER_ANNOUNCES = security("sasl", 6)
SASL_PARTNER_CHOOSES = security("sasl", 7)
SASL_HIGHEST_PROFILE = f"{SECURITY}#amqp:security/section:sasl/type:sasl-init/field:mechanism.2"
SASL_OUTCOME_ESTABLISHES = f"{SECURITY}#amqp:security/section:sasl/type:sasl-outcome.1"

FRAME_HEADER = 8
FRAME_MIN_DOFF = 2
AMQP_FRAME = 0x00
SASL_FRAME = 0x01
MAGIC = b"AMQP"
FRAMING_ERROR = "amqp:connection:framing-error"
INVALID_FIELD = "amqp:invalid-field"
WINDOW_VIOLATION = "amqp:session:window-violation"
ILLEGAL_STATE = "amqp:illegal-state"


def c(state: str) -> str:
    """A connection state name, layer-prefixed as the schema requires."""
    return f"connection:{state}"


def s(state: str) -> str:
    """A session state name, layer-prefixed as the schema requires."""
    return f"session:{state}"


# --------------------------------------------------------------------------- #
# The artifacts: every number and name below is read, never typed
# --------------------------------------------------------------------------- #


def parse(artifact: str) -> ElementTree.Element:
    return ElementTree.parse(SPEC / artifact).getroot()


def declared_types(artifact: str) -> dict[str, ElementTree.Element]:
    return {t.get("name"): t for t in parse(artifact).iter("type") if t.get("name")}


def descriptor_code(element: ElementTree.Element) -> int:
    descriptor = next(element.iter("descriptor"))
    return int(descriptor.get("code").split(":")[1], 16)


def field_names(element: ElementTree.Element) -> list[str]:
    return [f.get("name") for f in element.iter("field")]


def field_default(element: ElementTree.Element, name: str) -> str | None:
    for field in element.iter("field"):
        if field.get("name") == name:
            return field.get("default")
    raise SystemExit(f"gen-exchange-vectors: {element.get('name')} has no field {name!r}")


def defined_constant(name: str) -> int:
    """A `<definition>` constant, resolved across artifacts the way the ledger does:
    the SASL versions live in the security artifact and are cited from there."""
    for artifact in (TRANSPORT, SECURITY):
        for definition in parse(artifact).iter("definition"):
            if definition.get("name") == name:
                return int(definition.get("value"))
    raise SystemExit(f"gen-exchange-vectors: no constant named {name!r}")


def choice_value(artifact: str, owner: str, name: str) -> int:
    """A choice's number, from the type that declares it: the SASL outcome code the
    corpus writes is the artifact's own `ok` value, not a remembered zero."""
    for element in parse(artifact).iter("type"):
        if element.get("name") == owner:
            for choice in element.iter("choice"):
                if choice.get("name") == name:
                    return int(choice.get("value"))
    raise SystemExit(f"gen-exchange-vectors: {owner} declares no choice {name!r}")


# --------------------------------------------------------------------------- #
# The AMQP type system, enough of it to write the frames the corpus carries
# --------------------------------------------------------------------------- #


def be(number: int, width: int) -> bytes:
    return number.to_bytes(width, "big")


def encode(value: dict) -> bytes:
    """One value in the narrowest constructor that carries it, which is the form the
    corpus's encoder writes and the frame layer's own corpus pins."""
    kind = value["type"]
    if kind == "null":
        return b"\x40"
    if kind == "boolean":
        return b"\x41" if value["value"] else b"\x42"
    if kind == "ubyte":
        return b"\x50" + bytes([value["value"]])
    if kind == "ushort":
        return b"\x60" + be(value["value"], 2)
    if kind == "uint":
        number = value["value"]
        if number == 0:
            return b"\x43"
        if number < 256:
            return b"\x52" + bytes([number])
        return b"\x70" + be(number, 4)
    if kind == "ulong":
        number = value["value"]
        if number == 0:
            return b"\x44"
        if number < 256:
            return b"\x53" + bytes([number])
        return b"\x80" + be(number, 8)
    if kind == "binary":
        payload = bytes.fromhex(value["hex"])
        if len(payload) < 256:
            return b"\xA0" + bytes([len(payload)]) + payload
        return b"\xB0" + be(len(payload), 4) + payload
    if kind in ("string", "symbol"):
        payload = value["text"].encode("utf-8")
        tag = 0xA1 if kind == "string" else 0xA3
        if len(payload) < 256:
            return bytes([tag]) + bytes([len(payload)]) + payload
        return bytes([tag | 0x10]) + be(len(payload), 4) + payload
    if kind == "list":
        items = b"".join(encode(item) for item in value["items"])
        if not value["items"]:
            return b"\x45"
        size = len(items) + 1
        if size < 256 and len(value["items"]) < 256:
            return b"\xC0" + bytes([size]) + bytes([len(value["items"])]) + items
        return b"\xC1" + be(size + 3, 4) + be(len(value["items"]), 4) + items
    if kind == "described":
        return b"\x00" + encode(value["descriptor"]) + encode(value["value"])
    raise SystemExit(f"gen-exchange-vectors: cannot encode a {kind!r}")


def described(code: int, items: list[dict]) -> dict:
    """A performative: a described value whose value is a field list. Trailing nulls
    are dropped, which is the rule a shorter list means the missing fields are null."""
    while items and items[-1] == {"type": "null"}:
        items.pop()
    return {"type": "described", "descriptor": {"type": "ulong", "value": code},
            "value": {"type": "list", "items": items}}


def frame_octets(frame_type: int, body: dict, channel: int = 0, payload: bytes = b"",
                 extended: bytes = b"", doff: int = FRAME_MIN_DOFF) -> bytes:
    """SIZE counts the whole frame, header included, and is computed rather than
    declared, so no vector can carry a SIZE that disagrees with its octets."""
    body_octets = encode(body)
    size = FRAME_HEADER + len(extended) + len(body_octets) + len(payload)
    return (be(size, 4) + bytes([doff, frame_type]) + be(channel, 2) + extended +
            body_octets + payload)


def payload_to_total(frame_type: int, body: dict, total: int) -> bytes:
    """A payload that brings a frame to exactly `total` octets, measured from the
    frame's own encoding rather than from a hand count: a length that is one octet out
    produces a vector that claims to exceed a limit it does not reach."""
    fixed = FRAME_HEADER + len(encode(body))
    if total < fixed:
        raise SystemExit(f"gen-exchange-vectors: a {total}-octet frame cannot carry "
                         f"{fixed} octets of header and performative")
    return b"\x2a" * (total - fixed)


def frame_value(frame_type: int, body: dict, channel: int = 0, payload: bytes = b"",
                extended: bytes = b"", doff: int = FRAME_MIN_DOFF) -> dict:
    """The same frame in the corpus's structural vocabulary, for a send step: the
    structure pins the request and SIZE is the count the peer's writer derives."""
    value: dict = {"doff": doff, "type": f"{frame_type:02x}", "channel": channel,
                   "body": [body]}
    if extended:
        value["extended"] = extended.hex()
    if payload:
        value["payload"] = payload.hex()
    return value


def protocol_header(protocol_id: int, major: int, minor: int, revision: int) -> bytes:
    return MAGIC + bytes([protocol_id, major, minor, revision])


# --------------------------------------------------------------------------- #
# The corpus
# --------------------------------------------------------------------------- #


class Corpus:
    """The tables the vectors are authored against, read once from the artifacts."""

    def __init__(self) -> None:
        transport = declared_types(TRANSPORT)
        security = declared_types(SECURITY)
        self.versions = {
            "amqp": (defined_constant("MAJOR"), defined_constant("MINOR"),
                     defined_constant("REVISION")),
            "sasl": (defined_constant("SASL-MAJOR"), defined_constant("SASL-MINOR"),
                     defined_constant("SASL-REVISION")),
            "tls": (defined_constant("TLS-MAJOR"), defined_constant("TLS-MINOR"),
                    defined_constant("TLS-REVISION")),
        }
        self.protocol_ids = {"amqp": 0, "tls": 2, "sasl": 3}
        self.min_max_frame_size = defined_constant("MIN-MAX-FRAME-SIZE")
        self.open_code = descriptor_code(transport["open"])
        self.close_code = descriptor_code(transport["close"])
        self.begin_code = descriptor_code(transport["begin"])
        self.sasl_mechanisms_code = descriptor_code(security["sasl-mechanisms"])
        self.sasl_init_code = descriptor_code(security["sasl-init"])
        self.sasl_outcome_code = descriptor_code(security["sasl-outcome"])
        self.begin_code = descriptor_code(transport["begin"])
        self.end_code = descriptor_code(transport["end"])
        self.attach_code = descriptor_code(transport["attach"])
        self.detach_code = descriptor_code(transport["detach"])
        self.flow_code = descriptor_code(transport["flow"])
        self.transfer_code = descriptor_code(transport["transfer"])
        # the `data` section is a messaging type: a transfer's payload is one, and the
        # session layer carries it without reading it
        self.data_code = descriptor_code(declared_types(MESSAGING)["data"])
        self.error_code = descriptor_code(transport["error"])
        self.codes = {"begin": self.begin_code, "end": self.end_code,
                      "attach": self.attach_code, "detach": self.detach_code,
                      "flow": self.flow_code, "transfer": self.transfer_code,
                      "data": self.data_code, "error": self.error_code}
        self.fields = {name: field_names(transport[name])
                       for name in ("begin", "end", "attach", "detach", "flow",
                                    "transfer", "error")}
        self.open_fields = field_names(transport["open"])
        self.mechanisms_fields = field_names(security["sasl-mechanisms"])
        self.init_fields = field_names(security["sasl-init"])
        self.outcome_fields = field_names(security["sasl-outcome"])
        self.max_frame_size_default = int(field_default(transport["open"], "max-frame-size"))
        self.channel_max_default = int(field_default(transport["open"], "channel-max"))
        self.sasl_ok = choice_value(SECURITY, "sasl-code", "ok")

    # -- frames ------------------------------------------------------------- #

    def header(self, layer: str, *, minor: int | None = None,
               protocol_id: int | None = None) -> bytes:
        major, minor_version, revision = self.versions[layer]
        return protocol_header(
            self.protocol_ids[layer] if protocol_id is None else protocol_id,
            major, minor_version if minor is None else minor, revision)

    def open_items(self, container: str, *, max_frame_size: int | None,
                   channel_max: int | None) -> list[dict]:
        """An `open`'s fields, in the artifact's declared order, with a field the
        vector leaves unset written as null so the peer's default applies."""
        values: dict[str, dict] = {
            "container-id": {"type": "string", "text": container},
            "hostname": {"type": "null"},
            "max-frame-size": ({"type": "uint", "value": max_frame_size}
                               if max_frame_size is not None else {"type": "null"}),
            "channel-max": ({"type": "ushort", "value": channel_max}
                            if channel_max is not None else {"type": "null"}),
            "idle-time-out": {"type": "null"},
            "outgoing-locales": {"type": "null"},
            "incoming-locales": {"type": "null"},
            "offered-capabilities": {"type": "null"},
            "desired-capabilities": {"type": "null"},
            "properties": {"type": "null"},
        }
        missing = [name for name in self.open_fields if name not in values]
        if missing:
            raise SystemExit(f"gen-exchange-vectors: open declares fields this corpus "
                             f"does not write: {missing}")
        return [values[name] for name in self.open_fields]

    def open_body(self, container: str = "client", *, max_frame_size: int | None = None,
                  channel_max: int | None = None) -> dict:
        return described(self.open_code,
                         self.open_items(container, max_frame_size=max_frame_size,
                                         channel_max=channel_max))

    def close_body(self) -> dict:
        return described(self.close_code, [])

    def body(self, type_name: str, **values: dict) -> dict:
        """A performative as a described value: the fields in the artifact's declared
        order, each one a value the vector sets or null where it leaves it unset, so a
        vector that omits a field writes what a sender that omitted it writes."""
        names = self.fields[type_name]
        unknown = [name for name in values if name not in names]
        if unknown:
            raise SystemExit(f"{type_name} declares no field {unknown}")
        return described(self.codes[type_name],
                         [values.get(name, {"type": "null"}) for name in names])

    def begin_body(self, remote_channel: int | None = None, next_outgoing: int = 0,
                   incoming: int = 1000, outgoing: int = 1000) -> dict:
        """A `begin`, whose three windows are mandatory: the vector sets them, because a
        begin that does not is not the performative its descriptor names."""
        return self.body("begin", **{
            "remote-channel": ({"type": "ushort", "value": remote_channel}
                               if remote_channel is not None else {"type": "null"}),
            "next-outgoing-id": {"type": "uint", "value": next_outgoing},
            "incoming-window": {"type": "uint", "value": incoming},
            "outgoing-window": {"type": "uint", "value": outgoing}})

    def transfer_body(self, handle: int = 0, delivery_id: int = 0,
                      delivery_tag: bytes = b"tag") -> dict:
        """A `transfer` of one unfragmented delivery: the handle it is mandatory, and
        `more` is left unset, which is the default and means the message is not split."""
        return self.body("transfer", handle={"type": "uint", "value": handle},
                         **{"delivery-id": {"type": "uint", "value": delivery_id},
                            "delivery-tag": {"type": "binary", "hex": delivery_tag.hex()},
                            "message-format": {"type": "uint", "value": 0}})

    def error(self, condition: str) -> dict:
        """An `error` composite: the condition, and no description."""
        return described(self.error_code,
                         [{"type": "symbol", "text": condition}, {"type": "null"}])

    def data_section(self, payload: bytes) -> bytes:
        """One `data` section: the message layer's described binary, which is what a
        transfer carries as its opaque payload. The session layer does not read it."""
        return encode(described(self.data_code, [{"type": "binary", "hex": payload.hex()}]))

    def mechanisms_body(self, mechanisms: list[str]) -> dict:
        return described(self.sasl_mechanisms_code,
                         [{"type": "symbol", "text": name} for name in mechanisms])

    def init_body(self, mechanism: str) -> dict:
        values: dict[str, dict] = {"mechanism": {"type": "symbol", "text": mechanism},
                                   "initial-response": {"type": "null"},
                                   "hostname": {"type": "null"}}
        return described(self.sasl_init_code,
                         [values[name] for name in self.init_fields])

    def outcome_body(self, code: int | None = None) -> dict:
        values: dict[str, dict] = {
            "code": {"type": "ubyte", "value": self.sasl_ok if code is None else code},
            "additional-data": {"type": "null"}}
        return described(self.sasl_outcome_code,
                         [values[name] for name in self.outcome_fields])

    # -- steps -------------------------------------------------------------- #

    def send_header(self, layer: str, *, state: str = c("HDR_SENT"), **kwargs) -> dict:
        return {"direction": "send", "bytes": self.header(layer, **kwargs).hex(),
                "expect": {"status": "admitted", "state": state}}

    def receive_header(self, layer: str, *, state: str | None, **kwargs) -> dict:
        step = {"direction": "receive", "bytes": self.header(layer, **kwargs).hex(),
                "expect": {"status": "admitted"}}
        if state is not None:
            step["expect"]["state"] = state
        return step

    def send_frame(self, frame_type: int, body: dict, *, state: str, channel: int = 0,
                   payload: bytes = b"") -> dict:
        return {"direction": "send",
                "value": frame_value(frame_type, body, channel=channel, payload=payload),
                "expect": {"status": "admitted", "state": state}}

    def receive_frame(self, frame_type: int, body: dict, *, state: str | None,
                      channel: int = 0, payload: bytes = b"") -> dict:
        step = {"direction": "receive",
                "bytes": frame_octets(frame_type, body, channel=channel,
                                      payload=payload).hex(),
                "expect": {"status": "admitted"}}
        if state is not None:
            step["expect"]["state"] = state
        return step

    def refused(self, direction: str, *, reason: str, state: str | None,
                condition: str = FRAMING_ERROR,
                body: dict | None = None, frame_type: int = AMQP_FRAME,
                channel: int = 0, payload: bytes = b"", octets: bytes | None = None,
                note: str = "") -> dict:
        """A step the peer must not take. A `receive` carries octets; a `send` carries
        the frame it is asked to send, and produces nothing because the peer must not
        write it at all. Every refusal the connection layer raises carries the one
        condition the artifact uses for wire-level failures, so the cause is the reason
        class rather than a condition per failure."""
        expect: dict = {"status": "refused", "condition": condition, "reason": reason}
        if state is not None:
            expect["state"] = state
        if direction == "receive":
            octets = octets if octets is not None else frame_octets(
                frame_type, body, channel=channel, payload=payload)
            step = {"direction": "receive", "bytes": octets.hex(), "expect": expect}
        else:
            step = {"direction": "send",
                    "value": frame_value(frame_type, body, channel=channel, payload=payload),
                    "expect": expect}
        if note:
            step["note"] = note
        return step

    def refused_close_in_end(self, note: str = "") -> dict:
        """A `close` offered to a connection that is over: END's legal receives are `-`,
        so what arrives there is refused and the end stands."""
        return self.refused(
            "receive", reason="illegalState", state=c("END"), body=self.close_body(),
            note=note or "END's legal receives are `-`: the connection is over, and "
                         "nothing can arrive on it")

    def refused_header_in_end(self, note: str = "") -> dict:
        """A header offered to a connection that is over, on the same terms."""
        return self.refused(
            "receive", reason="illegalState", state=c("END"), octets=self.header("amqp"),
            note=note or "END's legal receives are `-`: the connection is over, so not "
                         "even a header arrives on it")


def exchange(vector: str, *, start: str, steps: list[dict], clauses: list[str],
             note: str) -> dict:
    return {"vector": vector, "kind": "exchange", "clauses": clauses, "start": start,
            "steps": steps, "note": note}


def corpus(tables: Corpus) -> list[dict]:
    t = tables
    vectors: list[dict] = []

    open0 = t.open_body()
    open_defaults = t.open_body("server")            # every limit left to its default
    open_wide = t.open_body("server", max_frame_size=t.max_frame_size_default,
                            channel_max=t.channel_max_default)

    # -- the negotiation paths the table permits ---------------------------- #

    vectors.append(exchange(
        "exchange-client-open", start=c("START"), clauses=[STATE_TABLE, STATE_DIAGRAM,
                                                        HEADER_LAYOUT, OPEN_ON_CHANNEL_ZERO],
        steps=[t.send_header("amqp"), t.receive_header("amqp", state=c("HDR_EXCH")),
               t.send_frame(AMQP_FRAME, open0, state=c("OPEN_SENT")),
               t.receive_frame(AMQP_FRAME, open_defaults, state=c("OPENED"))],
        note="the client's order: header out, header in, open out, open in. The table's "
             "START sends HDR, HDR_SENT receives HDR, HDR_EXCH sends OPEN, and OPEN_SENT "
             "receives OPEN, which is the whole path from START to OPENED"))

    vectors.append(exchange(
        "exchange-server-open", start=c("START"), clauses=[STATE_TABLE, STATE_DIAGRAM,
                                                        HEADER_LAYOUT, OPEN_ON_CHANNEL_ZERO],
        steps=[t.receive_header("amqp", state=c("HDR_RCVD")),
               t.send_header("amqp", state=c("HDR_EXCH")),
               t.receive_frame(AMQP_FRAME, open0, state=c("OPEN_RCVD")),
               t.send_frame(AMQP_FRAME, open_defaults, state=c("OPENED"))],
        note="the server's order, which the table permits equally: it may wait for the "
             "incoming header before sending its own, so HDR_RCVD comes first and "
             "OPEN_RCVD precedes OPENED"))

    vectors.append(exchange(
        "exchange-pipelined-open", start=c("START"),
        clauses=[STATE_TABLE, STATE_DIAGRAM, PRE_NEGOTIATION_LIMITS, OPEN_ON_CHANNEL_ZERO],
        steps=[t.send_header("amqp"),
               t.send_frame(AMQP_FRAME, open0, state=c("OPEN_PIPE")),
               t.receive_header("amqp", state=c("OPEN_SENT")),
               t.receive_frame(AMQP_FRAME, open_defaults, state=c("OPENED"))],
        note="a pipelined open: the open is sent before the partner's header arrives, so "
             "HDR_SENT sends OPEN into OPEN_PIPE, whose legal receives are HDR, and the "
             "matching header then lands in OPEN_SENT"))

    vectors.append(exchange(
        "exchange-pipelined-close", start=c("START"),
        clauses=[STATE_TABLE, STATE_DIAGRAM, CLOSE_WRITTEN, CLOSE_LAST, CLOSE_ANY_CHANNEL],
        steps=[t.send_header("amqp"),
               t.send_frame(AMQP_FRAME, open0, state=c("OPEN_PIPE")),
               t.send_frame(AMQP_FRAME, t.close_body(), state=c("OC_PIPE")),
               t.receive_header("amqp", state=c("CLOSE_PIPE")),
               t.receive_frame(AMQP_FRAME, open_defaults, state=c("CLOSE_SENT")),
               t.receive_frame(AMQP_FRAME, t.close_body(), state=c("END"))],
        note="the pipelined close: OPEN_PIPE sends the close into OC_PIPE, which sends "
             "nothing at all, and the partner's header and open walk it through "
             "CLOSE_PIPE and CLOSE_SENT to END — the table's `-` column on the send side"))

    vectors.append(exchange(
        "exchange-close-sent-first", start=c("OPENED"),
        clauses=[STATE_TABLE, CLOSE_WRITTEN, CLOSE_LAST],
        steps=[t.send_frame(AMQP_FRAME, t.close_body(), state=c("CLOSE_SENT")),
               t.receive_frame(AMQP_FRAME, t.close_body(), state=c("END"))],
        note="an orderly close we initiate: OPENED sends CLOSE into CLOSE_SENT, whose "
             "legal sends are `-`, and the partner's close ends the connection"))

    vectors.append(exchange(
        "exchange-close-received-first", start=c("OPENED"),
        clauses=[STATE_TABLE, CLOSE_WRITTEN, CLOSE_LAST, CLOSE_ANY_CHANNEL],
        steps=[t.receive_frame(AMQP_FRAME, t.close_body(), state=c("CLOSE_RCVD")),
               t.send_frame(AMQP_FRAME, t.close_body(), state=c("END"))],
        note="the partner closes first: OPENED receives CLOSE into CLOSE_RCVD, which "
             "receives nothing (`-`) but may still send, and our close ends it"))

    # -- version negotiation's refusals ------------------------------------- #

    vectors.append(exchange(
        "exchange-header-protocol-id-unsupported", start=c("START"),
        clauses=[STATE_TABLE, HEADER_LAYOUT, UNACCEPTABLE_PROTOCOL],
        steps=[t.refused("receive", reason="unsupported",
                         state=c("END"), octets=t.header("tls"),
                         note="protocol id two is the TLS layer's; this peer speaks "
                              "protocol id zero and three, so the request is for a "
                              "protocol it does not speak"),
               t.refused_header_in_end()],
        note="an unacceptable protocol id: the octets are a perfectly good protocol "
             "header, and the refusal is that this peer does not speak that protocol"))

    vectors.append(exchange(
        "exchange-header-protocol-id-unassigned", start=c("START"),
        clauses=[STATE_TABLE, HEADER_LAYOUT, UNACCEPTABLE_PROTOCOL],
        steps=[t.refused("receive", reason="unsupported",
                         state=c("END"), octets=t.header("amqp", protocol_id=9),
                         note="protocol id nine is assigned by nothing: it is refused as "
                              "a protocol this peer does not speak, not as octets that "
                              "are not a header"),
               t.refused_header_in_end()],
        note="an unassigned protocol id, refused with the same condition and the same "
             "class as the TLS one, because both are protocol ids this peer does not "
             "speak rather than malformed headers"))

    vectors.append(exchange(
        "exchange-header-version-unsupported", start=c("START"),
        clauses=[STATE_TABLE, HEADER_LAYOUT, UNSUPPORTED_VERSION, MAX_FRAME_SIZE],
        steps=[t.refused("receive", reason="unsupported",
                         state=c("END"), octets=t.header("amqp", minor=1),
                         note="major one minor one is a version this peer does not "
                              "speak; the artifact states 1.0.0 and the peer supports "
                              "exactly what the artifact states"),
               t.refused_header_in_end()],
        note="a well-formed header for a version this peer does not speak"))

    vectors.append(exchange(
        "exchange-header-truncated", start=c("START"),
        clauses=[STATE_TABLE, HEADER_LAYOUT, UNPARSABLE_HEADER],
        steps=[t.refused("receive", reason="truncated",
                         state=c("END"), octets=t.header("amqp")[:7],
                         note="seven octets where the header is eight"),
               t.refused_header_in_end()],
        note="a truncated protocol header: fewer octets than the layout's fixed width, "
             "which is a different failure from a header whose bytes mean nothing"))

    vectors.append(exchange(
        "exchange-header-malformed", start=c("START"),
        clauses=[STATE_TABLE, HEADER_LAYOUT, UNPARSABLE_HEADER],
        steps=[t.refused("receive", reason="malformed",
                         state=c("END"), octets=b"HTCP" + t.header("amqp")[4:],
                         note="the version negotiation example's HTTP case: eight octets "
                              "that are not a protocol header, so the negotiation fails "
                              "before any version can be compared"),
               t.refused_header_in_end()],
        note="octets that are not a protocol header at all: the ambiguity register's "
             "malformed, as distinct from a header for a protocol or version this peer "
             "does not speak"))

    # -- the ordering rules ------------------------------------------------- #

    vectors.append(exchange(
        "exchange-open-before-header", start=c("START"),
        clauses=[STATE_TABLE, HEADER_FIRST, PRE_NEGOTIATION_LIMITS],
        steps=[t.refused("send", reason="illegalState",
                         state=c("START"), body=open0,
                         note="the first frame on a connection is the open, but the "
                              "protocol header precedes every frame, and START's legal "
                              "send is HDR alone"),
               t.send_header("amqp")],
        note="an open offered before the header exchange: the octets are a legal open "
             "frame and the moment is wrong"))

    vectors.append(exchange(
        "exchange-open-twice", start=c("HDR_EXCH"),
        clauses=[STATE_TABLE, HEADER_FIRST, OPEN_ON_CHANNEL_ZERO],
        steps=[t.send_frame(AMQP_FRAME, open0, state=c("OPEN_SENT")),
               t.refused("send", reason="illegalState",
                         state=c("OPEN_SENT"), body=open0,
                         note="the table's OPEN_SENT column is `**`, and a second open "
                              "is not a frame known a priori to conform: the open is "
                              "the first frame a peer sends, once")],
        note="a second open: admitted by a reading that takes `**` for `*`, refused by "
             "the artifact's rule that the first frame is the open"))

    vectors.append(exchange(
        "exchange-open-on-channel-one-send", start=c("HDR_EXCH"),
        clauses=[STATE_TABLE, OPEN_ON_CHANNEL_ZERO],
        steps=[t.refused("send", reason="illegalState",
                         state=c("HDR_EXCH"), body=open0, channel=1,
                         note="the open frame can only be sent on channel 0"),
               t.send_frame(AMQP_FRAME, open0, state=c("OPEN_SENT"))],
        note="an open offered on channel one: legal octets, wrong channel"))

    vectors.append(exchange(
        "exchange-open-on-channel-one-receive", start=c("HDR_EXCH"),
        clauses=[STATE_TABLE, OPEN_ON_CHANNEL_ZERO, CHANNEL_RANGE],
        steps=[t.refused("receive", reason="illegalState",
                         state=c("DISCARDING"), body=open0, channel=1,
                         note="a received open on channel one: the connection is in "
                              "error, so the peer closes and then discards what arrives "
                              "until the partner's close"),
               t.receive_frame(AMQP_FRAME, t.close_body(), state=c("END"))],
        note="the same rule in the receive direction, where the consequence is the "
             "error-triggered close of the DISCARDING state"))

    vectors.append(exchange(
        "exchange-frame-where-header-belongs", start=c("START"),
        clauses=[STATE_TABLE, HEADER_FIRST, UNPARSABLE_HEADER],
        steps=[t.refused("receive", reason="malformed",
                         state=c("END"), body=open0,
                         note="START's legal receive is the protocol header, so these "
                              "octets — a frame — are not a header, and that is what "
                              "the refusal reports"),
               t.refused_header_in_end()],
        note="a frame where the header belongs: the octets parse as a frame perfectly "
             "well, which is exactly why the failure is named by what was expected "
             "rather than by what arrived"))

    vectors.append(exchange(
        "exchange-two-headers", start=c("START"),
        clauses=[STATE_TABLE, STATE_DIAGRAM, HEADER_MISMATCH],
        steps=[t.receive_header("amqp", state=c("HDR_RCVD")),
               t.refused("receive", reason="illegalState",
                         state=c("DISCARDING"), octets=t.header("amqp"),
                         note="HDR_RCVD's legal receive is OPEN: a second header is not "
                              "a frame the state permits, and nothing is sent twice")],
        note="the header exchange happens once: a second header in HDR_RCVD is refused "
             "although its octets are identical to the first"))

    vectors.append(exchange(
        "exchange-header-mismatch-in-hdr-sent", start=c("HDR_SENT"),
        clauses=[STATE_TABLE, HEADER_MISMATCH, UNACCEPTABLE_PROTOCOL],
        steps=[t.refused("receive", reason="unsupported",
                         state=c("END"), octets=t.header("sasl"),
                         note="the incoming header asks for the SASL layer while this "
                              "exchange is the AMQP one, which is the table's "
                              "R:HDR[!=S:HDR] arrow to END"),
               t.refused_header_in_end()],
        note="a header that does not match what this peer sent: the mismatch arrow the "
             "state diagram draws to END"))

    # -- `**` is not `*` ---------------------------------------------------- #

    vectors.append(exchange(
        "exchange-conforming-frame-in-open-sent", start=c("OPEN_SENT"),
        clauses=[STATE_TABLE, CLOSE_WRITTEN, PRE_NEGOTIATION_LIMITS],
        steps=[t.send_frame(AMQP_FRAME, t.close_body(), state=c("CLOSE_PIPE")),
               t.refused("send", reason="illegalState", state=c("CLOSE_PIPE"),
                         body=t.close_body(),
                         note="CLOSE_PIPE's legal sends are `-`: the close has been "
                              "written, and nothing is written after it")],
        note="OPEN_SENT's legal sends are `**`: a close within the limits every "
             "implementation must accept may be pipelined before the partner's open "
             "arrives, and the state diagram's OPEN_SENT --S:CLOSE--> CLOSE_PIPE says "
             "where it lands"))

    vectors.append(exchange(
        "exchange-frame-in-end-refused", start=c("END"),
        clauses=[STATE_TABLE, CLOSE_WRITTEN, CLOSE_LAST],
        steps=[t.refused("send", reason="illegalState",
                         state=c("END"), body=t.close_body(),
                         note="END's legal sends are `-`: the same close the previous "
                              "vector admits in OPEN_SENT is refused here, which is the "
                              "difference between the table's two columns"),
               t.refused_close_in_end()],
        note="the same frame in a state whose legal sends are `-`: the pair that shows "
             "`**` is not `-`, and neither is `*`"))

    vectors.append(exchange(
        "exchange-pipelined-channel-limit", start=c("START"),
        clauses=[STATE_TABLE, STATE_DIAGRAM, DISPATCH_TABLE, PRE_NEGOTIATION_LIMITS,
                 CHANNEL_MAX, CHANNEL_RANGE, SESSION_STATES],
        steps=[t.send_header("amqp"),
               t.send_frame(AMQP_FRAME, open_wide, state=c("OPEN_PIPE")),
               t.refused("send", reason="limit",
                         state=c("OPEN_PIPE"), body=t.transfer_body(), channel=1,
                         note="before any explicit negotiation the maximum channel "
                              "number is zero, so a frame pipelined onto channel one is "
                              "not known a priori to conform"),
               t.receive_header("amqp", state=c("OPEN_SENT")),
               t.receive_frame(AMQP_FRAME, open_wide, state=c("OPENED")),
               t.send_frame(AMQP_FRAME, t.begin_body(), state=s("BEGIN_SENT"), channel=1),
               t.receive_frame(AMQP_FRAME, t.begin_body(remote_channel=1), state=s("MAPPED"),
                               channel=1),
               t.send_frame(AMQP_FRAME, t.transfer_body(), state=s("MAPPED"), channel=1,
                            payload=t.data_section(b"one section"))],
        note="the same channel-one frame, refused and then admitted: refused while the "
             "peer's open is still unknown, because the a priori limit is channel zero "
             "and the table's `**` column admits only what is known a priori to conform; "
             "admitted once the peer's open has raised the channel maximum and the "
             "session's own begin has mapped the channel — the one place `**` differs "
             "from `*`"))

    vectors.append(exchange(
        "exchange-pipelined-frame-size-limit", start=c("START"),
        clauses=[STATE_TABLE, STATE_DIAGRAM, PRE_NEGOTIATION_LIMITS, MAX_FRAME_SIZE,
                 OVERSIZED_FRAME, TRANSFER_ONE_SECTION],
        steps=[t.send_header("amqp"),
               t.send_frame(AMQP_FRAME, open_wide, state=c("OPEN_PIPE")),
               t.refused("send", reason="limit",
                         state=c("OPEN_PIPE"), body=t.transfer_body(),
                         payload=payload_to_total(AMQP_FRAME, t.transfer_body(),
                                                  t.min_max_frame_size + 1),
                         note="the frame totals one octet more than MIN-MAX-FRAME-SIZE, "
                              "the size both peers must accept and the only size known "
                              "before the partner's open arrives"),
               t.receive_header("amqp", state=c("OPEN_SENT")),
               t.receive_frame(AMQP_FRAME, open_wide, state=c("OPENED")),
               t.send_frame(AMQP_FRAME, t.begin_body(), state=s("BEGIN_SENT"), channel=1),
               t.receive_frame(AMQP_FRAME, t.begin_body(remote_channel=1), state=s("MAPPED"),
                               channel=1),
               t.send_frame(AMQP_FRAME, t.transfer_body(), state=s("MAPPED"), channel=1,
                            payload=payload_to_total(AMQP_FRAME, t.transfer_body(),
                                                     t.min_max_frame_size + 1))],
        note="the same oversized frame: refused in OPEN_PIPE and admitted in OPENED, "
             "because the peer's open replaced the a priori maximum frame size with its "
             "own — and once the session has mapped the channel, the frame the connection "
             "would not carry before is the one it carries now"))

    vectors.append(exchange(
        "exchange-oversized-frame-received", start=c("START"),
        clauses=[STATE_TABLE, MAX_FRAME_SIZE, OVERSIZED_FRAME],
        steps=[t.send_header("amqp"),
               t.send_frame(AMQP_FRAME,
                            t.open_body(max_frame_size=t.min_max_frame_size),
                            state=c("OPEN_PIPE")),
               t.receive_header("amqp", state=c("OPEN_SENT")),
               t.receive_frame(AMQP_FRAME, open_wide, state=c("OPENED")),
               t.refused("receive", reason="limit",
                         state=c("DISCARDING"), body=t.transfer_body(), channel=1,
                         payload=payload_to_total(AMQP_FRAME, t.transfer_body(),
                                                  t.min_max_frame_size + 1),
                         note="this peer announced a maximum frame size of "
                              "MIN-MAX-FRAME-SIZE, and the partner sent one octet more: "
                              "a peer that receives an oversized frame must close the "
                              "connection with the framing-error error-code")],
        note="the receive side of the same limit, where it is this peer's own open that "
             "sets the bound and the consequence is the error-triggered close"))

    # -- the SASL layer ----------------------------------------------------- #

    vectors.append(exchange(
        "exchange-sasl-anonymous-to-open", start=c("START"),
        clauses=[STATE_TABLE, SASL_HEADER, SASL_FRAMES, SASL_SERVER_ANNOUNCES,
                 SASL_PARTNER_CHOOSES, SASL_OUTCOME_ESTABLISHES, SASL_HEADER_LAYOUT,
                 SASL_EXCHANGE],
        steps=[t.send_header("sasl"),
               t.receive_header("sasl", state=c("HDR_EXCH")),
               t.receive_frame(SASL_FRAME, t.mechanisms_body(["ANONYMOUS"]), state=None),
               t.send_frame(SASL_FRAME, t.init_body("ANONYMOUS"), state=c("HDR_EXCH")),
               t.receive_frame(SASL_FRAME, t.outcome_body(), state=c("START")),
               t.send_header("amqp"),
               t.receive_header("amqp", state=c("HDR_EXCH")),
               t.send_frame(AMQP_FRAME, open0, state=c("OPEN_SENT")),
               t.receive_frame(AMQP_FRAME, open_defaults, state=c("OPENED"))],
        note="the SASL client's side of ANONYMOUS: protocol id three, the header "
             "exchange again, the mechanisms the server announces, our init, the "
             "outcome, and then — because a successful outcome establishes the layer "
             "and the peers must exchange protocol headers again — protocol id zero, the "
             "header exchange, and open"))

    vectors.append(exchange(
        "exchange-sasl-anonymous-server", start=c("START"),
        clauses=[STATE_TABLE, SASL_HEADER, SASL_FRAMES, SASL_SERVER_ANNOUNCES,
                 SASL_PARTNER_CHOOSES, SASL_OUTCOME_ESTABLISHES, SASL_HEADER_LAYOUT],
        steps=[t.receive_header("sasl", state=c("HDR_RCVD")),
               t.send_header("sasl", state=c("HDR_EXCH")),
               t.send_frame(SASL_FRAME, t.mechanisms_body(["ANONYMOUS"]), state=c("HDR_EXCH")),
               t.receive_frame(SASL_FRAME, t.init_body("ANONYMOUS"), state=c("HDR_EXCH")),
               t.send_frame(SASL_FRAME, t.outcome_body(), state=c("START")),
               t.receive_header("amqp", state=c("HDR_RCVD")),
               t.send_header("amqp", state=c("HDR_EXCH")),
               t.receive_frame(AMQP_FRAME, open0, state=c("OPEN_RCVD")),
               t.send_frame(AMQP_FRAME, open_defaults, state=c("OPENED"))],
        note="the SASL server's side of the same exchange: it announces the mechanisms "
             "and sends the outcome half of the dialogue, and the protocol header "
             "exchange after the outcome happens in the same order a plain server's "
             "does"))

    vectors.append(exchange(
        "exchange-sasl-mechanism-not-offered", start=c("START"),
        clauses=[STATE_TABLE, SASL_SERVER_ANNOUNCES, SASL_HIGHEST_PROFILE, SASL_EXCHANGE],
        steps=[t.receive_header("sasl", state=c("HDR_RCVD")),
               t.send_header("sasl", state=c("HDR_EXCH")),
               t.send_frame(SASL_FRAME, t.mechanisms_body(["ANONYMOUS"]), state=c("HDR_EXCH")),
               t.refused("receive", reason="unsupported",
                         frame_type=SASL_FRAME, body=t.init_body("PLAIN"),
                         state=c("END"),
                         note="this peer announced ANONYMOUS and nothing else, so an "
                              "init naming PLAIN selects a mechanism it does not "
                              "support. The layer is not established, so there is no "
                              "AMQP close to write: the transport is cut, which is END")],
        note="a mechanism the peer did not announce: the clause requires the receiving "
             "peer to close, and the close-code it names has no value in the generated "
             "choice table, so the refusal carries the one connection-error the artifact "
             "does use and the reason class says what was unsupported"))

    vectors.append(exchange(
        "exchange-sasl-mechanism-case-sensitive", start=c("START"),
        clauses=[STATE_TABLE, SASL_PARTNER_CHOOSES, SASL_HIGHEST_PROFILE, SASL_EXCHANGE],
        steps=[t.receive_header("sasl", state=c("HDR_RCVD")),
               t.send_header("sasl", state=c("HDR_EXCH")),
               t.send_frame(SASL_FRAME, t.mechanisms_body(["ANONYMOUS"]), state=c("HDR_EXCH")),
               t.refused("receive", reason="unsupported",
                         frame_type=SASL_FRAME, body=t.init_body("anonymous"),
                         state=c("END"),
                         note="a mechanism is a symbol, and a symbol is compared octet "
                              "for octet: lower-case anonymous is not ANONYMOUS, and no "
                              "clause anywhere makes mechanism names case-insensitive")],
        note="the mechanism comparison the symbol type forces: the same letters in "
             "another case are a different symbol and therefore a mechanism the peer "
             "did not offer"))

    vectors.append(exchange(
        "exchange-sasl-frame-before-header", start=c("START"),
        clauses=[STATE_TABLE, SASL_HEADER, SASL_FRAMES],
        steps=[t.refused("send", reason="illegalState",
                         frame_type=SASL_FRAME, body=t.mechanisms_body(["ANONYMOUS"]),
                         state=c("START"),
                         note="START's legal send is the protocol header, and the SASL "
                              "layer is established by a header with protocol id three "
                              "before any SASL frame"),
               t.send_header("sasl")],
        note="a SASL frame offered before the header exchange: the layer does not exist "
             "yet"))

    vectors.append(exchange(
        "exchange-amqp-frame-in-sasl-layer", start=c("START"),
        clauses=[STATE_TABLE, SASL_HEADER, SASL_FRAMES, OPEN_ON_CHANNEL_ZERO],
        steps=[t.send_header("sasl"),
               t.receive_header("sasl", state=c("HDR_EXCH")),
               t.refused("send", reason="illegalState",
                         state=c("HDR_EXCH"), body=open0,
                         note="the SASL dialogue is not finished, so the AMQP layer's "
                              "open is not a frame of this layer: the outcome must "
                              "arrive and the protocol headers be exchanged again")],
        note="an AMQP performative inside the SASL layer, which is the layer transition "
             "rule the security section states and the corpus can observe"))

    vectors.append(exchange(
        "exchange-sasl-frame-in-amqp-layer", start=c("START"),
        clauses=[STATE_TABLE, SASL_FRAMES, SASL_HEADER],
        steps=[t.receive_header("amqp", state=c("HDR_RCVD")),
               t.send_header("amqp", state=c("HDR_EXCH")),
               t.refused("receive", reason="illegalState",
                         state=c("DISCARDING"),
                         frame_type=SASL_FRAME, body=t.mechanisms_body(["ANONYMOUS"]),
                         note="this exchange is the AMQP layer's: HDR_EXCH's legal "
                              "receive is OPEN, and a SASL frame is not it")],
        note="a SASL frame in the AMQP layer, refused in the receive direction where "
             "the consequence is the error-triggered close"))

    # -- DISCARDING, whose receives are discarded rather than answered ------ #

    vectors.append(exchange(
        "exchange-discarding-ignores-frames", start=c("DISCARDING"),
        clauses=[STATE_TABLE, DISPATCH_TABLE, DISCARD_ON_ERROR, CLOSE_LAST],
        steps=[t.receive_frame(AMQP_FRAME, t.close_body(), state=c("END")),
               t.refused("send", reason="illegalState",
                         state=c("END"), body=t.close_body(),
                         note="END's legal sends are `-`: once the partner's close has "
                              "arrived the connection is over, and nothing is written "
                              "after it")],
        note="DISCARDING receives `*` and answers nothing: the frames it receives are "
             "discarded until the partner's close arrives, and that close is what ends "
             "the connection, after which nothing is written"))

    return vectors


def session_corpus(tables: Corpus) -> list[dict]:
    """The session family: `begin`/`end`, `attach`/`detach`, `flow` and `transfer` on a
    channel, from the session section's state descriptions, its transitions picture and
    the field tables the generated surface carries.

    A vector here begins at a `session:` state, which the interface reads as the
    connection being `OPENED` with both `open`s exchanged with their fields unset — so a
    session can be exercised without replaying the connection handshake, and a vector
    that needs other limits runs the connection itself."""
    t = tables
    vectors: list[dict] = []
    begin = [STATE_TABLE, SESSION_STATES, SESSION_TRANSITIONS, BEGIN_ESTABLISHES,
             BEGIN_REMOTE_CHANNEL]
    session_end = [SESSION_STATES, SESSION_TRANSITIONS, END_DISASSOCIATES, SESSION_ERRORS]
    transfer_clauses = [SESSION_STATES, TRANSFER_ONE_SECTION, DATA_SECTION]
    attach_clauses = [SESSION_STATES, ATTACH_MANDATORY, ATTACH_DEFAULTS]

    def windows(next_outgoing: int = 0, incoming: int = 1000, outgoing: int = 1000) -> dict:
        """The three window fields begin and flow both make mandatory, as field values a
        body builder fills in."""
        return {"next-outgoing-id": {"type": "uint", "value": next_outgoing},
                "incoming-window": {"type": "uint", "value": incoming},
                "outgoing-window": {"type": "uint", "value": outgoing}}

    def transfer(**kwargs) -> dict:
        return t.transfer_body(**kwargs)

    # -- establishing and ending a session -------------------------------- #

    vectors.append(exchange(
        "exchange-session-begin-then-end", start=s("UNMAPPED"), clauses=begin + session_end,
        steps=[t.send_frame(AMQP_FRAME, t.body("begin", **windows()), state=s("BEGIN_SENT"),
                            channel=1),
               t.receive_frame(AMQP_FRAME, t.body("begin", **windows(), **{"remote-channel": {"type": "ushort", "value": 1}}),
                               state=s("MAPPED"), channel=1),
               t.send_frame(AMQP_FRAME, t.body("end"), state=s("END_SENT"), channel=1),
               t.receive_frame(AMQP_FRAME, t.body("end"), state=s("UNMAPPED"), channel=1)],
        note="the locally initiated order: our begin assigns channel 1 as the outgoing "
             "channel, their begin answers with remote-channel 1, and the session is "
             "MAPPED until our end puts it in END_SENT and theirs puts it back in "
             "UNMAPPED"))

    vectors.append(exchange(
        "exchange-session-begin-remotely-initiated", start=s("UNMAPPED"),
        clauses=begin + session_end,
        steps=[t.receive_frame(AMQP_FRAME, t.body("begin", **windows()), state=s("BEGIN_RCVD"),
                               channel=1),
               t.send_frame(AMQP_FRAME, t.body("begin", **windows(), **{"remote-channel": {"type": "ushort", "value": 1}}),
                            state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME, t.body("end"), state=s("END_RCVD"), channel=1),
               t.send_frame(AMQP_FRAME, t.body("end"), state=s("UNMAPPED"), channel=1)],
        note="the other order: their begin arrives first and marks the begin as one "
             "referring to a remotely initiated session, so our answer is the begin "
             "that MUST set remote-channel to the channel theirs arrived on"))

    vectors.append(exchange(
        "exchange-session-end-with-error-discards", start=s("MAPPED"),
        clauses=session_end + [IDLE_DISCARDS],
        steps=[t.send_frame(AMQP_FRAME, t.body("end", error=t.error(ILLEGAL_STATE)),
                            state=s("DISCARDING"), channel=1),
               t.receive_frame(AMQP_FRAME, transfer(), state=None, channel=1),
               t.receive_frame(AMQP_FRAME, t.body("end"), state=s("UNMAPPED"), channel=1),
               t.refused("send", reason="illegalState", state=s("UNMAPPED"),
                         body=transfer(), channel=1)],
        note="the error-triggered close: an END carrying an error is DISCARDING, whose "
             "incoming frames must be silently discarded until the peer's end — the "
             "transfer is discarded without being read — and once the session is "
             "UNMAPPED it can neither send nor receive"))

    # -- a transfer carrying one unfragmented data section ----------------- #

    vectors.append(exchange(
        "exchange-session-transfer-one-data-section", start=s("UNMAPPED"),
        clauses=transfer_clauses + begin,
        steps=[t.send_frame(AMQP_FRAME, t.body("begin", **windows()), state=s("BEGIN_SENT"),
                            channel=1),
               t.receive_frame(AMQP_FRAME, t.body("begin", **windows(), **{"remote-channel": {"type": "ushort", "value": 1}}),
                               state=s("MAPPED"), channel=1),
               t.send_frame(AMQP_FRAME, transfer(), state=None, channel=1,
                            payload=t.data_section(b"one unfragmented section")),
               t.receive_frame(AMQP_FRAME, transfer(), state=None, channel=1,
                               payload=t.data_section(b"one unfragmented section"))],
        note="one message in one transfer: the payload is a single data section, which "
             "the frame layer calls opaque and the session layer does not read — what it "
             "decides is that a MAPPED session may send and receive it"))

    # -- fields the generated table makes mandatory, and their defaults ----- #

    vectors.append(exchange(
        "exchange-session-attach-missing-role", start=s("MAPPED"), clauses=attach_clauses,
        steps=[t.refused("send", reason="malformed", state=s("MAPPED"), condition=INVALID_FIELD,
                         body=t.body("attach", name={"type": "string", "text": "link"},
                                     handle={"type": "uint", "value": 0}),
                         channel=1,
                         note="attach's role is mandatory in the declared surface, and a "
                              "performative that does not carry it is not the "
                              "performative its descriptor names"),
               t.send_frame(AMQP_FRAME, t.body("attach", name={"type": "string", "text": "link"},
                                               handle={"type": "uint", "value": 0},
                                               role={"type": "boolean", "value": False}),
                            state=None, channel=1)],
        note="a mandatory field missing is refused with the artifact's own invalid-field "
             "condition, and the same attach carrying it is admitted — which is what "
             "makes the refusal about the field rather than about the frame"))

    vectors.append(exchange(
        "exchange-session-attach-defaults-admitted", start=s("MAPPED"),
        clauses=attach_clauses + [ATTACH_SETTLE_DEFAULT],
        steps=[t.send_frame(AMQP_FRAME, t.body("attach", name={"type": "string", "text": "link"},
                                               handle={"type": "uint", "value": 0},
                                               role={"type": "boolean", "value": False}),
                            state=None, channel=1),
               t.send_frame(AMQP_FRAME, t.body("detach", handle={"type": "uint", "value": 0},
                                               closed={"type": "boolean", "value": True}),
                            state=None, channel=1)],
        note="an attach that omits snd-settle-mode and rcv-settle-mode is admitted: the "
             "declared surface gives them the defaults `mixed` and `first`, so omitting "
             "them is a value and not a refusal — and their effect on dispositions is not "
             "this slice's"))

    vectors.append(exchange(
        "exchange-session-flow-missing-next-incoming-id", start=s("MAPPED"),
        clauses=[FLOW_NEXT_INCOMING_ID, SESSION_ERRORS],
        steps=[t.refused("receive", reason="malformed", state=s("DISCARDING"),
                         condition=INVALID_FIELD,
                         body=t.body("flow", **windows()), channel=1,
                         note="the begin has been received, so a flow's next-incoming-id "
                              "MUST be set, and this one is not"),
               t.receive_frame(AMQP_FRAME, t.body("end"), state=s("UNMAPPED"), channel=1)],
        note="a flow field rule, whose violation is input the session cannot process: "
             "it answers with the END an error, which the diagram draws from MAPPED to "
             "DISCARDING"))

    # -- the channel a frame belongs to ------------------------------------ #

    vectors.append(exchange(
        "exchange-session-transfer-before-begin", start=s("UNMAPPED"),
        clauses=[SESSION_STATES, BEGIN_ESTABLISHES] + [CHANNEL_MAP],
        steps=[t.refused("send", reason="illegalState", state=s("UNMAPPED"), body=transfer(),
                         channel=1,
                         note="no channel is mapped to a session that has not begun, so "
                              "the frame is not this session's to send"),
               t.send_frame(AMQP_FRAME, t.body("begin", **windows()), state=s("BEGIN_SENT"),
                            channel=1)],
        note="a transfer offered before the begin that maps the channel: the begin is "
             "what assigns the outgoing channel, so the refusal is about the channel and "
             "the begin that follows is admitted on the same one"))

    vectors.append(exchange(
        "exchange-session-frame-on-unmapped-channel", start=s("MAPPED"),
        clauses=[SESSION_STATES, CHANNEL_MAP],
        steps=[t.refused("receive", reason="illegalState", state=s("MAPPED"), body=transfer(),
                         channel=2,
                         note="channel 2 is not this session's incoming channel, and the "
                              "connection maps incoming frames to sessions by channel"),
               t.receive_frame(AMQP_FRAME, transfer(), state=None, channel=1)],
        note="a frame on a channel no session here is mapped to: the session cannot even "
             "answer on it, so it refuses and the state does not move, and the same "
             "transfer on the mapped channel is admitted"))

    vectors.append(exchange(
        "exchange-session-incoming-id-must-be-set", start=s("MAPPED"),
        clauses=[FLOW_NEXT_INCOMING_ID, IDLE_DISCARDS],
        steps=[t.receive_frame(AMQP_FRAME,
                               t.body("flow", **windows(), **{"next-incoming-id": {"type": "uint", "value": 0}}),
                               state=None, channel=1),
               t.send_frame(AMQP_FRAME,
                            t.body("flow", **windows(), **{"next-incoming-id": {"type": "uint", "value": 0}}),
                            state=None, channel=1)],
        note="the same field, set: the rule is that next-incoming-id MUST be set "
             "once the peer has received the begin frame, and it has, so both "
             "directions carry it and neither is refused"))

    # -- the session's flow-control arithmetic ---------------------------------- #

    def flow_frame(next_outgoing=0, incoming=1000, outgoing=1000, next_incoming=0) -> dict:
        return t.body("flow", **{"next-incoming-id": ({"type": "uint", "value": next_incoming}
                                                      if next_incoming is not None
                                                      else {"type": "null"}),
                                 "incoming-window": {"type": "uint", "value": incoming},
                                 "next-outgoing-id": {"type": "uint", "value": next_outgoing},
                                 "outgoing-window": {"type": "uint", "value": outgoing}})

    vectors.append(exchange(
        "exchange-session-window-remote-incoming", start=s("MAPPED"),
        clauses=[WINDOW_REMOTE_INCOMING, WINDOW_AFTER_FLOW, WINDOW_AFTER_SENDING],
        steps=[t.receive_frame(AMQP_FRAME, flow_frame(incoming=1), state=None, channel=1),
               t.send_frame(AMQP_FRAME, transfer(), state=None, channel=1),
               t.refused("send", reason="limit", state=s("MAPPED"), condition=WINDOW_VIOLATION,
                         body=transfer(), channel=1,
                         note="remote-incoming-window was recomputed from the flow as "
                              "next-incoming-id + incoming-window - next-outgoing-id = 1, "
                              "and a sent transfer decrements it, so the second one has "
                              "nothing to spend")],
        note="the recomputation clause and the decrement it is spent by: one flow sets the "
             "remote window to one transfer, the first transfer is admitted and the second "
             "is refused as a window violation"))

    vectors.append(exchange(
        "exchange-session-window-recomputed", start=s("MAPPED"),
        clauses=[WINDOW_AFTER_FLOW, WINDOW_AFTER_SENDING],
        steps=[t.receive_frame(AMQP_FRAME, flow_frame(incoming=0), state=None, channel=1),
               t.refused("send", reason="limit", state=s("MAPPED"), condition=WINDOW_VIOLATION,
                         body=transfer(), channel=1,
                         note="a flow that leaves the window empty"),
               t.receive_frame(AMQP_FRAME, flow_frame(incoming=5), state=None, channel=1),
               t.send_frame(AMQP_FRAME, transfer(), state=None, channel=1)],
        note="the doc says the endpoint MUST update the remote windows \'directly from\' the "
             "frame, so a later flow replaces an earlier one: the window is empty, then "
             "five transfers wide, and only the later value decides"))

    vectors.append(exchange(
        "exchange-session-window-incoming-exhausted", start=s("UNMAPPED"),
        clauses=[WINDOW_INCOMING, WINDOW_AFTER_RECEIVING],
        steps=[t.send_frame(AMQP_FRAME, t.body("begin", **{"incoming-window": {"type": "uint", "value": 1}, "next-outgoing-id": {"type": "uint", "value": 0}, "outgoing-window": {"type": "uint", "value": 10}}), state=s("BEGIN_SENT"), channel=1),
               t.receive_frame(AMQP_FRAME, t.body("begin", **windows()), state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME, transfer(), state=None, channel=1),
               t.refused("receive", reason="limit", state=s("DISCARDING"),
                         condition=WINDOW_VIOLATION, body=transfer(), channel=1,
                         note="this session announced an incoming window of one transfer "
                              "and its policy decrements it per transfer received, so the "
                              "second arrival is the window violation the session ends on")],
        note="the window this endpoint announced in its own begin is what gates what it "
             "receives, and its exhaustion is refused with the artifact\'s own "
             "window-violation and the END that leaves the session DISCARDING"))


    # -- the dispatch the interface fixes ---------------------------------- #

    vectors.append(exchange(
        "exchange-session-close-on-a-session-channel", start=s("MAPPED"),
        clauses=[DISPATCH_TABLE, CLOSE_ANY_CHANNEL],
        steps=[t.send_frame(AMQP_FRAME, t.close_body(), state=c("CLOSE_SENT"), channel=1),
               t.receive_frame(AMQP_FRAME, t.close_body(), state=c("END"), channel=1)],
        note="a `close` on a session's channel is the *connection's* frame: the dispatch "
             "table gives open and close to the connection endpoint, and a close may be "
             "received on any channel up to the channel maximum, so the step that carries "
             "it names a connection state"))

    vectors.append(exchange(
        "exchange-connection-discarding-discards-session-frames", start=s("MAPPED"),
        clauses=[DISPATCH_TABLE, OPEN_ON_CHANNEL_ZERO, DISCARD_ON_ERROR],
        steps=[t.refused("receive", reason="illegalState", state=c("DISCARDING"),
                         body=t.open_body(), channel=1,
                         note="the open frame can only be sent on channel 0, so one on "
                              "channel 1 is the connection's own rule broken, and a "
                              "refused receive is answered by closing"),
               t.receive_frame(AMQP_FRAME, transfer(), state=None if False else c("DISCARDING"), channel=1)],
        note="a session frame arriving while the connection is discarding: the artifact "
             "says any incoming frames on the connection MUST be silently discarded "
             "until the peer's close, so it is admitted and changes nothing"))

    return vectors


def mutation_corpus(tables: Corpus) -> list[dict]:
    """The controls, which are meant to fail: each one asserts something the artifact
    does not permit, so a correct peer refuses or lands somewhere else and the harness
    reports it. They live apart from the corpus for exactly that reason."""
    open0 = tables.open_body()
    return [
        exchange(
            "mutation-end-send-asserted", start=c("END"),
            clauses=[STATE_TABLE, CLOSE_LAST],
            steps=[{"direction": "send",
                    "value": frame_value(AMQP_FRAME, tables.close_body()),
                    "expect": {"status": "admitted", "state": c("END")}},
                   tables.refused_close_in_end()],
            note="the state-table mutation: this vector asserts that END's legal sends "
                 "are `*` rather than `-`, so a peer that implements the table refuses "
                 "and the harness reports the vector as failing. An operator running "
                 "this file expects a failure naming it"),
        exchange(
            "mutation-wrong-expected-state", start=c("START"),
            clauses=[STATE_TABLE, STATE_DIAGRAM, HEADER_FIRST],
            steps=[{"direction": "send", "bytes": tables.header("amqp").hex(),
                    "expect": {"status": "admitted", "state": c("HDR_RCVD")}},
                   tables.send_frame(AMQP_FRAME, open0, state=c("OPEN_PIPE"))],
            note="the vector's own expectation is wrong: sending the header in START "
                 "leaves HDR_SENT, not HDR_RCVD, so the harness's failure path is "
                 "exercised by a step the peer admits"),
        exchange(
            "mutation-refusal-expected-admitted", start=c("START"),
            clauses=[STATE_TABLE, HEADER_FIRST],
            steps=[{"direction": "receive", "bytes": tables.header("tls").hex(),
                    "expect": {"status": "admitted", "state": c("HDR_RCVD")}},
                   tables.refused_header_in_end()],
            note="the reverse mutation in the expectation: a header this peer cannot "
                 "accept is written down as admitted, so the peer's refusal is what "
                 "makes the vector fail"),
    ]


def write(path: pathlib.Path, vectors: list[dict]) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = "\n".join(json.dumps(v, sort_keys=True) for v in vectors) + "\n"
    path.write_text(text, encoding="utf-8")
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", default=str(ROOT / "vectors" / "generated-exchanges.ndjson"),
                        help="where the exchange corpus is written")
    parser.add_argument("--mutations", default=None, metavar="PATH",
                        help="also write the mutation controls — vectors that assert "
                             "what the artifact does not permit and are therefore meant "
                             "to fail — to PATH")
    args = parser.parse_args(argv)

    tables = Corpus()
    vectors = corpus(tables) + session_corpus(tables)
    digest = write(pathlib.Path(args.out), vectors)
    starts: dict[str, int] = {}
    reasons: dict[str, int] = {}
    for vector in vectors:
        starts[vector["start"]] = starts.get(vector["start"], 0) + 1
        for step in vector["steps"]:
            if step["expect"]["status"] == "refused":
                key = step["expect"]["reason"]
                reasons[key] = reasons.get(key, 0) + 1
    print(f"generated {len(vectors)} exchange vectors into {args.out}")
    print("  start states: " + ", ".join(f"{k}={v}" for k, v in sorted(starts.items())))
    print("  refusals: " + ", ".join(f"{k}={v}" for k, v in sorted(reasons.items())))
    print(f"  sha256: {digest}")

    if args.mutations is not None:
        controls = mutation_corpus(tables)
        control_digest = write(pathlib.Path(args.mutations), controls)
        print(f"generated {len(controls)} mutation controls into {args.mutations}")
        print(f"  sha256: {control_digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
