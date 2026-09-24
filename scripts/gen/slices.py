"""The per-slice exchange corpora: the connection and session families as ordered steps.

One family module of the corpus generator, and `scripts/gen-exchange-vectors.py` is the
command line that dispatches to it; the package docstring maps the whole set.

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
    wire-level refusals, with the specific cause in the reason class;
  * the framing boundaries the connection owns: a frame at exactly the maximum frame
    size this peer announced and at one octet more, a frame whose header is longer than
    the minimum, a frame with no body on a channel a session would have to map, a frame
    above the channel maximum this peer declared, the SASL layer's own 512-octet bound,
    and the two frame-layer failure classes (`sizeMismatch`, `truncated`) that reach the
    connection as a pass-through, under the one condition it uses for a wire-level
    failure;
  * the settlement negotiation in both directions: the `settled` choice obliging a
    delivery to be settled in at least one of its transfers and the `mixed` choice
    obliging neither, the `unsettled` choice's exemption for an aborted delivery, and
    the transfer's `rcv-settle-mode` admitted only where the attach negotiated it;
  * the flow's counts against the quantities each end holds: the delivery-count a
    sender's flow must carry as its own current count, and the echo a receiver's flow
    must return;
  * the delivery a transfer ends or discards: `more` carrying one across transfers,
    `aborted` discarding one with the data its earlier transfers carried, and the
    precedence the artifact gives `aborted` when both flags are set;
  * the fields an attach's and a begin's own clauses make them carry or omit — a
    sender's missing `initial-delivery-count`, a receiver's (which is ignored), the
    `remote-channel` in both of its directions — and the resume flag a resumed delivery
    is named by;
  * the dispatch table's channel rule, which the interface fixes and the register
    records: a session performative on channel zero is a frame the connection cannot
    relay and no session can answer.

`--mutations` writes the control family to a separate path: a vector that asserts a
mutated state-table row (END permits a send) and which the peer must therefore refuse,
and a vector whose own expected state is wrong so that the harness's failure path is
exercised. Those are controls, not corpus: they are meant to fail, so they are written
where the operator asks for them rather than into the passing corpus.

`--staged` writes the third family to a path of the caller's choosing: vectors authored
from the artifact that at least one artefact does not meet. Each is a *divergence* (the
two artefacts answer the same step differently, and neither side is chosen) or a *shared
gap* (both admit what a clause forbids, so no differential can see it); the divergence
kind is empty as the file stands — its last two members were aligned by `d50abc1` and
`1540777`, five more by `5624f16`, and all seven were promoted — so the family is shared
gaps only, which is what the file is for: holding the obligations a gate cannot yet
require rather than being emptied. `staged_corpus` names which, with the clause and both
observed answers, because the file is a fix slice's opening evidence rather than a corpus
a gate runs.

Runs offline; the only input is the vendored artifacts under `spec/oasis/`.
"""

from __future__ import annotations

import pathlib
from xml.etree import ElementTree

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = ROOT / "spec" / "oasis"
TRANSPORT = "amqp-core-transport-v1.0-os.xml"
MESSAGING = "amqp-core-messaging-v1.0-os.xml"
SECURITY = "amqp-core-security-v1.0-os.xml"

UNATTACHED_HANDLE = "amqp:session:unattached-handle"
HANDLE_IN_USE = "amqp:session:handle-in-use"
# The link rules, each cited at the clause that states it rather than at the section it
# lives in: Part 2 states them under `links/doc:…`, and a vector cites the one its own
# steps exercise. A section-level citation (`section:link-handles`, `section:flow-control`)
# named an area rather than a rule, and resolved against no clause at all.
LINK_HANDLES = f"{TRANSPORT}#amqp:transport/section:links/doc:link-handles.1"
LINK_ERRORS = f"{TRANSPORT}#amqp:transport/section:links/doc:closing-a-link.1"
TRANSFER_FIRST_FIELDS = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:delivery-tag.1"
TRANSFER_SETTLED = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:settled.4"
ABORTED_MESSAGES_DISCARDED = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:aborted.1"
DISPOSITION_ROLE = f"{TRANSPORT}#amqp:transport/section:performatives/type:disposition.1"
# The sender's half of the link credit, in the clause each vector exercises: `.2` is the
# sender's value matching the delivery-limit the receiver identified, `.3` is the formula
# it sets `link-credit` by when the receiver sends flow information, `.9` is stopping at
# zero. (The other half of the aborted-transfer sentence — the payload MUST be ignored —
# is `DATA_SECTION` below, named there for the session family that cites it.)
FLOW_SENDER_MATCHES_DELIVERY_LIMIT = f"{TRANSPORT}#amqp:transport/section:links/doc:flow-control.2"
FLOW_SENDER_SETS_CREDIT = f"{TRANSPORT}#amqp:transport/section:links/doc:flow-control.3"
FLOW_SENDER_STOPS_AT_ZERO_CREDIT = f"{TRANSPORT}#amqp:transport/section:links/doc:flow-control.9"
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
FLOW_HANDLE_MUST_BE_ATTACHED = f"{TRANSPORT}#amqp:transport/section:performatives/type:flow/field:handle.1"
FLOW_DELIVERY_COUNT_SET_BY_SENDER = f"{TRANSPORT}#amqp:transport/section:performatives/type:flow/field:delivery-count.2"
# `.4` is the same field's other presence rule, stated for the moment before the sender has
# attached: the receiver's flow may not name a count it has no sender to have taken it from.
FLOW_DELIVERY_COUNT_NOT_BEFORE_ATTACH = f"{TRANSPORT}#amqp:transport/section:performatives/type:flow/field:delivery-count.4"
# link-credit's ownership is stated twice — once in the `flow-control` doc, as the one of the
# four quantities only the receiver chooses, and once in the field's own table — and the pairs
# that carry it cite both. (The doc's `.u1`, not its `.u3`: `.u3` is `drain`'s sentence.)
FLOW_CREDIT_RECEIVER_CHOOSES = f"{TRANSPORT}#amqp:transport/section:links/doc:flow-control.u1"
LINK_CREDIT_RECEIVER_SETS = f"{TRANSPORT}#amqp:transport/section:performatives/type:flow/field:link-credit.u1"
# Five of the flow's fields carry one sentence each — "When the handle field is not set,
# this field MUST NOT be set" — so the vector that exercises the coupling cites all five.
# One name for the five, because the artifact states one coupling and repeats it per field.
FLOW_FIELDS_REQUIRE_HANDLE = [
    f"{TRANSPORT}#amqp:transport/section:performatives/type:flow/field:{field}.1"
    for field in ("available", "delivery-count", "drain", "link-credit", "properties")
]

# The fields a flow carries only when it names a link: the handle, and the two quantities
# the two ends hold between them. A vector about the session's own windows — the frame-size
# bound, the window arithmetic — leaves them unset, and `Corpus.flow_body`'s `absent` and
# `null` say which of the two unset encodings the vector is about.
FLOW_LINK_FIELDS = ("handle", "delivery-count", "link-credit")
# The two of them the count rules read: `.2` makes the sender's flow carry one, `.3` makes
# the receiver's echo the other, and a vector that leaves both off states a presence the
# rule forbids.
FLOW_COUNT_FIELDS = ("delivery-count", "link-credit")

WINDOW_REMOTE_INCOMING = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.3"
WINDOW_INCOMING = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.5"
WINDOW_AFTER_SENDING = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.5"
WINDOW_AFTER_FLOW = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.7"
WINDOW_AFTER_RECEIVING = f"{TRANSPORT}#amqp:transport/section:sessions/doc:session-flow-control.6"

# The settle-mode pair. `settled.4`/`.5` and `.6` are one sentence's two choices: the
# artifact distinguishes them only by the `choice` attribute of their cross-references
# (`<xref name="sender-settle-mode" choice="settled"/>` against `choice="unsettled"`),
# so a vector names the clause whose choice it negotiates rather than the family.
TRANSFER_SETTLED_NEVER = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:settled.6"
TRANSFER_RCV_SETTLE_ILLEGAL = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:rcv-settle-mode.u1"
# `.u2` is the same field's exemption: a transfer the sender flags settled makes the field
# ignored, so the rule above is gated on the frame's own flag rather than on the negotiation.
TRANSFER_RCV_SETTLE_IGNORED = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:rcv-settle-mode.u2"
# The resumption clauses, none of which has a carrier: `resume.2` is the sender's MUST NOT
# and `.3` the first-transfer rule, and both are statements about a delivery's presence in
# an unsettled map the layer does not hold.
TRANSFER_RESUME_SENDER_MUST_NOT = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:resume.2"
TRANSFER_RESUME_FIRST_TRANSFER = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:resume.3"
# The `more`/`aborted` pair: `.u1` is the precedence note ("the aborted flag takes
# precedence") and `.2` the sender's SHOULD NOT, which a receiver cannot enforce and which
# is why the vector that carries both states the precedence rather than the SHOULD NOT.
TRANSFER_MORE_ABORTED_PRECEDENCE = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:more.u1"
TRANSFER_ABORT_PRIOR_DATA = f"{TRANSPORT}#amqp:transport/section:links.33"
ATTACH_INITIAL_COUNT = f"{TRANSPORT}#amqp:transport/section:performatives/type:attach/field:initial-delivery-count.1"
ATTACH_UNSETTLED_NULL_KEY = f"{TRANSPORT}#amqp:transport/section:performatives/type:attach/field:unsettled.5"
FLOW_DELIVERY_COUNT_ECHO = f"{TRANSPORT}#amqp:transport/section:performatives/type:flow/field:delivery-count.3"
BEGIN_LOCAL_REMOTE_CHANNEL = f"{TRANSPORT}#amqp:transport/section:performatives/type:begin/field:remote-channel.1"
# The connection-level framing boundaries: the SIZE field counts the extended header
# (`framing.1`), and `framing.4` is the empty frame the idle-timeout doc licenses.
SIZE_COUNTS_EXTENDED = f"{TRANSPORT}#amqp:transport/section:framing.1"
EMPTY_FRAME = f"{TRANSPORT}#amqp:transport/section:framing.4"
EMPTY_FRAME_ANY_CHANNEL = f"{TRANSPORT}#amqp:transport/section:connections/doc:doc-idle-time-out.7"
# The section's answer to input a session cannot process (`.5`), and the discard phase it
# obliges (`.6`) — the two clauses every session refusal is placed by.
SESSION_END_ON_ERROR = f"{TRANSPORT}#amqp:transport/section:sessions.5"
# `links.29` is where the artifact says what `more` means — "additional data MAY be
# transferred in additional «transfer» frames by setting the more flag on all but the last
# «transfer» frame" — which is what makes an unset flag a completed message rather than an
# absent one.
TRANSFER_MORE_LAST_FRAME = f"{TRANSPORT}#amqp:transport/section:links.29"
# "Both peers MUST accept frames of up to 512 octets", which is the floor an `open`'s own
# declared maximum has to leave in place.
MIN_ACCEPTED_FRAME = f"{TRANSPORT}#amqp:transport/section:performatives/type:open/field:max-frame-size.3"

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
    if kind == "map":
        entries = b"".join(encode(entry["key"]) + encode(entry["value"])
                           for entry in value["entries"])
        if not value["entries"]:
            # map8 with a count of zero: the size field counts the count field and the
            # items that follow it, so an empty map's size is one
            return b"\xC1\x01\x00"
        # the count field counts *items* rather than pairs — a map's keys and values are
        # its items, so a one-pair map declares two — which is why a pair count written
        # here is refused by both readers as an odd item count
        count = len(value["entries"]) * 2
        size = len(entries) + 1
        if size < 256 and count < 256:
            return b"\xC1" + bytes([size]) + bytes([count]) + entries
        return b"\xD1" + be(size + 3, 4) + be(count, 4) + entries
    if kind == "described":
        return b"\x00" + encode(value["descriptor"]) + encode(value["value"])
    if kind == "array":
        ctor = int(value["constructor"], 16)
        elements = b"".join(element_octets(ctor, item) for item in value["items"])
        count = len(value["items"])
        if 2 + len(elements) <= 0xFF and count <= 0xFF:
            return bytes([0xE0, 2 + len(elements), count, ctor]) + elements
        return (bytes([0xF0]) + be(5 + len(elements), 4) + be(count, 4)
                + bytes([ctor]) + elements)
    raise SystemExit(f"gen-exchange-vectors: cannot encode a {kind!r}")


def element_octets(constructor: int, value: dict) -> bytes:
    """One element of an array, in the array's declared constructor form.

    An array states its element constructor once, so an element carries its data and no
    constructor of its own. The corpus writes exactly one array — the `sasl-server-mechanisms`
    field, whose declared type is `symbol` — so the one constructor the table assigns it is
    written here and anything else is refused rather than written in another form.
    """
    if constructor == 0xA3:
        if value["type"] != "symbol":
            raise SystemExit(f"gen-exchange-vectors: a symbol array carries symbols, not "
                             f"{value['type']!r}")
        payload = value["text"].encode("utf-8")
        if len(payload) > 0xFF:
            raise SystemExit("gen-exchange-vectors: a symbol8 array element is at most 255 "
                             "octets; this corpus writes the narrowest form")
        return bytes([len(payload)]) + payload
    raise SystemExit(f"gen-exchange-vectors: element constructor {constructor:#04x} is not "
                     f"one this corpus writes")


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


def empty_frame(frame_type: int = AMQP_FRAME, channel: int = 0) -> bytes:
    """A frame consisting solely of a frame header, which `framing.4` licenses ("a frame
    consisting solely of a frame header, with no frame body") and which the idle-timeout
    doc requires a peer to handle on any valid channel. SIZE counts the header alone."""
    return be(FRAME_HEADER, 4) + bytes([FRAME_MIN_DOFF, frame_type]) + be(channel, 2)


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
        self.disposition_code = descriptor_code(transport["disposition"])
        # the `data` section is a messaging type: a transfer's payload is one, and the
        # session layer carries it without reading it
        self.data_code = descriptor_code(declared_types(MESSAGING)["data"])
        self.error_code = descriptor_code(transport["error"])
        self.codes = {"begin": self.begin_code, "end": self.end_code,
                      "attach": self.attach_code, "detach": self.detach_code,
                      "flow": self.flow_code, "transfer": self.transfer_code,
                      "disposition": self.disposition_code,
                      "data": self.data_code, "error": self.error_code}
        self.fields = {name: field_names(transport[name])
                       for name in ("begin", "end", "attach", "detach", "flow",
                                    "transfer", "disposition", "error")}
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
                      delivery_tag: bytes = b"tag", *, identity: bool = True,
                      settled: bool | None = None, more: bool | None = None,
                      aborted: bool | None = None, resume: bool | None = None,
                      rcv_settle_mode: int | None = None) -> dict:
        """A `transfer` of one unfragmented delivery: the handle it is mandatory, and
        `more` is left unset, which is the default and means the message is not split.

        `identity=False` leaves `delivery-id`, `delivery-tag` and `message-format` off the
        frame, which is what a continuation transfer writes. The flags each field is named
        for are written only where the vector sets them, so an unset flag is the absent
        field the artifact's own default applies to rather than an explicit false."""
        fields: dict[str, dict] = {"handle": {"type": "uint", "value": handle}}
        if identity:
            fields["delivery-id"] = {"type": "uint", "value": delivery_id}
            fields["delivery-tag"] = {"type": "binary", "hex": delivery_tag.hex()}
            fields["message-format"] = {"type": "uint", "value": 0}
        for name, flag in (("settled", settled), ("more", more), ("aborted", aborted),
                           ("resume", resume)):
            if flag is not None:
                fields[name] = {"type": "boolean", "value": flag}
        if rcv_settle_mode is not None:
            fields["rcv-settle-mode"] = {"type": "ubyte", "value": rcv_settle_mode}
        return self.body("transfer", **fields)

    def attach_body(self, role: bool = False, handle: int = 0, name: str = "link",
                    initial_delivery_count: int = 0,
                    snd_settle_mode: int | None = None,
                    rcv_settle_mode: int | None = None,
                    unsettled: dict | None = None) -> dict:
        """An `attach`. The `role` field's declared type is a restricted `boolean` whose
        `sender` value is false and whose `receiver` value is true, and
        `initial-delivery-count` "MUST NOT be null if role is sender", so this carries it
        exactly in that case.

        `snd_settle_mode` is the number of a **choice** of the declared element
        `sender-settle-mode` — `unsettled` (0), `settled` (1), `mixed` (2) — and not the
        element itself. The element names the field's type and the sentences that constrain
        `transfer`'s `settled` field each select one of those choices, so a value written
        here is a negotiation, and reading the element's *name* where a sentence selects a
        *choice* inverts which obligation is in force. `rcv_settle_mode` is the same shape
        for the receiver's half of the negotiation, whose choices are `first` and `second`.
        """
        fields: dict[str, dict] = {"name": {"type": "string", "text": name},
                                   "handle": {"type": "uint", "value": handle},
                                   "role": {"type": "boolean", "value": role}}
        if not role:
            fields["initial-delivery-count"] = {"type": "uint",
                                                "value": initial_delivery_count}
        if snd_settle_mode is not None:
            fields["snd-settle-mode"] = {"type": "ubyte", "value": snd_settle_mode}
        if rcv_settle_mode is not None:
            fields["rcv-settle-mode"] = {"type": "ubyte", "value": rcv_settle_mode}
        if unsettled is not None:
            fields["unsettled"] = unsettled
        return self.body("attach", **fields)

    def unsettled_map(self, entries: list[tuple[dict, dict]]) -> dict:
        """An `unsettled` field's value: a map of delivery-tag to delivery state. Part 3
        gives the states meanings and this layer does not read them, so a vector that
        exercises the map's own key rule carries values that are whatever the rule under
        test does not look at."""
        return {"type": "map",
                "entries": [{"key": key, "value": value} for key, value in entries]}

    def settle_mode(self, owner: str, name: str) -> int:
        """A settle-mode choice's number, from the artifact's own choice table: the
        `sender-settle-mode` and `receiver-settle-mode` elements are where the two
        negotiations' values live, and a vector that writes one cites the choice."""
        return choice_value(TRANSPORT, owner, name)

    def detach_body(self, handle: int = 0, closed: bool = True) -> dict:
        """A `detach`, whose handle is mandatory and whose `closed` flag says whether the
        link endpoint is destroyed rather than merely released."""
        return self.body("detach", handle={"type": "uint", "value": handle},
                         closed={"type": "boolean", "value": closed})

    def flow_body(self, handle: int = 0, delivery_count: int = 0, link_credit: int = 0,
                  next_incoming: int = 0, next_outgoing: int = 0,
                  incoming: int = 1000, outgoing: int = 1000,
                  absent: tuple[str, ...] = (), null: tuple[str, ...] = (),
                  **extra: dict) -> dict:
        """A `flow` for one link: the handle it names, the delivery-count the doc's
        `flow-control` defines, and the credit the receiver grants.

        A flow's count rules are about a field's *presence*, and a field absent from the
        field list and one present as the type system's null are different encodings of
        "unset" — the corpus carries both for `delivery-count`, because the clause reads
        them alike. `absent` names the fields left off the list and `null` the fields
        written as null; a field list is positional, so `absent` applies only to a suffix
        and `null` only where a field the vector sets follows, and naming one in the
        wrong form raises rather than silently becoming the other.

        `extra` carries fields the parameters above do not name — `available`,
        `properties` — as field values, exactly as `body` takes them, so a vector that
        sets one of them still builds its flow here rather than assembling the
        performative under a second writer."""
        names = self.fields["flow"]
        values: dict[str, dict] = {
            "next-incoming-id": {"type": "uint", "value": next_incoming},
            "incoming-window": {"type": "uint", "value": incoming},
            "next-outgoing-id": {"type": "uint", "value": next_outgoing},
            "outgoing-window": {"type": "uint", "value": outgoing},
            "handle": {"type": "uint", "value": handle},
            "delivery-count": {"type": "uint", "value": delivery_count},
            "link-credit": {"type": "uint", "value": link_credit},
            **extra}
        absent, null = set(absent), set(null)
        for name in absent | null:
            if name not in values:
                raise SystemExit(f"gen-exchange-vectors: flow declares no field {name}")
            values[name] = {"type": "null"}
        written = [index for index, name in enumerate(names)
                   if name in values and name not in absent | null]
        last = max(written) if written else -1
        for name in absent:
            if names.index(name) < last:
                raise SystemExit(
                    f"gen-exchange-vectors: flow's {name} is named absent with a set "
                    f"field after it — a field list is positional, so it is written null")
        for name in null:
            if names.index(name) >= last:
                raise SystemExit(
                    f"gen-exchange-vectors: flow's {name} is named null with nothing set "
                    f"after it — the encoder drops trailing nulls, which is its absent form")
        return self.body("flow", **values)

    def fragment_body(self, index: int, count: int, delivery_id: int = 0,
                      handle: int = 0, settled: bool | None = None) -> dict:
        """One transfer of a delivery split into `count` transfers. `delivery-id`,
        `delivery-tag` and `message-format` are specified for the first and omitted on
        continuations, which is what the three clauses require of them; `more` is set on
        every transfer but the last, which is what makes the delivery continue."""
        fields: dict[str, dict] = {"handle": {"type": "uint", "value": handle}}
        if index == 0:
            fields["delivery-id"] = {"type": "uint", "value": delivery_id}
            fields["delivery-tag"] = {"type": "binary", "hex": b"tag".hex()}
            fields["message-format"] = {"type": "uint", "value": 0}
        if index < count - 1:
            fields["more"] = {"type": "boolean", "value": True}
        if settled is not None:
            fields["settled"] = {"type": "boolean", "value": settled}
        return self.body("transfer", **fields)

    def error(self, condition: str) -> dict:
        """An `error` composite: the condition, and no description."""
        return described(self.error_code,
                         [{"type": "symbol", "text": condition}, {"type": "null"}])

    def data_section(self, payload: bytes) -> bytes:
        """One `data` section: the message layer's described binary, which is what a
        transfer carries as its opaque payload. The session layer does not read it."""
        return encode(described(self.data_code, [{"type": "binary", "hex": payload.hex()}]))

    def mechanisms_body(self, mechanisms: list[str]) -> dict:
        """A `sasl-mechanisms` frame's body.

        `sasl-server-mechanisms` is declared a `multiple` symbol, and Part 1's types section
        gives a `multiple` field one element of the type or an **array** of them — its own
        worked example encodes `book.authors` as the array constructor `0xE0`. So the field is
        written as that array. Writing its symbols straight into the body's field list is the
        shape both artefacts refuse, because one list cannot be both the composite's field
        list and the field's own elements.
        """
        return described(self.sasl_mechanisms_code,
                         [{"type": "array", "constructor": "a3",
                           "items": [{"type": "symbol", "text": name}
                                     for name in mechanisms]}])

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
        write it at all. The condition is named per cause and never defaulted to what an
        implementation happens to do: the state table's permission refusals carry the
        artifact's `illegal-state`, the channel rules the `framing-error` the open's own
        doc mandates for a channel out of range, and the link rules the session error the
        artifact declares for them."""
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
            "receive", reason="illegalState", condition=ILLEGAL_STATE, state=c("END"), body=self.close_body(),
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
        steps=[t.refused("send", reason="illegalState", condition=ILLEGAL_STATE,
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
               t.refused("send", reason="illegalState", condition=ILLEGAL_STATE,
                         state=c("OPEN_SENT"), body=open0,
                         note="the table's OPEN_SENT column is `**`, and a second open "
                              "is not a frame known a priori to conform: the open is "
                              "the first frame a peer sends, once")],
        note="a second open: admitted by a reading that takes `**` for `*`, refused by "
             "the artifact's rule that the first frame is the open"))

    vectors.append(exchange(
        "exchange-open-on-channel-one-send", start=c("HDR_EXCH"),
        clauses=[STATE_TABLE, OPEN_ON_CHANNEL_ZERO],
        steps=[t.refused("send", reason="illegalState", condition=FRAMING_ERROR,
                         state=c("HDR_EXCH"), body=open0, channel=1,
                         note="the open frame can only be sent on channel 0"),
               t.send_frame(AMQP_FRAME, open0, state=c("OPEN_SENT"))],
        note="an open offered on channel one: legal octets, wrong channel"))

    vectors.append(exchange(
        "exchange-open-on-channel-one-receive", start=c("HDR_EXCH"),
        clauses=[STATE_TABLE, OPEN_ON_CHANNEL_ZERO, CHANNEL_RANGE],
        steps=[t.refused("receive", reason="illegalState", condition=FRAMING_ERROR,
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
               t.refused("receive", reason="illegalState", condition=FRAMING_ERROR,
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
               t.refused("send", reason="illegalState", condition=ILLEGAL_STATE, state=c("CLOSE_PIPE"),
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
        steps=[t.refused("send", reason="illegalState", condition=ILLEGAL_STATE,
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
               t.send_frame(AMQP_FRAME, t.attach_body(role=False), state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME, t.attach_body(role=True), state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME, t.flow_body(handle=0, link_credit=1000),
                               state=s("MAPPED"), channel=1),
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
               t.send_frame(AMQP_FRAME, t.attach_body(role=False), state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME, t.attach_body(role=True), state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME, t.flow_body(handle=0, link_credit=1000),
                               state=s("MAPPED"), channel=1),
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
        steps=[t.refused("send", reason="illegalState", condition=ILLEGAL_STATE,
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
               t.refused("send", reason="illegalState", condition=ILLEGAL_STATE,
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
               t.refused("receive", reason="illegalState", condition=ILLEGAL_STATE,
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
               t.refused("send", reason="illegalState", condition=ILLEGAL_STATE,
                         state=c("END"), body=t.close_body(),
                         note="END's legal sends are `-`: once the partner's close has "
                              "arrived the connection is over, and nothing is written "
                              "after it")],
        note="DISCARDING receives `*` and answers nothing: the frames it receives are "
             "discarded until the partner's close arrives, and that close is what ends "
             "the connection, after which nothing is written"))

    # -- the frame-size bound at the value it was declared with -------------------- #

    # The two frames below are the same flow — the session's windows, which is a body
    # every layer reads and no link rule constrains — padded to a total the vector states.
    def sized_receive(body: dict, total: int, *, state: str, channel: int = 1) -> dict:
        return {"direction": "receive",
                "bytes": frame_octets(AMQP_FRAME, body, channel=channel,
                                      payload=payload_to_total(AMQP_FRAME, body, total)).hex(),
                "expect": {"status": "admitted", "state": state}}

    vectors.append(exchange(
        "exchange-frame-size-at-the-declared-maximum", start=c("START"),
        clauses=[STATE_TABLE, PRE_NEGOTIATION_LIMITS, MAX_FRAME_SIZE, OVERSIZED_FRAME,
                 SESSION_STATES, BEGIN_ESTABLISHES],
        steps=[t.send_header("amqp"),
               t.send_frame(AMQP_FRAME,
                            t.open_body(max_frame_size=t.min_max_frame_size),
                            state=c("OPEN_PIPE")),
               t.receive_header("amqp", state=c("OPEN_SENT")),
               t.receive_frame(AMQP_FRAME, open_wide, state=c("OPENED")),
               t.send_frame(AMQP_FRAME, t.begin_body(), state=s("BEGIN_SENT"), channel=1),
               t.receive_frame(AMQP_FRAME, t.begin_body(remote_channel=1),
                               state=s("MAPPED"), channel=1),
               sized_receive(t.flow_body(absent=FLOW_LINK_FIELDS), t.min_max_frame_size,
                             state=s("MAPPED")),
               t.refused("receive", reason="limit", state=c("DISCARDING"),
                         body=t.flow_body(absent=FLOW_LINK_FIELDS), channel=1,
                         payload=payload_to_total(AMQP_FRAME,
                                                  t.flow_body(absent=FLOW_LINK_FIELDS),
                                                  t.min_max_frame_size + 1),
                         note="one octet more than the maximum frame size this peer "
                              "announced in its own open, which the clause makes the "
                              "bound: \"A peer that receives an oversized frame MUST "
                              "close the connection with the framing-error "
                              "error-code\"")],
        note="the boundary the other oversized vector approaches from one side only: "
             "`exchange-oversized-frame-received` refuses a frame one octet over the "
             "limit, and this vector admits a frame of exactly MIN-MAX-FRAME-SIZE on the "
             "same terms and then refuses the next octet — so the bound is the "
             "comparison's rather than the frame's, and the two halves are one vector "
             "because a boundary is only pinned by both sides of it"))

    vectors.append(exchange(
        "exchange-frame-size-below-the-header", start=c("OPENED"),
        clauses=[STATE_TABLE, SIZE_COUNTS_EXTENDED, HEADER_LAYOUT, OVERSIZED_FRAME],
        steps=[t.refused("receive", reason="sizeMismatch", state=c("DISCARDING"),
                         octets=be(4, 4) + bytes([FRAME_MIN_DOFF, AMQP_FRAME]) + be(0, 2),
                         note="SIZE declares four octets where the header alone is eight: "
                              "`framing.1` makes the field the total the header, the "
                              "extended header and the body occupy together, so a frame "
                              "that cannot hold its own header is not a frame"),
               t.refused("receive", reason="truncated",
                         state=c("DISCARDING"), octets=empty_frame()[:6],
                         note="the same field against the octets available: "
                              "`doc-idle-time-out.7` requires a peer to *handle* empty "
                              "frames, and six octets are not a frame header at all")],
        note="the frame layer's own two classes, which no exchange vector pins: the "
             "corpus's frame vectors refuse these octets at the frame boundary, and this "
             "vector is the other half — that the connection reports the frame layer's "
             "class rather than one of its own, under the one condition both artefacts "
             "use for a wire-level failure. The register's `check-precedence-unspecified` "
             "entry is why no order between the two checks is claimed here: the artifact "
             "ranks no checks, and each step offers one failure only"))

    vectors.append(exchange(
        "exchange-empty-frame-any-channel", start=c("OPENED"),
        clauses=[STATE_TABLE, EMPTY_FRAME, EMPTY_FRAME_ANY_CHANNEL, DISPATCH_TABLE],
        steps=[{"direction": "receive", "bytes": empty_frame(channel=0).hex(),
                "expect": {"status": "admitted", "state": c("OPENED")}},
               {"direction": "receive", "bytes": empty_frame(channel=1).hex(),
                "expect": {"status": "admitted", "state": c("OPENED")}}],
        note="a frame with no body on two channels: the artifact licenses the shape "
             "(`framing.4`) and requires a peer to handle it \"on any valid channel\", so "
             "the second step is the one that matters — a channel the session layer would "
             "have to map is not a channel the idle-timeout frame needs mapped"))

    vectors.append(exchange(
        "exchange-extended-header-relayed", start=c("OPENED"),
        clauses=[STATE_TABLE, SIZE_COUNTS_EXTENDED, HEADER_LAYOUT, CLOSE_ANY_CHANNEL],
        steps=[{"direction": "receive",
                "bytes": frame_octets(AMQP_FRAME, t.close_body(), doff=3,
                                      extended=b"\x00\x00\x00\x00").hex(),
                "expect": {"status": "admitted", "state": c("CLOSE_RCVD")}},
               t.send_frame(AMQP_FRAME, t.close_body(), state=c("END"))],
        note="a frame whose header is longer than the minimum: `picture.11` draws the "
             "extended header as part of the frame header and `framing.1` counts it inside "
             "SIZE, so a peer that reads the octets after DOFF and before the body carries "
             "the frame — the treatment of those octets is the frame type's business "
             "(`framing.2`), which is why this vector's body is the `close` the connection "
             "answers for rather than a session's. The second step is the close this side "
             "owes the peer, so the vector also shows the longer header left the state "
             "machine where a shorter header would have"))

    vectors.append(exchange(
        "exchange-frame-above-our-declared-channel-max", start=c("START"),
        clauses=[STATE_TABLE, PRE_NEGOTIATION_LIMITS, CHANNEL_MAX, CHANNEL_RANGE],
        steps=[t.send_header("amqp"),
               t.send_frame(AMQP_FRAME,
                            t.open_body(max_frame_size=t.min_max_frame_size, channel_max=2),
                            state=c("OPEN_PIPE")),
               t.receive_header("amqp", state=c("OPEN_SENT")),
               t.receive_frame(AMQP_FRAME, open_wide, state=c("OPENED")),
               t.refused("receive", reason="limit", state=c("DISCARDING"),
                         body=t.transfer_body(), channel=3,
                         note="this peer announced a maximum channel number of two in its "
                              "own open, and the frame carries channel three: "
                              "`open/field:channel-max.2` mandates the framing-error for a "
                              "channel outside the supported range, and the range is the "
                              "one this peer declared")],
        note="the receive-side channel bound, which no vector pins — the corpus's channel "
             "vectors are send-side, or observe the a priori maximum of zero before any "
             "negotiation. Here the bound is this peer's own announcement, so the refusal "
             "is about the range it declared rather than about the peer's"))

    vectors.append(exchange(
        "exchange-oversized-sasl-frame", start=c("START"),
        clauses=[STATE_TABLE, PRE_NEGOTIATION_LIMITS, SASL_HEADER, SASL_FRAMES,
                 SASL_SERVER_ANNOUNCES, MIN_ACCEPTED_FRAME],
        steps=[t.send_header("sasl"),
               t.receive_header("sasl", state=c("HDR_EXCH")),
               t.refused("receive", reason="limit", state=c("END"), frame_type=SASL_FRAME,
                         body=t.mechanisms_body(["ANONYMOUS"]),
                         payload=payload_to_total(SASL_FRAME,
                                                  t.mechanisms_body(["ANONYMOUS"]),
                                                  t.min_max_frame_size + 1),
                         note="no `open` has been exchanged, so the maximum frame size is "
                              "still the 512 octets every peer must accept "
                              "(`connections.1`), and the SASL layer's bound is that "
                              "constant rather than the negotiated one — \"Both peers "
                              "MUST accept frames of up to 512 octets\"")],
        note="the pre-negotiation size bound in the layer that never negotiates one: the "
             "SASL dialogue runs before any `open`, so 512 is the only bound in force and "
             "the answer to exceeding it is the connection's own framing-error"))

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
        """The three window fields a `begin` makes mandatory, as field values its body
        builder fills in. A `flow` names these three and `next-incoming-id` as well, and
        its body comes from `flow_body`, which writes all four."""
        return {"next-outgoing-id": {"type": "uint", "value": next_outgoing},
                "incoming-window": {"type": "uint", "value": incoming},
                "outgoing-window": {"type": "uint", "value": outgoing}}

    def transfer(**kwargs) -> dict:
        return t.transfer_body(**kwargs)

    def link_flow(handle: int = 0, delivery_count: int | None = None,
                  link_credit: int | None = None) -> dict:
        """A flow that names the link: the four session windows, the handle, and whichever
        of the two count fields the vector sets. The count and credit vectors are about
        the fields a flow leaves off, so both are absent unless the vector names a value —
        and the body itself is `flow_body`'s, so a vector that leaves one off asks there
        rather than assembling the performative itself.

        The four windows are the session's rather than the link's: a flow names
        `next-incoming-id` as well as the begin's three, and the session rules require it
        once the peer's begin has arrived, so a flow built from the begin's fields alone
        is a frame refused for the wrong reason."""
        return t.flow_body(
            handle=handle, delivery_count=delivery_count or 0,
            link_credit=link_credit or 0,
            absent=tuple(name for name, value in
                         zip(FLOW_COUNT_FIELDS, (delivery_count, link_credit))
                         if value is None))

    def link_up(role_sender: bool = False, handle: int = 0, peer_handle: int = 0,
                credit: int = 1000, peer_settle: int | None = None,
                own_settle: int | None = None, own_rcv_settle: int | None = None) -> list:
        """The three steps that attach a link on a MAPPED session: our attach, the
        peer's attach, and the peer's flow, which is what grants a sender its credit. Every
        state is pinned, because a setup whose steps were unpinned could drift under a rule
        the vector is not about.

        `own_settle`/`own_rcv_settle` are written into *our* attach and `peer_settle` into
        the peer's: the two sides negotiate the settlement modes separately and each one's
        value governs what that side sends, so a vector that means to constrain the peer's
        transfers writes the peer's attach and not ours."""
        return [
            t.send_frame(AMQP_FRAME, t.attach_body(role=not role_sender, handle=handle,
                                                   snd_settle_mode=own_settle,
                                                   rcv_settle_mode=own_rcv_settle),
                         state=s("MAPPED"), channel=1),
            t.receive_frame(AMQP_FRAME, t.attach_body(role=role_sender, handle=peer_handle,
                                                      snd_settle_mode=peer_settle),
                            state=s("MAPPED"), channel=1),
            t.receive_frame(AMQP_FRAME, t.flow_body(
                handle=peer_handle, delivery_count=0,
                # the peer's flow grants credit when the peer is the receiver, and echoes
                # the last value it was sent when the peer is the sender: only the receiver
                # sets the quantity, and the sender's value is the echo of it
                link_credit=(credit if role_sender else 0)),
                state=s("MAPPED"), channel=1)]


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
               t.refused("send", reason="illegalState", condition=UNATTACHED_HANDLE,
                         state=s("MAPPED"), body=transfer(), channel=1,
                         note="a transfer names a link handle, and this session has no "
                              "attached link, so there is no handle for it to name"),
               t.refused("receive", reason="illegalState", condition=UNATTACHED_HANDLE,
                         state=s("DISCARDING"), body=transfer(), channel=1,
                         note="the same input refused the other way: the session cannot "
                              "process a frame for a link it does not have, so it answers "
                              "with the END the section mandates")],
        note="one message in one transfer is what the *link* layer carries: a session on "
             "its own has no link, so a transfer is refused on both sides with the "
             "session error the artifact declares for a handle that is not attached — "
             "the frame is the performative the descriptor names and the moment is "
             "still wrong"))

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
               t.send_frame(AMQP_FRAME, t.attach_body(role=False), state=None, channel=1)],
        note="a mandatory field missing is refused with the artifact's own invalid-field "
             "condition, and the same attach carrying it is admitted — which is what "
             "makes the refusal about the field rather than about the frame"))

    vectors.append(exchange(
        "exchange-session-attach-defaults-admitted", start=s("MAPPED"),
        clauses=attach_clauses + [ATTACH_SETTLE_DEFAULT],
        steps=[t.send_frame(AMQP_FRAME, t.attach_body(role=False), state=None, channel=1),
               t.send_frame(AMQP_FRAME, t.detach_body(), state=None, channel=1)],
        note="an attach that omits snd-settle-mode and rcv-settle-mode is admitted: the "
             "declared surface gives them the defaults `mixed` and `first`, so omitting "
             "them is a value and not a refusal — and their effect on dispositions is not "
             "this slice's"))

    vectors.append(exchange(
        "exchange-session-flow-missing-next-incoming-id", start=s("MAPPED"),
        clauses=[FLOW_NEXT_INCOMING_ID, SESSION_ERRORS],
        steps=[t.refused("receive", reason="malformed", state=s("DISCARDING"),
                         condition=INVALID_FIELD,
                         body=t.flow_body(absent=FLOW_LINK_FIELDS,
                                          null=("next-incoming-id",)), channel=1,
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
                              "connection maps incoming frames to sessions by channel")] +
              link_up() + [
               t.receive_frame(AMQP_FRAME, transfer(), state=None, channel=1)],
        note="a frame on a channel no session here is mapped to: the session cannot even "
             "answer on it, so it refuses and the state does not move, and the same "
             "transfer on the mapped channel is admitted"))

    vectors.append(exchange(
        "exchange-session-incoming-id-must-be-set", start=s("MAPPED"),
        clauses=[FLOW_NEXT_INCOMING_ID, IDLE_DISCARDS],
        steps=[t.receive_frame(AMQP_FRAME,
                               t.flow_body(absent=FLOW_LINK_FIELDS),
                               state=None, channel=1),
               t.send_frame(AMQP_FRAME,
                            t.flow_body(absent=FLOW_LINK_FIELDS),
                            state=None, channel=1)],
        note="the same field, set: the rule is that next-incoming-id MUST be set "
             "once the peer has received the begin frame, and it has, so both "
             "directions carry it and neither is refused"))

    # -- the session's flow-control arithmetic ---------------------------------- #

    vectors.append(exchange(
        "exchange-session-window-remote-incoming", start=s("MAPPED"),
        clauses=[WINDOW_REMOTE_INCOMING, WINDOW_AFTER_FLOW, WINDOW_AFTER_SENDING],
        steps=link_up(role_sender=True) + [
               t.receive_frame(AMQP_FRAME,
                               t.flow_body(absent=FLOW_LINK_FIELDS, incoming=1),
                               state=None, channel=1),
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
        steps=link_up(role_sender=True) + [
               t.receive_frame(AMQP_FRAME, t.flow_body(absent=FLOW_LINK_FIELDS, incoming=0), state=None, channel=1),
               t.refused("send", reason="limit", state=s("MAPPED"), condition=WINDOW_VIOLATION,
                         body=transfer(), channel=1,
                         note="a flow that leaves the window empty"),
               t.receive_frame(AMQP_FRAME, t.flow_body(absent=FLOW_LINK_FIELDS, incoming=5), state=None, channel=1),
               t.send_frame(AMQP_FRAME, transfer(), state=None, channel=1)],
        note="the doc says the endpoint MUST update the remote windows \'directly from\' the "
             "frame, so a later flow replaces an earlier one: the window is empty, then "
             "five transfers wide, and only the later value decides"))

    vectors.append(exchange(
        "exchange-session-window-incoming-exhausted", start=s("UNMAPPED"),
        clauses=[WINDOW_INCOMING, WINDOW_AFTER_RECEIVING],
        steps=[t.send_frame(AMQP_FRAME, t.body("begin", **{"incoming-window": {"type": "uint", "value": 1}, "next-outgoing-id": {"type": "uint", "value": 0}, "outgoing-window": {"type": "uint", "value": 10}}), state=s("BEGIN_SENT"), channel=1),
               t.receive_frame(AMQP_FRAME, t.body("begin", **windows()), state=s("MAPPED"), channel=1)] +
              link_up() + [
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
        steps=[t.refused("receive", reason="illegalState", condition=ILLEGAL_STATE, state=c("DISCARDING"),
                         body=t.open_body(), channel=1,
                         note="the state's `*` receive column does not admit a second "
                              "open -- the exclusion the register records rather than a "
                              "column of the table -- and a refused receive on an open "
                              "connection is answered by closing"),
               t.receive_frame(AMQP_FRAME, transfer(), state=None if False else c("DISCARDING"), channel=1)],
        note="a session frame arriving while the connection is discarding: the artifact "
             "says any incoming frames on the connection MUST be silently discarded "
             "until the peer's close, so it is admitted and changes nothing"))


    # -- the link machine: handles, credit, deliveries and settlement ------ #

    message = b"a message whose split points are the vector's business"

    # The four clauses an attach-and-transfer sequence writes: the attach's mandatory
    # handle, the delivery-tag and settled flag the first transfer carries, and the
    # disposition that settles it. A vector whose steps exchange such a sequence cites
    # this list and adds the clauses of its own; one that does not cites its own only.
    # This is not a blanket for every link vector — the blanket it replaces grew a
    # citation for the *section* a rule lives in, which is how vectors came to claim
    # rules their steps never touched.
    transfer_fields = [ATTACH_MANDATORY, TRANSFER_FIRST_FIELDS, TRANSFER_SETTLED,
                       DISPOSITION_ROLE]

    vectors.append(exchange(
        "exchange-link-handle-in-use", start=s("MAPPED"), clauses=transfer_fields,
        steps=link_up() + [
            t.refused("send", reason="illegalState", condition=HANDLE_IN_USE,
                      state=c("CLOSE_SENT"), body=t.attach_body(role=False), channel=1,
                      note="handle 0 is already this endpoint's link handle, and "
                           "attach/field:handle.1 says a handle MUST NOT be used for other "
                           "open links: handle.2 mandates an immediate close carrying a "
                           "handle-in-use session-error, and the state named is the "
                           "connection's because the close is the connection's frame")],
        note="a second attach reusing a live handle: the rule is `handle.1`'s and the "
             "response is the immediate close `handle.2` mandates, which reaches "
             "CLOSE_SENT on the connection rather than moving the session"))

    vectors.append(exchange(
        "exchange-link-handle-out-of-range", start=s("UNMAPPED"),
        clauses=[LINK_HANDLES, ATTACH_MANDATORY, BEGIN_ESTABLISHES],
        steps=[t.send_frame(AMQP_FRAME, t.begin_body(), state=s("BEGIN_SENT"), channel=1),
               t.receive_frame(AMQP_FRAME,
                               t.body("begin", **windows(),
                                      **{"remote-channel": {"type": "ushort", "value": 1},
                                         "handle-max": {"type": "uint", "value": 2}}),
                               state=s("MAPPED"), channel=1),
               t.refused("send", reason="limit", condition=FRAMING_ERROR,
                         state=c("CLOSE_SENT"), body=t.attach_body(role=False, handle=5),
                         channel=1,
                         note="the partner's begin declared handle-max 2, and "
                              "handle-max.1 forbids attaching outside the range its "
                              "partner can handle; handle-max.2 mandates closing the "
                              "connection with the framing-error the open's own doc names "
                              "for an out-of-range value")],
        note="a handle outside the range the partner announced: the two handle-max clauses "
             "in the send direction, where the bound is the partner's and the response is "
             "the connection's close"))

    vectors.append(exchange(
        "exchange-link-credit-granted-and-spent", start=s("MAPPED"),
        clauses=[FLOW_SENDER_STOPS_AT_ZERO_CREDIT, TRANSFER_ONE_SECTION],
        steps=link_up(role_sender=True, credit=1) + [
            t.send_frame(AMQP_FRAME, t.fragment_body(0, 1), state=s("MAPPED"), channel=1,
                         payload=message),
            t.refused("send", reason="limit", condition=FRAMING_ERROR, state=s("MAPPED"),
                      body=t.fragment_body(0, 1, delivery_id=1), channel=1,
                      note="the receiver granted one delivery of credit, and the doc's "
                           "flow-control makes the delivery-limit the receiver's "
                           "delivery-count plus its link-credit: the sender's count has "
                           "reached it")],
        note="credit is a bound the receiver sets and the sender spends: one delivery fits "
             "the grant and the second does not"))

    vectors.append(exchange(
        "exchange-link-credit-regranted", start=s("MAPPED"),
        clauses=[FLOW_SENDER_SETS_CREDIT, TRANSFER_ONE_SECTION],
        steps=link_up(role_sender=True, credit=1) + [
            t.send_frame(AMQP_FRAME, t.fragment_body(0, 1), state=s("MAPPED"), channel=1,
                         payload=message),
            t.receive_frame(AMQP_FRAME, t.flow_body(handle=0, delivery_count=1, link_credit=1),
                            state=s("MAPPED"), channel=1),
            t.send_frame(AMQP_FRAME, t.fragment_body(0, 1, delivery_id=1), state=s("MAPPED"),
                         channel=1, payload=message)],
        note="the doc's formula for a sender: link-credit_snd := delivery-count_rcv + "
             "link-credit_rcv - delivery-count_snd — so a flow that raises the receiver's "
             "credit by one raises the sender's by one, and the delivery the exhausted "
             "link refused a moment ago is admitted"))

    # the same message, three senders' framings: one transfer, two, three. Every split
    # point is permitted, so a receiver that admitted one and refused another would be
    # coupled to a sender's framing rather than to the message.
    for count in (1, 2, 3):
        chunks = [message[i::count] for i in range(count)] if count > 1 else [message]
        steps = link_up()
        for index in range(count):
            steps.append(t.receive_frame(AMQP_FRAME, t.fragment_body(index, count),
                                         state=s("MAPPED"), channel=1, payload=chunks[index]))
        vectors.append(exchange(
            f"exchange-link-fragments-{count}-transfer{'s' if count > 1 else ''}",
            start=s("MAPPED"), clauses=transfer_fields + [TRANSFER_ONE_SECTION],
            steps=steps,
            note=f"one message carried by {count} transfer(s): the transfer clauses make "
                 f"the delivery-id, delivery-tag and message-format first-transfer fields "
                 f"and `more` what continues a delivery, and a receiver that accepted this "
                 f"framing is not thereby committed to another"))

    vectors.append(exchange(
        "exchange-link-settled-inherited", start=s("MAPPED"), clauses=transfer_fields,
        steps=link_up() + [
            t.receive_frame(AMQP_FRAME, t.fragment_body(0, 2, settled=True),
                            state=s("MAPPED"), channel=1, payload=message[:10]),
            t.receive_frame(AMQP_FRAME, t.fragment_body(1, 2),
                            state=s("MAPPED"), channel=1, payload=message[10:])],
        note="the settled flag of a continuation left unset: the clause interprets it as "
             "true if and only if a preceding transfer of the delivery set it, so this "
             "delivery is settled even though its last frame does not say so"))

    vectors.append(exchange(
        "exchange-link-sender-settle-mode-unmet", start=s("MAPPED"), clauses=transfer_fields,
        steps=[t.send_frame(AMQP_FRAME, t.attach_body(role=True), state=s("MAPPED"), channel=1),
               # `settled.4` turns on the *choice* `<xref name="sender-settle-mode"
               # choice="settled"/>`, not on the element's name, so the negotiation this
               # vector carries is that choice's number — read from the artifact's own
               # choice table rather than written as a numeral somebody remembered.
               t.receive_frame(AMQP_FRAME,
                               t.attach_body(role=False, snd_settle_mode=choice_value(
                                   TRANSPORT, "sender-settle-mode", "settled")),
                               state=s("MAPPED"), channel=1),
               # the peer is this link's sender, so its flow echoes the credit this
               # endpoint last sent rather than granting any
               t.receive_frame(AMQP_FRAME, t.flow_body(handle=0, link_credit=0),
                               state=s("MAPPED"), channel=1),
               t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                         state=s("DISCARDING"), body=t.fragment_body(0, 1), channel=1,
                         payload=message,
                         note="snd-settle-mode was negotiated to the `settled` choice of "
                              "sender-settle-mode, whose obligation is that a delivery MUST "
                              "be settled in at least one of its transfers, and this delivery "
                              "never carries the flag")],
        note="settled.4 in the receive direction: the sender's obligation, checked where "
             "the delivery ends — the frame is well formed and the delivery it carries "
             "breaks the negotiated mode"))

    vectors.append(exchange(
        "exchange-link-first-transfer-needs-its-fields", start=s("MAPPED"),
        clauses=transfer_fields,
        steps=link_up() + [
            t.receive_frame(AMQP_FRAME, t.fragment_body(0, 1), state=s("MAPPED"), channel=1,
                            payload=message),
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"), octets=frame_octets(
                          AMQP_FRAME, t.body("transfer", handle={"type": "uint", "value": 0}),
                          channel=1, payload=message),
                      note="delivery-tag and message-format MUST be specified for the "
                           "first transfer of a message and can only be omitted for a "
                           "continuation, and no delivery is in progress")],
        note="the clause that couples `delivery-tag` to the delivery it continues: a "
             "transfer that omits it is a continuation, and a continuation needs a "
             "delivery to continue, so the same frame is admitted while a delivery is in "
             "progress and refused when none is"))

    vectors.append(exchange(
        "exchange-link-detach-releases-handle", start=s("MAPPED"),
        clauses=[LINK_HANDLES] + transfer_fields + [FLOW_HANDLE_MUST_BE_ATTACHED],
        steps=link_up() + [
            t.receive_frame(AMQP_FRAME, t.detach_body(), state=s("MAPPED"), channel=1),
            t.refused("receive", reason="illegalState", condition=UNATTACHED_HANDLE,
                      state=s("DISCARDING"), body=t.fragment_body(0, 1), channel=1,
                      payload=message,
                      note="link-handles says the handle remains in use until the link is "
                           "detached, so the detach released it and a transfer naming it "
                           "now names a link this endpoint does not have")],
        note="a detach releases the handle, and the release is observable: the frame that "
             "was admitted a moment ago is refused, with the session error the artifact "
             "declares for a handle that is not attached"))

    vectors.append(exchange(
        "exchange-link-aborted-discarded", start=s("MAPPED"),
        clauses=[LINK_HANDLES] + transfer_fields + [ABORTED_MESSAGES_DISCARDED, DATA_SECTION],
        steps=link_up() + [
            t.receive_frame(AMQP_FRAME,
                            t.body("transfer", handle={"type": "uint", "value": 0},
                                   **{"delivery-id": {"type": "uint", "value": 0},
                                      "delivery-tag": {"type": "binary", "hex": b"tag".hex()},
                                      "message-format": {"type": "uint", "value": 0},
                                      "aborted": {"type": "boolean", "value": True}}),
                            state=s("MAPPED"), channel=1, payload=message),
            t.receive_frame(AMQP_FRAME, t.fragment_body(0, 1, delivery_id=1),
                            state=s("MAPPED"), channel=1, payload=message)],
        note="aborted.1: an aborted delivery is discarded and its payload ignored, so the "
             "next transfer is a first transfer again rather than a continuation of it"))

    vectors.append(exchange(
        "exchange-link-disposition-direction", start=s("MAPPED"), clauses=transfer_fields,
        steps=link_up() + [
            t.receive_frame(AMQP_FRAME,
                            t.body("disposition", role={"type": "boolean", "value": True},
                                   first={"type": "uint", "value": 0},
                                   last={"type": "uint", "value": 0}),
                            state=s("MAPPED"), channel=1),
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      body=t.body("disposition", role={"type": "boolean", "value": False},
                                  first={"type": "uint", "value": 0},
                                  last={"type": "uint", "value": 0}),
                      channel=1,
                      note="disposition.1: the disposition's role gives the directionality "
                           "of the deliveries it names, and this endpoint attached as the "
                           "receiver, so the sender's role is not its to send")],
        note="the disposition's role is a direction, not a hint: the same frame with the "
             "role this endpoint's end owns is admitted, and the range it names is "
             "validated as a range"))


    vectors.append(exchange(
        "exchange-link-flow-unattached-handle", start=s("MAPPED"),
        clauses=[LINK_HANDLES, FLOW_HANDLE_MUST_BE_ATTACHED],
        steps=link_up() + [
            t.refused("send", reason="illegalState", condition=UNATTACHED_HANDLE,
                      state=s("MAPPED"),
                      body=t.flow_body(handle=7, delivery_count=0, link_credit=1),
                      channel=1,
                      note="flow/field:handle.1: a flow set to a handle that is not "
                           "currently associated with an attached link MUST be answered by "
                           "ending the session with a session error — and this endpoint's "
                           "link is handle 0"),
            t.refused("receive", reason="illegalState", condition=UNATTACHED_HANDLE,
                      state=s("DISCARDING"),
                      body=t.flow_body(handle=7, delivery_count=0, link_credit=1),
                      channel=1,
                      note="the same clause in the direction that ends the session: the "
                           "END it mandates is what leaves DISCARDING")],
        note="the flow half of the rule the transfer vector pins: the corpus's other flows "
             "leave the handle unset on purpose — they carry the session's windows — so "
             "this is the vector for the clause that binds a flow that does name a link"))

    vectors.append(exchange(
        "exchange-link-detach-unattached-handle", start=s("MAPPED"),
        clauses=[LINK_HANDLES, LINK_ERRORS],
        steps=link_up(role_sender=True) + [
            t.receive_frame(AMQP_FRAME, t.detach_body(handle=7), state=s("MAPPED"),
                            channel=1),
            t.send_frame(AMQP_FRAME, t.detach_body(handle=7), state=s("MAPPED"), channel=1),
            t.send_frame(AMQP_FRAME, t.fragment_body(0, 1), state=s("MAPPED"), channel=1,
                         payload=message)],
        note="the exception in `links.15`, which terminates the session for input related "
             "to a detached link endpoint \"other than a detach\": a detach naming a "
             "handle this endpoint does not have is admitted in both directions, releases "
             "nothing, and leaves the attached link usable — which is the last step"))


    vectors.append(exchange(
        "exchange-link-flow-field-without-handle", start=s("MAPPED"),
        clauses=[LINK_HANDLES, *FLOW_FIELDS_REQUIRE_HANDLE],
        steps=link_up() + [
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      # the windows, the next-incoming-id the session rule requires once
                      # the peer's begin has arrived, and the link field the coupling
                      # forbids — so the only rule that can refuse this frame is the one
                      # the vector is about
                      body=t.body("flow", **windows(),
                                  **{"next-incoming-id": {"type": "uint", "value": 0},
                                     "available": {"type": "uint", "value": 1}}),
                      channel=1,
                      note="flow/field:available.1, which five of the flow's fields carry "
                           "verbatim: \"When the handle field is not set, this field MUST "
                           "NOT be set\" — and this flow names no link. `available` is "
                           "chosen deliberately: the other four fields are read by rules "
                           "of their own (the delivery-count carriage, the credit echo), "
                           "so a vector carrying one of them is refused whether or not "
                           "the coupling is there and cannot witness it; nothing else in "
                           "the layer reads `available`")],
        note="a flow that carries the session's windows and a link's credit at once: the "
             "credit belongs to a link, so naming none while sending it is the refusal the "
             "five clauses state — and the window-only flows the rest of the corpus uses "
             "are the conforming case"))

    vectors.append(exchange(
        "exchange-flow-properties-without-handle", start=s("MAPPED"),
        clauses=[LINK_HANDLES, *FLOW_FIELDS_REQUIRE_HANDLE],
        steps=link_up() + [
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      body=t.body("flow", **windows(),
                                  **{"next-incoming-id": {"type": "uint", "value": 0},
                                     "properties": t.unsettled_map(
                                         [({"type": "symbol", "text": "x"},
                                           {"type": "uint", "value": 1})])}),
                      channel=1,
                      note="`flow/field:properties.1` is one of the five sentences "
                           "that read \"When the handle field is not set, this field "
                           "MUST NOT be set\", and the register's "
                           "`flow-link-field-without-handle` reading names all "
                           "five")],
        note="the coupling's fifth field, which the vector above does not reach: this "
             "flow names no handle and sets `properties`, so the rule refuses it with "
             "`amqp:invalid-field` and leaves the session in `session:DISCARDING`. The "
             "reference admitted the same frame until `5ad7b6b`; both artefacts have "
             "refused it since"))

    vectors.append(exchange(
        "exchange-link-credit-echoed", start=s("MAPPED"),
        clauses=[FLOW_SENDER_MATCHES_DELIVERY_LIMIT],
        steps=link_up() + [
            t.receive_frame(AMQP_FRAME,
                            t.flow_body(handle=0, delivery_count=0, link_credit=0),
                            state=s("MAPPED"), channel=1),
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      body=t.flow_body(handle=0, delivery_count=0, link_credit=7),
                      channel=1,
                      note="the ownership sentence link-credit carries: \"Only the "
                           "receiver endpoint can independently set this value. The sender "
                           "endpoint sets this to the last known value seen from the "
                           "receiver\" — this endpoint granted none, so a sender's flow "
                           "carrying seven is inventing the receiver's quantity rather "
                           "than echoing it")],
        note="the conservation law the artifact states in words rather than in a keyword: "
             "the sender's link-credit is what the receiver last sent, so a flow that "
             "names another value is a deviation — the first flow, echoing the zero this "
             "endpoint granted, is admitted"))

    vectors.append(exchange(
        "exchange-link-credit-echo-sent-not-the-last-known", start=s("MAPPED"),
        clauses=[FLOW_SENDER_MATCHES_DELIVERY_LIMIT, FLOW_CREDIT_RECEIVER_CHOOSES,
                 LINK_CREDIT_RECEIVER_SETS],
        steps=[t.send_frame(AMQP_FRAME, t.attach_body(role=False), state=s("MAPPED"),
                            channel=1),
               t.receive_frame(AMQP_FRAME, t.attach_body(role=True),
                               state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME,
                               t.flow_body(handle=0, delivery_count=0, link_credit=3),
                               state=s("MAPPED"), channel=1),
               t.refused("send", reason="malformed", condition=INVALID_FIELD,
                         state=s("MAPPED"),
                         body=link_flow(delivery_count=0, link_credit=5),
                         channel=1)],
        note="the conservation law in the direction this endpoint owns: the receiver chose "
             "three, and the flow we write as the link's sender names five, so the step is "
             "refused with `amqp:invalid-field` without the frame being written. The "
             "receive-direction vector above is the peer's half of the same quantity"))

    vectors.append(exchange(
        "exchange-link-credit-echo-sent-the-last-known", start=s("MAPPED"),
        clauses=[FLOW_SENDER_MATCHES_DELIVERY_LIMIT, FLOW_CREDIT_RECEIVER_CHOOSES,
                 LINK_CREDIT_RECEIVER_SETS],
        steps=[t.send_frame(AMQP_FRAME, t.attach_body(role=False), state=s("MAPPED"),
                            channel=1),
               t.receive_frame(AMQP_FRAME, t.attach_body(role=True),
                               state=s("MAPPED"), channel=1),
               t.receive_frame(AMQP_FRAME,
                               t.flow_body(handle=0, delivery_count=0, link_credit=3),
                               state=s("MAPPED"), channel=1),
               t.send_frame(AMQP_FRAME,
                            link_flow(delivery_count=0, link_credit=3),
                            state=s("MAPPED"), channel=1)],
        note="the conforming form of the same quantity: the sender's flow echoes the three "
             "the receiver last indicated, and every step is admitted. It is the "
             "delimitation for the refusal beside it — a layer that read the sender's flow "
             "as its own quantity would admit both frames, and one that refused any flow "
             "from the sending end would refuse this one too"))

    vectors.append(exchange(
        "exchange-link-credit-counts-messages-not-frames", start=s("MAPPED"),
        clauses=[FLOW_SENDER_STOPS_AT_ZERO_CREDIT, TRANSFER_FIRST_FIELDS],
        steps=link_up(role_sender=True, credit=1) + [
            t.send_frame(AMQP_FRAME, t.fragment_body(index, 3), state=s("MAPPED"),
                         channel=1, payload=message[index::3])
            for index in range(3)] + [
            t.refused("send", reason="limit", condition=FRAMING_ERROR, state=s("MAPPED"),
                      body=t.fragment_body(0, 1, delivery_id=1), channel=1,
                      payload=message,
                      note="the grant was one *message*, and this transfer begins a second "
                           "one: link-credit is \"the current maximum number of messages "
                           "that can be handled at the receiver endpoint\" and the "
                           "delivery-count \"is incremented whenever a message is set\"")],
        note="what the credit counts: one delivery of credit carries a message split over "
             "three transfers, because the two continuations are frames of a message "
             "already counted — a layer that charged per frame would refuse the second and "
             "third, and the exhaustion is shown by the delivery that does begin a second "
             "message"))

    vectors.append(exchange(
        "exchange-link-attach-keeps-the-credit", start=s("MAPPED"),
        clauses=[FLOW_SENDER_SETS_CREDIT, FLOW_DELIVERY_COUNT_SET_BY_SENDER],
        steps=link_up(role_sender=True, credit=1) + [
            t.receive_frame(AMQP_FRAME, t.attach_body(role=True, handle=1),
                            state=s("MAPPED"), channel=1),
            t.send_frame(AMQP_FRAME, t.fragment_body(0, 1), state=s("MAPPED"), channel=1,
                         payload=message)],
        note="an attach from the partner, arriving after the link is established and after "
             "the partner granted credit, names a handle this endpoint has not seen — and "
             "the flow state belongs to the link, not to the frame, so an attach that does "
             "not establish the link must not replace what the link has agreed: the "
             "transfer that follows is admitted on the credit the partner granted, and "
             "before this rule it was refused for having none"))

    # The two states the artifact gives a channel to, entered as *start* states.
    # `sessions.10` gives END_SENT its entry in the incoming channel map ("but is no
    # longer assigned an outgoing channel number") and `sessions.11` gives END_RCVD its
    # outgoing number with no incoming entry. A state reached by a step keeps the maps of
    # the state it came from, so only a vector that starts here can see what the state is
    # assigned — which is why these two begin at the state rather than arriving at it.
    vectors.append(exchange(
        "exchange-session-receive-in-end-sent", start=s("END_SENT"),
        clauses=[SESSION_STATES, WINDOW_AFTER_FLOW],
        steps=[t.receive_frame(AMQP_FRAME, t.flow_body(absent=FLOW_LINK_FIELDS),
                               state=s("END_SENT"), channel=1),
               t.receive_frame(AMQP_FRAME, t.body("end"), state=s("UNMAPPED"), channel=1)],
        note="END_SENT keeps the incoming channel map, so a flow arriving on it is this "
             "session's to receive and is admitted; the peer's end then releases the "
             "session, which is the one frame a state that cannot send still answers"))

    vectors.append(exchange(
        "exchange-session-send-in-end-rcvd", start=s("END_RCVD"),
        clauses=[SESSION_STATES, WINDOW_AFTER_FLOW],
        steps=[t.send_frame(AMQP_FRAME, t.flow_body(absent=FLOW_LINK_FIELDS),
                            state=s("END_RCVD"), channel=1),
               t.send_frame(AMQP_FRAME, t.body("end"), state=s("UNMAPPED"), channel=1)],
        note="END_RCVD keeps its outgoing channel number with no incoming entry, so a flow "
             "sent there is admitted and the end that follows releases the session"))

    # The direction the role fixes: a transfer is the sender's frame, so a link whose
    # endpoint is the sender may not receive one and an endpoint that is the receiver may
    # not send one. The condition is the artifact's `illegal-state`, "The peer sent a frame
    # that is not permitted in the current state" — not `framing-error`, whose definition
    # is about octets that form no frame header.
    vectors.append(exchange(
        "exchange-link-transfer-direction-received", start=s("MAPPED"),
        clauses=[SESSION_STATES],
        steps=link_up(role_sender=True) + [
            t.refused("receive", reason="illegalState", condition=ILLEGAL_STATE,
                      state=s("DISCARDING"), body=t.fragment_body(0, 1), channel=1,
                      payload=message,
                      note="this endpoint attached as the link's sender, so a transfer "
                           "arriving here is the peer's frame on the wrong end of the "
                           "link; a receive the session cannot process is answered by "
                           "the END an error, which is what DISCARDING records")],
        note="the received half of the role rule: the frame is well formed and the moment "
             "is wrong, which is illegal-state rather than a wire failure"))

    vectors.append(exchange(
        "exchange-link-transfer-direction-sent", start=s("MAPPED"),
        clauses=[SESSION_STATES],
        steps=link_up(role_sender=False) + [
            t.refused("send", reason="illegalState", condition=ILLEGAL_STATE,
                      state=s("MAPPED"), body=t.fragment_body(0, 1), channel=1,
                      payload=message,
                      note="this endpoint attached as the link's receiver, so offering a "
                           "transfer is offering the sender's frame from the wrong end; "
                           "a send it must not make is simply not made, so the state "
                           "stands")],
        note="the sent half: the same rule from the direction where the peer would have "
             "written the frame, and the state does not move because nothing was written"))

    # A state label and the channel map its description assigns are one fact, and a
    # transition that releases a channel must move the label with it: `BEGIN_SENT` "is
    # assigned an outgoing channel number", so sending the end that releases that channel
    # lands in `END_SENT`, whose description is exactly the maps the record then has.
    vectors.append(exchange(
        "exchange-session-send-end-in-begin-sent", start=s("BEGIN_SENT"),
        clauses=[SESSION_STATES, SESSION_TRANSITIONS, END_DISASSOCIATES],
        steps=[t.send_frame(AMQP_FRAME, t.body("end"), state=s("END_SENT"), channel=1),
               t.refused("receive", reason="illegalState", condition=FRAMING_ERROR,
                         state=s("END_SENT"), body=t.body("end"), channel=1,
                         note="END_SENT's own description is that it MAY receive frames and "
                              "not send them, so the end that follows is refused — and the "
                              "refusal is reached on the label, which is the point: this "
                              "session reached END_SENT with no incoming channel at all, "
                              "because BEGIN_SENT has none, whereas END_SENT's description "
                              "claims an incoming entry — the pair of descriptions cannot "
                              "both hold on this route")],
        note="a session that has sent its begin and sends its end: the label follows the "
             "channel, because BEGIN_SENT's own description claims the outgoing channel "
             "the end releases; the second step shows why the label's arrival here is not "
             "the whole story, since END_SENT is described as having an incoming entry and "
             "this route cannot give it one"))

    # The discarding phase, reached by a *rule* rather than by the channel map, so the
    # predicate that reaches it is tested rather than shadowed: an unattached handle is
    # refused by linkHandleOf in a state that can still receive, which is where the
    # widening bites. The second step is the peer's end, the one frame a discarding
    # session answers.
    vectors.append(exchange(
        "exchange-session-refusal-in-end-sent-discards", start=s("END_SENT"),
        clauses=[SESSION_STATES, SESSION_ERRORS],
        steps=[t.refused("receive", reason="illegalState", condition=UNATTACHED_HANDLE,
                         state=s("DISCARDING"),
                         body=t.flow_body(handle=7, delivery_count=0, link_credit=1,
                                          next_incoming=0),
                         channel=1,
                         note="a flow naming a handle this endpoint does not have, "
                              "refused by the handle rule rather than by the channel "
                              "map: sessions.6 then obliges the session to discard until "
                              "the peer's end, which is what DISCARDING records — and "
                              "the state it left is what the widening moves"),
               t.receive_frame(AMQP_FRAME, t.body("end"), state=s("UNMAPPED"), channel=1)],
        note="the predicate that reaches the discarding phase, tested by a rule: the "
             "channel map would answer first if the frame were on the wrong channel, "
             "which is why the handle rule is used here"))

    # -- the settlement negotiation: the flag against the mode it was negotiated under --
    #
    # `snd-settle-mode` is negotiated per link and per direction: an attach's value governs
    # what the side that wrote it sends. `settled.4`/`.5` and `.6` are that negotiation's
    # two obligations, each selected by the `choice` attribute of its xref rather than by
    # the field's declared type, and the corpus already carries the `settled` choice in the
    # receive direction (`exchange-link-sender-settle-mode-unmet`). The vectors below are
    # the rest of the matrix: the `unsettled` choice's MUST NOT in the direction each end
    # owns and its abort exemption in both, the `mixed` choice's absence of obligation, and
    # the delivery boundary each one is stated at — "at least one transfer frame for a
    # delivery" against "every transfer".
    settle_choices = {
        "unsettled": t.settle_mode("sender-settle-mode", "unsettled"),
        "settled": t.settle_mode("sender-settle-mode", "settled"),
        "mixed": t.settle_mode("sender-settle-mode", "mixed"),
        "first": t.settle_mode("receiver-settle-mode", "first"),
        "second": t.settle_mode("receiver-settle-mode", "second"),
    }

    vectors.append(exchange(
        "exchange-link-settled-over-unsettled-negotiation", start=s("MAPPED"),
        clauses=[TRANSFER_SETTLED_NEVER, SESSION_END_ON_ERROR, SESSION_ERRORS],
        steps=link_up(role_sender=False, peer_settle=settle_choices["unsettled"]) + [
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"), body=t.transfer_body(settled=True),
                      channel=1, payload=message)],
        note="the `unsettled` choice's obligation in the direction the peer owns: the "
             "link's sender negotiated it, so a transfer it flags settled is refused with "
             "`amqp:invalid-field` and the session lands in `session:DISCARDING`. The "
             "transfer's own exemption is the abort vector beside it, which is what keeps "
             "the pair a reading of the choice rather than of the flag; both artefacts "
             "admitted this frame until `5624f16`"))

    vectors.append(exchange(
        "exchange-link-settled-over-unsettled-negotiation-aborted", start=s("MAPPED"),
        clauses=[TRANSFER_SETTLED_NEVER, ABORTED_MESSAGES_DISCARDED, DATA_SECTION],
        steps=link_up(role_sender=False, peer_settle=settle_choices["unsettled"]) + [
            t.receive_frame(AMQP_FRAME,
                            t.transfer_body(settled=True, aborted=True),
                            state=s("MAPPED"), channel=1, payload=message)],
        note="the same sentence's exemption: the artifact forbids the flag on every "
             "transfer of a delivery \"unless the delivery is aborted\", so a settled, "
             "aborted transfer under the `unsettled` choice is admitted and the peer stays "
             "in `session:MAPPED`. It is the delimitation for the refusal beside it — a "
             "layer that refused the flag outright fails here, and the two together are "
             "what makes the choice, rather than the flag, the thing being read"))

    vectors.append(exchange(
        "exchange-link-settled-over-unsettled-negotiation-sent", start=s("MAPPED"),
        clauses=[TRANSFER_SETTLED_NEVER, TRANSFER_ONE_SECTION],
        steps=link_up(role_sender=True, credit=1,
                      own_settle=settle_choices["unsettled"]) + [
            t.refused("send", reason="malformed", condition=INVALID_FIELD,
                      state=s("MAPPED"), body=t.transfer_body(settled=True),
                      channel=1, payload=message)],
        note="the same obligation in the direction this endpoint owns: our own attach "
             "negotiated the `unsettled` choice, so a transfer we write under it must not "
             "carry the flag, and the step is refused with `amqp:invalid-field` without "
             "the frame being written. The receive-direction refusal above is the peer's "
             "half of the sentence; both artefacts wrote this frame until `5624f16`"))

    vectors.append(exchange(
        "exchange-link-settled-over-unsettled-negotiation-sent-aborted", start=s("MAPPED"),
        clauses=[TRANSFER_SETTLED_NEVER, ABORTED_MESSAGES_DISCARDED],
        steps=link_up(role_sender=True, credit=1,
                      own_settle=settle_choices["unsettled"]) + [
            t.send_frame(AMQP_FRAME, t.transfer_body(settled=True, aborted=True),
                         state=s("MAPPED"), channel=1, payload=message)],
        note="the exemption read from this endpoint's own side: under our `unsettled` "
             "negotiation a transfer we write may carry the flag when it aborts the "
             "delivery, and this one does, so the step is admitted and the peer stays in "
             "`session:MAPPED`. Beside the refusal it is what shows the rule is about the "
             "delivery the flag settles rather than about the field's presence"))

    vectors.append(exchange(
        "exchange-link-settled-on-a-continuation-suffices", start=s("MAPPED"),
        clauses=[TRANSFER_SETTLED, TRANSFER_FIRST_FIELDS, TRANSFER_ONE_SECTION],
        steps=link_up(role_sender=False, peer_settle=settle_choices["settled"]) + [
            t.receive_frame(AMQP_FRAME, t.transfer_body(more=True),
                            state=s("MAPPED"), channel=1, payload=message[:10]),
            t.receive_frame(AMQP_FRAME, t.transfer_body(identity=False, settled=True),
                            state=s("MAPPED"), channel=1, payload=message[10:]),
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      body=t.transfer_body(delivery_id=1), channel=1, payload=message,
                      note="the negotiation is `settled`, so this second delivery MUST be "
                           "settled in at least one of its transfers and this transfer "
                           "carries no flag: `settled.4` is per *delivery*, and the "
                           "delivery before this one was settled by its continuation")],
        note="`settled.4`'s boundary is a delivery rather than a transfer: the flag must be "
             "true on at least one transfer *for a delivery*, so a delivery whose first "
             "transfer leaves it unset and whose second sets it is complete and settled, "
             "and the next delivery — which settles nowhere — is the violation"))

    vectors.append(exchange(
        "exchange-link-settled-false-under-settled-negotiation", start=s("MAPPED"),
        clauses=[TRANSFER_SETTLED, SESSION_END_ON_ERROR, SESSION_ERRORS],
        steps=link_up(role_sender=False, peer_settle=settle_choices["settled"]) + [
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"), body=t.transfer_body(settled=False),
                      channel=1, payload=message)],
        note="the `settled` choice is met by the flag's content rather than by the field's "
             "presence: a transfer that sets `settled` to *false* settles no transfer of "
             "its delivery, so the delivery breaks the negotiation and is refused with "
             "`amqp:invalid-field`, leaving the peer in `session:DISCARDING`. Both "
             "artefacts admitted it until `d50abc1` and `1540777`; both refuse it since"))

    vectors.append(exchange(
        "exchange-link-mixed-negotiation-neither-obligation", start=s("MAPPED"),
        clauses=[TRANSFER_SETTLED, TRANSFER_SETTLED_NEVER, TRANSFER_ONE_SECTION],
        steps=link_up(role_sender=False, peer_settle=settle_choices["mixed"]) + [
            t.receive_frame(AMQP_FRAME, t.transfer_body(settled=True),
                            state=s("MAPPED"), channel=1, payload=message),
            t.receive_frame(AMQP_FRAME, t.transfer_body(delivery_id=1),
                            state=s("MAPPED"), channel=1, payload=message)],
        note="the third choice is the one both sentences exclude: with `mixed` negotiated, "
             "`settled.4` — which selects the `settled` choice — obliges nothing and "
             "`settled.6` — which selects `unsettled` — forbids nothing, so a settled "
             "delivery and an unsettled one are both admitted on the same link. This is "
             "the control that shows the two obligations do not leak onto a negotiation "
             "neither of them names"))

    # -- the receiver's settlement mode, and what a transfer may say about it -------- #

    vectors.append(exchange(
        "exchange-link-rcv-settle-second-over-first", start=s("MAPPED"),
        clauses=[TRANSFER_RCV_SETTLE_ILLEGAL, ATTACH_SETTLE_DEFAULT, SESSION_END_ON_ERROR,
                 SESSION_ERRORS],
        steps=link_up(role_sender=False, own_rcv_settle=settle_choices["first"]) + [
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      body=t.transfer_body(rcv_settle_mode=settle_choices["second"]),
                      channel=1, payload=message)],
        note="the mode the negotiation forbids: our attach fixed this link at `first`, so "
             "the peer's transfer naming `second` is refused with `amqp:invalid-field` and "
             "the session lands in `session:DISCARDING`. Both artefacts admitted this frame "
             "until `5624f16`; `exchange-link-rcv-settle-second-over-second` beside it is "
             "the same field value admitted under the other negotiation, which is what "
             "makes the refusal about the negotiation rather than the field"))

    vectors.append(exchange(
        "exchange-link-rcv-settle-second-over-first-ignored-when-settled",
        start=s("MAPPED"),
        clauses=[TRANSFER_RCV_SETTLE_IGNORED, TRANSFER_RCV_SETTLE_ILLEGAL],
        steps=link_up(role_sender=False, own_rcv_settle=settle_choices["first"]) + [
            t.receive_frame(AMQP_FRAME,
                            t.transfer_body(settled=True,
                                            rcv_settle_mode=settle_choices["second"]),
                            state=s("MAPPED"), channel=1, payload=message)],
        note="the same field and the same `first` negotiation as the refusal above, with "
             "the transfer sent settled: the sender's flag makes the field ignored, so the "
             "frame is admitted and the peer stays in `session:MAPPED`. It is the "
             "exemption rather than the rule, and a weaker witness than its neighbours for "
             "that reason — a layer that never read the field at all arrives here, so what "
             "the pair pins is the gate on the flag, not the refusal's own reach"))

    vectors.append(exchange(
        "exchange-link-rcv-settle-second-over-second", start=s("MAPPED"),
        clauses=[TRANSFER_RCV_SETTLE_ILLEGAL, ATTACH_SETTLE_DEFAULT, TRANSFER_ONE_SECTION],
        steps=link_up(role_sender=False, own_rcv_settle=settle_choices["second"]) + [
            t.receive_frame(
                AMQP_FRAME,
                t.transfer_body(rcv_settle_mode=settle_choices["second"]),
                state=s("MAPPED"), channel=1, payload=message)],
        note="the complement of the refusal beside it: `rcv-settle-mode.u1` forbids the "
             "field only against a link negotiated to `first`, so a link negotiated to "
             "`second` carries the same field value admitted — which is what makes the "
             "refusal about the negotiation rather than about the field's presence"))

    # -- the flow's counts against the quantities the two ends actually hold --------- #

    vectors.append(exchange(
        "exchange-flow-sender-count-not-its-current", start=s("MAPPED"),
        clauses=[FLOW_DELIVERY_COUNT_SET_BY_SENDER, SESSION_END_ON_ERROR, SESSION_ERRORS],
        steps=link_up(role_sender=False) + [
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      body=t.flow_body(handle=0, delivery_count=5, link_credit=0),
                      channel=1,
                      note="`flow/field:delivery-count.2`: a flow sent from the sender "
                           "endpoint to the receiver MUST carry the sender's *current* "
                           "delivery-count, and this link's sender has sent nothing, so "
                           "the count this receiver holds is zero and the frame claims "
                           "five")],
        note="the sender's half of the delivery-count rule, which the existing credit "
             "vector does not reach: the receiver's count is what the peer's deliveries "
             "have advanced, and a flow claiming a count of its own is the sender "
             "inventing the number the receiver checks. Both artefacts refuse this one "
             "frame for this one reason, and the clause's other readings — the field "
             "absent, and the receiver's own count restated — are the vectors beside it"))

    vectors.append(exchange(
        "exchange-flow-sender-count-null", start=s("MAPPED"),
        clauses=[FLOW_DELIVERY_COUNT_SET_BY_SENDER, SESSION_END_ON_ERROR,
                 SESSION_ERRORS],
        steps=link_up(role_sender=False) + [
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      body=t.body("flow", **windows(),
                                  **{"next-incoming-id": {"type": "uint", "value": 0},
                                     "handle": {"type": "uint", "value": 0},
                                     "link-credit": {"type": "uint", "value": 0}}),
                      channel=1)],
        note="the null form of the field the vector above pins a value for: this flow "
             "names the link and carries `delivery-count` as null, which the type system's "
             "trailing-null rule makes the field unset, so the rule refuses the frame with "
             "`amqp:invalid-field` and the session lands in `session:DISCARDING`. The "
             "reference admitted the same frame until `5ad7b6b`; both artefacts have "
             "refused it since"))

    vectors.append(exchange(
        "exchange-flow-sender-count-absent", start=s("MAPPED"),
        clauses=[FLOW_DELIVERY_COUNT_SET_BY_SENDER, SESSION_END_ON_ERROR,
                 SESSION_ERRORS],
        steps=link_up(role_sender=False) + [
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"), body=link_flow(), channel=1)],
        note="the presence half of the sender's count: this flow names the link and leaves "
             "the field off altogether, which the clause forbids as squarely as it forbids "
             "a wrong value, so the frame is refused with `amqp:invalid-field` and the "
             "session lands in `session:DISCARDING`. The vector above pins the value half "
             "of the same sentence; both artefacts admitted this frame until `5624f16`"))

    vectors.append(exchange(
        "exchange-flow-sender-count-absent-sent", start=s("MAPPED"),
        clauses=[FLOW_DELIVERY_COUNT_SET_BY_SENDER, SESSION_END_ON_ERROR,
                 SESSION_ERRORS],
        steps=[t.send_frame(AMQP_FRAME, t.attach_body(role=False), state=s("MAPPED"),
                            channel=1),
               t.refused("send", reason="malformed", condition=INVALID_FIELD,
                         state=s("MAPPED"), body=link_flow(), channel=1)],
        note="the same presence rule in the direction this endpoint owns: a flow we write "
             "as the link's sender that names the link without the field is not written at "
             "all, and the step is refused with `amqp:invalid-field` leaving the peer in "
             "`session:MAPPED`"))

    vectors.append(exchange(
        "exchange-flow-sender-count-not-its-current-sent", start=s("MAPPED"),
        clauses=[FLOW_DELIVERY_COUNT_SET_BY_SENDER, SESSION_END_ON_ERROR,
                 SESSION_ERRORS],
        steps=[t.send_frame(AMQP_FRAME, t.attach_body(role=False), state=s("MAPPED"),
                            channel=1),
               t.refused("send", reason="malformed", condition=INVALID_FIELD,
                         state=s("MAPPED"),
                         body=link_flow(delivery_count=5, link_credit=0),
                         channel=1)],
        note="the value half in the same direction: the count we write has to be this "
             "endpoint's own current one, and five is not the count of a sender that has "
             "sent nothing, so the step is refused with `amqp:invalid-field` without the "
             "frame being written"))

    vectors.append(exchange(
        "exchange-flow-receiver-count-echoed", start=s("MAPPED"),
        clauses=[FLOW_DELIVERY_COUNT_ECHO, FLOW_SENDER_SETS_CREDIT,
                 FLOW_SENDER_MATCHES_DELIVERY_LIMIT],
        steps=link_up(role_sender=True, credit=1) + [
            t.send_frame(AMQP_FRAME, t.transfer_body(), state=s("MAPPED"), channel=1,
                         payload=message),
            t.receive_frame(AMQP_FRAME, t.flow_body(handle=0, delivery_count=1,
                                                    link_credit=1),
                            state=s("MAPPED"), channel=1)],
        note="`flow/field:delivery-count.3` in its conforming form: a flow sent from the "
             "receiver to the sender MUST carry \"the last known value of the "
             "corresponding sending endpoint\", and this endpoint — the link's sender — "
             "has sent one delivery, so the receiver's flow carries one and the grant it "
             "carries is applied. It is the delimitation for the refusal beside it, which "
             "asks the same flow to carry a value that is not the sender's: a layer that "
             "read any value as the peer's would admit both, so the admitted half is what "
             "gives the refused half its meaning"))

    vectors.append(exchange(
        "exchange-flow-receiver-count-not-echoed", start=s("MAPPED"),
        clauses=[FLOW_DELIVERY_COUNT_ECHO, FLOW_SENDER_SETS_CREDIT],
        steps=link_up(role_sender=True, credit=1) + [
            t.send_frame(AMQP_FRAME, t.transfer_body(), state=s("MAPPED"), channel=1,
                         payload=message),
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      body=t.flow_body(handle=0, delivery_count=0, link_credit=1),
                      channel=1)],
        note="the receiver's flow refused for naming a count the sending endpoint never "
             "had: this endpoint is the link's sender and has sent one delivery, so a "
             "receiver's flow carrying zero is refused with `amqp:invalid-field` and the "
             "session lands in `session:DISCARDING`. Both artefacts admitted this frame "
             "until `5624f16`"))

    # The `.4` moment: the peer is the link's receiver and *this* endpoint has not attached
    # yet, so there is no sender for it to have a count from. Neither vector can use
    # `link_up`, whose first step is our own attach — the rule is about the state before it.
    peer_receiver_only = t.receive_frame(AMQP_FRAME, t.attach_body(role=True, handle=0),
                                         state=s("MAPPED"), channel=1)

    vectors.append(exchange(
        "exchange-flow-receiver-count-set-before-sender-attach", start=s("MAPPED"),
        clauses=[FLOW_DELIVERY_COUNT_NOT_BEFORE_ATTACH, SESSION_END_ON_ERROR,
                 SESSION_ERRORS],
        steps=[peer_receiver_only,
               t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                         state=s("DISCARDING"),
                         body=link_flow(delivery_count=0, link_credit=0),
                         channel=1)],
        note="the count a receiver may not name yet: the peer attached as the link's "
             "receiver and this endpoint has not attached, so it has seen no sender to "
             "take a count from, and its flow setting the field is refused with "
             "`amqp:invalid-field`, leaving the session in `session:DISCARDING`. The "
             "conforming form beside it leaves the field off, which is what makes the "
             "refusal about the field's presence rather than the flow's"))

    vectors.append(exchange(
        "exchange-flow-receiver-count-absent-before-sender-attach", start=s("MAPPED"),
        clauses=[FLOW_DELIVERY_COUNT_NOT_BEFORE_ATTACH, FLOW_DELIVERY_COUNT_ECHO],
        steps=[peer_receiver_only,
               t.receive_frame(AMQP_FRAME, link_flow(), state=s("MAPPED"), channel=1)],
        note="the conforming form of the rule above: at the same moment the receiver's "
             "flow carries the windows and names the link with no count, and both steps "
             "are admitted. It is the delimitation for the refusal beside it, since the "
             "echo rule that governs the receiver's later flows is the one this moment "
             "excepts"))

    # -- `more` and `aborted`: the delivery a transfer ends, and the one it discards --- #

    vectors.append(exchange(
        "exchange-link-aborted-continuation-discards-prior", start=s("MAPPED"),
        clauses=[TRANSFER_MORE_ABORTED_PRECEDENCE, TRANSFER_ABORT_PRIOR_DATA,
                 ABORTED_MESSAGES_DISCARDED, DATA_SECTION],
        steps=link_up(role_sender=False) + [
            t.receive_frame(AMQP_FRAME, t.transfer_body(more=True),
                            state=s("MAPPED"), channel=1, payload=message[:10]),
            t.receive_frame(AMQP_FRAME, t.transfer_body(identity=False, aborted=True,
                                                        more=True),
                            state=s("MAPPED"), channel=1, payload=message[10:]),
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"),
                      body=t.transfer_body(identity=False), channel=1, payload=message,
                      note="the delivery the abort discarded is gone, so a transfer that "
                           "omits the three identity fields has nothing to continue")],
        note="`more.u1`'s precedence over a delivery that was already in progress: the "
             "aborted transfer carries `more` as well, and the value is ignored — the "
             "delivery it aborts is discarded *with* the data its earlier transfer "
             "carried, which is `links.33`'s \"the receiver MUST discard the message data "
             "that was transferred prior to the abort\". The third step is how that is "
             "observable: a continuation with no delivery to continue is refused"))

    vectors.append(exchange(
        "exchange-link-aborted-then-next-delivery", start=s("MAPPED"),
        clauses=[TRANSFER_MORE_ABORTED_PRECEDENCE, ABORTED_MESSAGES_DISCARDED,
                 TRANSFER_FIRST_FIELDS],
        steps=link_up(role_sender=False) + [
            t.receive_frame(AMQP_FRAME, t.transfer_body(aborted=True, more=True),
                            state=s("MAPPED"), channel=1, payload=message),
            t.receive_frame(AMQP_FRAME, t.transfer_body(delivery_id=1),
                            state=s("MAPPED"), channel=1, payload=message)],
        note="the complement of the abort vector: an aborted delivery leaves the link "
             "usable, so the next transfer is a first transfer of a new delivery and is "
             "admitted. `aborted.2` discards the delivery and its payload, not the link"))

    vectors.append(exchange(
        "exchange-link-aborted-false-spends-no-credit", start=s("MAPPED"),
        clauses=[ABORTED_MESSAGES_DISCARDED, FLOW_SENDER_STOPS_AT_ZERO_CREDIT,
                 TRANSFER_MORE_ABORTED_PRECEDENCE],
        steps=link_up(role_sender=True, credit=1) + [
            t.send_frame(AMQP_FRAME, t.transfer_body(aborted=False),
                         state=s("MAPPED"), channel=1, payload=message),
            t.refused("send", reason="limit", condition=FRAMING_ERROR,
                      state=s("MAPPED"), body=t.transfer_body(delivery_id=1),
                      channel=1, payload=message)],
        note="the credit an aborted delivery spends turns on what `aborted` carries: a "
             "transfer whose flag is *false* is not an aborted delivery, so it consumes the "
             "one delivery the receiver granted and the delivery after it is refused with "
             "`amqp:connection:framing-error` and class `limit`, the peer staying in "
             "`session:MAPPED`. The reference admitted that delivery until `1540777`; both "
             "artefacts have refused it since"))

    vectors.append(exchange(
        "exchange-link-aborted-spends-the-credit", start=s("MAPPED"),
        clauses=[ABORTED_MESSAGES_DISCARDED, FLOW_SENDER_STOPS_AT_ZERO_CREDIT,
                 TRANSFER_ABORT_PRIOR_DATA],
        steps=link_up(role_sender=True, credit=1) + [
            t.send_frame(AMQP_FRAME, t.transfer_body(aborted=True),
                         state=s("MAPPED"), channel=1, payload=message),
            t.refused("send", reason="limit", condition=FRAMING_ERROR,
                      state=s("MAPPED"), body=t.transfer_body(delivery_id=1),
                      channel=1, payload=message)],
        note="an aborted delivery spends the credit it was sent under, so the delivery the "
             "receiver's grant does not cover is refused with "
             "`amqp:connection:framing-error` and class `limit`, the peer staying in "
             "`session:MAPPED`. The reference admitted it until `1540777`; both artefacts "
             "have refused it since"))

    vectors.append(exchange(
        "exchange-link-more-false-completes-the-delivery", start=s("MAPPED"),
        clauses=[TRANSFER_MORE_LAST_FRAME, TRANSFER_FIRST_FIELDS],
        steps=link_up() + [
            t.receive_frame(AMQP_FRAME, t.transfer_body(more=False),
                            state=s("MAPPED"), channel=1, payload=message),
            t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                      state=s("DISCARDING"), body=t.transfer_body(identity=False),
                      channel=1, payload=message)],
        note="`more` carries a value rather than a presence: a transfer whose flag is "
             "*false* is the last of its delivery, so the delivery is complete and the "
             "continuation that follows it — a transfer with nothing to continue — is "
             "refused with `amqp:invalid-field`, leaving the peer in `session:DISCARDING`. "
             "Both artefacts admitted both steps until `d50abc1` and `1540777`; both refuse "
             "the continuation since"))

    # -- resumption: the flag a resumed delivery is named by ------------------------- #

    vectors.append(exchange(
        "exchange-link-resume-on-first-transfer", start=s("MAPPED"),
        clauses=[TRANSFER_RESUME_FIRST_TRANSFER, TRANSFER_FIRST_FIELDS,
                 TRANSFER_ONE_SECTION],
        steps=link_up(role_sender=False) + [
            t.receive_frame(AMQP_FRAME, t.transfer_body(resume=True, more=True),
                            state=s("MAPPED"), channel=1, payload=message[:10]),
            t.receive_frame(AMQP_FRAME, t.transfer_body(identity=False),
                            state=s("MAPPED"), channel=1, payload=message[10:])],
        note="`resume.3` and `.4` read together: the flag MUST be set on the *first* "
             "transfer of a resumed delivery, and on a subsequent transfer it MAY be set "
             "or omitted — so a resumed delivery named on its first transfer and left "
             "unnamed on its continuation is the conforming case, and admission is the "
             "observable"))

    # -- the fields an attach's own clauses make it carry or omit -------------------- #

    vectors.append(exchange(
        "exchange-link-attach-sender-without-initial-count", start=s("MAPPED"),
        clauses=[ATTACH_INITIAL_COUNT, ATTACH_DEFAULTS, SESSION_END_ON_ERROR,
                 SESSION_ERRORS],
        steps=[t.send_frame(AMQP_FRAME, t.attach_body(role=True), state=s("MAPPED"),
                            channel=1),
               t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                         state=s("DISCARDING"),
                         body=t.body("attach", name={"type": "string", "text": "link"},
                                     handle={"type": "uint", "value": 0},
                                     role={"type": "boolean", "value": False}),
                         channel=1,
                         note="the peer's attach declares the sender role and carries no "
                              "`initial-delivery-count`, which "
                              "`attach/field:initial-delivery-count.1` forbids: \"This "
                              "MUST NOT be null if role is sender\"")],
        note="a mandatory-by-condition field rather than a mandatory one: the declared "
             "surface marks neither, so the rule is the role's — the same attach with the "
             "receiver role is the vector beside this one, where the omission is the "
             "default the clause says is ignored"))

    vectors.append(exchange(
        "exchange-link-attach-receiver-without-initial-count", start=s("MAPPED"),
        clauses=[ATTACH_INITIAL_COUNT, ATTACH_DEFAULTS],
        steps=[t.send_frame(AMQP_FRAME, t.attach_body(role=True), state=s("MAPPED"),
                            channel=1),
               t.receive_frame(AMQP_FRAME, t.attach_body(role=True),
                               state=s("MAPPED"), channel=1)],
        note="the ignored half of the same sentence: \"This MUST NOT be null if role is "
             "sender, and it is ignored if the role is receiver\" — so the attach whose "
             "role is the receiver and which omits the field is admitted, and the refusal "
             "beside it is about the role rather than about the field"))

    # -- the begin's remote-channel in both directions ------------------------------- #

    vectors.append(exchange(
        "exchange-session-begin-with-remote-channel", start=s("UNMAPPED"),
        clauses=[BEGIN_LOCAL_REMOTE_CHANNEL, BEGIN_ESTABLISHES, SESSION_STATES,
                 SESSION_TRANSITIONS],
        steps=[t.refused("send", reason="malformed", condition=INVALID_FIELD,
                         state=s("UNMAPPED"),
                         body=t.body("begin", **windows(),
                                     **{"remote-channel": {"type": "ushort", "value": 1}}),
                         channel=1,
                         note="a locally initiated session's begin MUST NOT set "
                              "`remote-channel`: this endpoint has not received a remote "
                              "begin, so there is no channel for the field to name"),
               t.send_frame(AMQP_FRAME, t.body("begin", **windows()),
                            state=s("BEGIN_SENT"), channel=1)],
        note="the refusal half of `begin/field:remote-channel.1`, which no vector pins: "
             "the corpus's two begin vectors carry the field only where it is required, "
             "and this one offers it where it is forbidden — the second step shows the "
             "refusal is about the field, since the same begin without it is admitted"))

    vectors.append(exchange(
        "exchange-session-begin-answer-without-remote-channel", start=s("BEGIN_RCVD"),
        clauses=[BEGIN_ESTABLISHES, BEGIN_REMOTE_CHANNEL, SESSION_STATES,
                 SESSION_TRANSITIONS],
        steps=[t.refused("send", reason="malformed", condition=INVALID_FIELD,
                         state=s("BEGIN_RCVD"),
                         body=t.body("begin", **windows()), channel=1,
                         note="the peer's begin arrived on channel one and this begin "
                              "answers it, so `remote-channel` MUST be set to that "
                              "channel — `.1`'s MUST NOT and `.2`'s MUST are one "
                              "sentence, and this is the second half"),
               t.send_frame(AMQP_FRAME, t.body("begin", **windows(),
                                               **{"remote-channel": {"type": "ushort",
                                                                     "value": 1}}),
                            state=s("MAPPED"), channel=1)],
        note="the answering begin's field, refused for being absent: the corpus pins the "
             "conforming value in `exchange-session-begin-remotely-initiated`, and this "
             "vector pins what the section says about a begin that leaves it out"))

    # -- a flow's next-incoming-id before the peer's begin -------------------------- #

    vectors.append(exchange(
        "exchange-session-flow-next-incoming-id-before-begin", start=s("BEGIN_SENT"),
        clauses=[FLOW_NEXT_INCOMING_ID, SESSION_STATES, SESSION_TRANSITIONS],
        steps=[t.refused("send", reason="malformed", condition=INVALID_FIELD,
                         state=s("BEGIN_SENT"),
                         body=t.body("flow", **windows(),
                                     **{"next-incoming-id": {"type": "uint", "value": 0}}),
                         channel=1,
                         note="`flow/field:next-incoming-id.1`: the field \"MUST be set if "
                              "the peer has received the begin frame for the session, and "
                              "MUST NOT be set if it has not\" — this endpoint has sent "
                              "its own begin and the peer has not answered, so the "
                              "partner's begin has not arrived and the field is forbidden"),
               t.send_frame(AMQP_FRAME, t.body("flow", **windows()),
                            state=s("BEGIN_SENT"), channel=1)],
        note="the MUST NOT half of the rule whose MUST half the corpus pins twice: a flow "
             "may be sent from BEGIN_SENT — the state's description says it may send — and "
             "the only rule that refuses this one is the field's own, which the second "
             "step shows by carrying the same frame without it"))

    # -- the dispatch: a session performative on the connection's channel ----------- #

    vectors.append(exchange(
        "exchange-session-frame-on-channel-zero", start=s("MAPPED"),
        clauses=[DISPATCH_TABLE, CHANNEL_MAP, OPEN_ON_CHANNEL_ZERO],
        steps=[t.refused("send", reason="illegalState", condition=FRAMING_ERROR,
                         state=c("OPENED"), body=t.transfer_body(), channel=0,
                         note="channel zero is the connection's, and a session "
                              "performative on it belongs to no session: the register's "
                              "`channel-zero-layering` reading is that the artifact does "
                              "not say so and the dispatch table's two connection frames "
                              "are all it gives the connection, so the refusal is the "
                              "codec's reading rather than a clause's"),
               t.send_frame(AMQP_FRAME,
                            t.body("flow", **{
                                "next-incoming-id": {"type": "uint", "value": 0},
                                "incoming-window": {"type": "uint", "value": 1000},
                                "next-outgoing-id": {"type": "uint", "value": 0},
                                "outgoing-window": {"type": "uint", "value": 1000}}),
                            state=s("MAPPED"), channel=1)],
        note="the dispatch table's channel rule, which the interface fixes and no vector "
             "has exercised: `open` and `close` are the connection's whatever channel "
             "they carry, and every other performative belongs to the session on *its* "
             "channel — so a transfer on channel zero is a frame the connection cannot "
             "relay and no session can answer, and the second step is its admitted "
             "sibling on the session's own channel"))

    return vectors


def staged_corpus(tables: Corpus) -> list[dict]:
    """Vectors whose expectations the artefacts do not both meet, staged rather than
    carried.

    An exchange corpus is a contract, and every vector in `vectors/` has to pass in both
    artefacts or the gate that runs it is red. These vectors are the ones authored from
    the artifact whose expectation at least one artefact refuses to meet: each note names
    the clause the expectation comes from, which of the two classes it is, and what each
    artefact actually did — the buffer it was given, the answer it gave, and the class it
    named. They are written to a path the caller names, outside `vectors/`, so the corpus
    a gate reads stays green while the finding stays in a file a fix slice can lift.

    Every vector here is now a **shared gap**: a frame both artefacts admit (or refuse)
    against the clause, so no differential can see it. The class it is not — a
    **divergence**, a frame the two artefacts answer differently, with neither side chosen
    here — held the aborted-credit pair and is empty since `d50abc1` and `1540777` aligned
    them; both are in `vectors/`, with the two flag readings the same commits settled.

    Shared gaps only is the stronger statement, and the one worth carrying: every vector
    staged here is a rule neither artefact enforces, so no comparison between the two can
    see any of them, and this corpus is the only instrument that can. What is staged is the
    ledger's deferred obligations made visible rather than a backlog of defects for one side
    to fix.

    Eleven members have left since the family was first written — the two `61c0430` aligned,
    the four the transfer-flag reading settled at `1a21b0a`, and the five settlement and count
    readings `5624f16` carried — and the four that remain fall into two subjects rather than
    one. Three are resumption readings the model restriction puts out of reach:
    `transfer/field:resume.2`, `.3` and `attach/field:unsettled.5` each name the local
    unsettled map or a resumed delivery, and one link per session is the whole of the model's
    link state. The fourth needs no link at all — a frame whose header is all there is,
    arriving in a connection that is over, where `picture.24`'s column for both directions
    is `-`.
    """
    t = tables
    message = b"a message whose split points are the vector's business"

    def link_up(role_sender: bool = False, credit: int = 1000) -> list:
        return [
            t.send_frame(AMQP_FRAME, t.attach_body(role=not role_sender),
                         state=s("MAPPED"), channel=1),
            t.receive_frame(AMQP_FRAME, t.attach_body(role=role_sender),
                            state=s("MAPPED"), channel=1),
            t.receive_frame(AMQP_FRAME, t.flow_body(
                handle=0, delivery_count=0,
                link_credit=(credit if role_sender else 0)),
                state=s("MAPPED"), channel=1)]

    return [
        # -- frames both artefacts admit against the clause --------------------- #

        exchange(
            "staged-link-resume-sent-not-in-map", start=s("MAPPED"),
            clauses=[TRANSFER_RESUME_SENDER_MUST_NOT, TRANSFER_ONE_SECTION],
            steps=link_up(role_sender=True, credit=1) + [
                t.refused("send", reason="malformed", condition=INVALID_FIELD,
                          state=s("MAPPED"), body=t.transfer_body(resume=True), channel=1,
                          payload=message)],
            note="**Shared gap.** `transfer/field:resume.2`: \"The sender MUST NOT send "
                 "resumed transfers for deliveries not in its local unsettled map.\" Our "
                 "endpoint is the link's sender and has sent nothing, so a resumed "
                 "transfer for delivery zero is a resume of a delivery that does not "
                 "exist. **Both artefacts write it**: neither reads the `resume` field, "
                 "which the specification's disposition records as uncarried "
                 "(`deferred:S4`) and the reference's layer never mentions. The clause is "
                 "stated for the sending end, so this is one a conformance check could "
                 "hold without an unsettled map — the map's absence is what makes the "
                 "delivery's absence easy to state and impossible to check"),

        exchange(
            "staged-link-resume-only-on-continuation", start=s("MAPPED"),
            clauses=[TRANSFER_RESUME_FIRST_TRANSFER, TRANSFER_FIRST_FIELDS],
            steps=link_up() + [
                t.receive_frame(AMQP_FRAME, t.transfer_body(more=True),
                                state=s("MAPPED"), channel=1, payload=message[:10]),
                t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                          state=s("DISCARDING"),
                          body=t.transfer_body(identity=False, resume=True), channel=1,
                          payload=message[10:])],
            note="**Shared gap.** `resume.3`: \"If a resumed delivery spans more than one "
                 "transfer performative, then the resume flag MUST be set to true on the "
                 "*first* transfer of the resumed delivery.\" The delivery here is "
                 "resumed — its continuation says so — while the first transfer that "
                 "began it did not. **Both artefacts admit** both steps. The corpus's "
                 "admitted half (`exchange-link-resume-on-first-transfer`) has the flag "
                 "where the clause requires it, and the pair is what separates \"the flag "
                 "is read\" from \"the flag is required in a place\""),

        exchange(
            "staged-link-attach-unsettled-null-key", start=s("MAPPED"),
            clauses=[ATTACH_UNSETTLED_NULL_KEY, ATTACH_DEFAULTS],
            steps=[t.send_frame(AMQP_FRAME, t.attach_body(role=True), state=s("MAPPED"),
                                channel=1),
                   t.refused("receive", reason="malformed", condition=INVALID_FIELD,
                             state=s("DISCARDING"),
                             body=t.body("attach",
                                         name={"type": "string", "text": "link"},
                                         handle={"type": "uint", "value": 0},
                                         role={"type": "boolean", "value": False},
                                         **{"initial-delivery-count":
                                                {"type": "uint", "value": 0},
                                            "unsettled": t.unsettled_map(
                                                [({"type": "null"},
                                                  {"type": "binary", "hex": "00"})])}),
                             channel=1)],
            note="**Shared gap.** `attach/field:unsettled.5`: \"The unsettled map MUST NOT "
                 "contain null valued keys.\" A null key is a legal map key in the type "
                 "system — which is why the clause has to forbid it *here* — and the "
                 "reference decodes this frame happily. **Both artefacts admit** it: "
                 "neither reads the `unsettled` field at all, and the specification's "
                 "disposition records the generated table row as the field's only trace. "
                 "The map itself is well formed (an even item count, a null key, an "
                 "octet-string value), so the only rule this frame breaks is the one the "
                 "vector names"),

        exchange(
            "staged-bodyless-frame-in-end", start=c("END"),
            clauses=[STATE_TABLE, EMPTY_FRAME, EMPTY_FRAME_ANY_CHANNEL],
            steps=[t.refused("receive", reason="illegalState", condition=ILLEGAL_STATE,
                             state=c("END"), octets=empty_frame(channel=0),
                             note="END's legal receives are `-`, so a frame arrives where "
                                  "the table admits none"),
                   t.refused("receive", reason="illegalState", condition=ILLEGAL_STATE,
                             state=c("END"), octets=empty_frame(channel=1))],
            note="**Shared gap: a frame with no body defeats the table's `-` column.** "
                 "`picture.24` gives END `-` in both columns, and the corpus already pins "
                 "that a `close` and a protocol header arriving there are refused with "
                 "`amqp:illegal-state` and class `illegalState`. A frame whose header is "
                 "all there is — which `framing.4` licenses, and which "
                 "`doc-idle-time-out.10` forbids *sending* after a close — is **admitted "
                 "by both artefacts in END**, with no state change, because both "
                 "short-circuit on a bodyless frame before the state column is consulted. "
                 "The idle-timeout clause requires a peer to handle empty frames \"on any "
                 "valid channel\"; it does not license one on a connection that is over, "
                 "and the table's `-` is what says so")
    ]


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


