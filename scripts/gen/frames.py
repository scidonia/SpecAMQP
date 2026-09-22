"""The frame corpus: every performative in both directions, and the layout's arithmetic.

One family of the corpus generator: `scripts/gen-value-vectors.py --frames PATH` is the
command line that dispatches to it. Its encoder is the value family's, imported rather
than transcribed a second time, so a value the frame corpus carries is encoded exactly
as the value corpus encodes it.
"""

from __future__ import annotations

import pathlib
from xml.etree import ElementTree

from gen.values import be, encode

ROOT = pathlib.Path(__file__).resolve().parents[2]
# --------------------------------------------------------------- frame vectors
#
# The frame layer's layout is prose and ASCII art in the framing section rather than a
# machine-readable declaration, so this transcribes it exactly as the two frame layers
# do, and cites the same clauses. Everything else is *read* from the declared surface:
# which types are performatives, which fields each one carries, which of those are
# mandatory, what their defaults say, and what the artifact defines MIN-MAX-FRAME-SIZE
# to be. Nothing here is a second hand-written list of any of that.

FRAMING_CLAUSE = "amqp-core-transport-v1.0-os.xml#amqp:transport/section:framing.1"
PERFORMATIVE_CLAUSE = "amqp-core-transport-v1.0-os.xml#amqp:transport/section:framing.3"
SASL_CLAUSE = "amqp-core-security-v1.0-os.xml#amqp:security/section:sasl.1"

FRAME_HEADER = 8      # the layout: a fixed eight-octet frame header
FRAME_WORD = 4        # DOFF counts four-octet words
FRAME_MIN_DOFF = 2    # with an eight-octet header the body cannot start earlier
AMQP_FRAME = 0x00
SASL_FRAME = 0x01

# The element constructor an array field's elements are written under: the fixed forms
# the fields of these performatives name, since an array's elements are written in the
# array's declared form. (The element-constructor family below covers the rest of the
# table, including the compound and array categories.)
ARRAY_CONSTRUCTOR = {"symbol": "a3", "string": "a1", "binary": "a0",
                     "ubyte": "50", "ushort": "60", "uint": "70", "ulong": "80"}


def declared_types() -> dict[str, ElementTree.Element]:
    """Every declared type across the pinned artifacts, by name.

    Part 2 and Part 5 declare the performatives and Part 1 declares most of the types
    their fields name, while a restricted type may be declared in one part and used in
    another, so the whole declared surface is read rather than a single artifact.
    """
    types: dict[str, ElementTree.Element] = {}
    for path in sorted((ROOT / "spec" / "oasis").glob("amqp-core-*-v1.0-os.xml")):
        for element in ElementTree.parse(path).getroot().iter("type"):
            if element.get("name") and element.get("class"):
                types.setdefault(element.get("name"), element)
    return types


def defined_constant(name: str) -> str:
    """The value of a `<definition>` the artifact's text names, so a constant a vector
    asserts about is read rather than copied."""
    for path in sorted((ROOT / "spec" / "oasis").glob("amqp-core-*-v1.0-os.xml")):
        for element in ElementTree.parse(path).getroot().iter("definition"):
            if element.get("name") == name:
                return element.get("value")
    raise SystemExit(f"gen-value-vectors: the artifacts define no constant {name!r}")


def type_chain(types: dict[str, ElementTree.Element], name: str) -> list[ElementTree.Element]:
    """A declared type and the restricted types it is defined over, in order."""
    chain: list[ElementTree.Element] = []
    current = types.get(name)
    while current is not None:
        chain.append(current)
        if current.get("class") != "restricted":
            break
        current = types.get(current.get("source"))
    if not chain or chain[-1].get("class") != "primitive":
        raise SystemExit(f"gen-value-vectors: {name!r} does not resolve to a primitive type")
    return chain


def primitive_name(types: dict[str, ElementTree.Element], name: str) -> str:
    return type_chain(types, name)[-1].get("name")


def sample_value(types: dict[str, ElementTree.Element], declared: str) -> dict:
    """A value of the declared type, for a field that must be present and carries no
    default. Only the primitives the performatives' mandatory fields actually reach are
    given a sample: a type with no sample is a generator gap, and says so rather than
    guessing at an encoding."""
    primitive = primitive_name(types, declared)
    if primitive == "string":
        return {"type": "string", "text": "v"}
    if primitive == "symbol":
        return {"type": "symbol", "text": "PLAIN"}
    if primitive == "binary":
        return {"type": "binary", "hex": "00"}
    if primitive == "boolean":
        return {"type": "boolean", "value": True}
    if primitive in ("ubyte", "ushort", "uint", "ulong", "byte", "short", "int", "long"):
        return {"type": primitive, "value": 0}
    if primitive == "timestamp":
        return {"type": "timestamp", "milliseconds": 0}
    if primitive == "char":
        return {"type": "char", "codepoint": 65}
    if primitive == "uuid":
        return {"type": "uuid", "hex": "00" * 16}
    raise SystemExit(f"gen-value-vectors: no sample value for a {primitive!r} field")


def default_value(types: dict[str, ElementTree.Element], declared: str, text: str) -> dict:
    """The artifact's `default` attribute read as a value of the field's declared type.

    The attribute is untyped text — numerals, booleans and choice names in one field —
    so reading it is a transcription rule of its own, and this is the one place it
    lives. A numeral becomes a value of the primitive the type resolves to, `true` and
    `false` become booleans, and anything else must name one of the type's declared
    choice values, which the artifact gives a numeral for.
    """
    primitive = primitive_name(types, declared)
    if text in ("true", "false"):
        if primitive != "boolean":
            raise SystemExit(f"gen-value-vectors: {declared} default {text!r} is not a boolean")
        return {"type": "boolean", "value": text == "true"}
    try:
        number: int | None = int(text)
    except ValueError:
        number = None
    if number is None:
        for element in type_chain(types, declared):
            for child in element:
                if child.tag == "choice" and child.get("name") == text:
                    number = int(child.get("value"))
    if number is None:
        raise SystemExit(f"gen-value-vectors: {declared} default {text!r} is neither a "
                         f"numeral, a boolean nor a declared choice name")
    if primitive not in ("ubyte", "ushort", "uint", "ulong", "byte", "short", "int", "long"):
        raise SystemExit(f"gen-value-vectors: {declared} default {text!r} is a numeral while "
                         f"the type resolves to {primitive}")
    return {"type": primitive, "value": number}


def field_value(types: dict[str, ElementTree.Element], field: ElementTree.Element) -> dict | None:
    """A field's value: its declared default where it has one, a sample where it is
    mandatory, and null where it is neither — and the trailing nulls are then dropped
    from the end of the field list, which is what the trailing-null rule allows."""
    declared = field.get("type")
    default = field.get("default")
    if default is not None:
        return default_value(types, declared, default)
    if field.get("mandatory") == "true":
        if field.get("multiple") == "true":
            primitive = primitive_name(types, declared)
            if primitive not in ARRAY_CONSTRUCTOR:
                raise SystemExit(f"gen-value-vectors: no array constructor for {primitive!r}")
            return {"type": "array", "constructor": ARRAY_CONSTRUCTOR[primitive],
                    "items": [sample_value(types, declared)]}
        return sample_value(types, declared)
    return None


def performative_value(types: dict[str, ElementTree.Element], element: ElementTree.Element) -> dict:
    """One performative as a described value: its descriptor, and its fields in wire
    order."""
    descriptor = next(element.iter("descriptor"))
    code = int(descriptor.get("code").split(":")[1], 16)
    fields = list(element.iter("field"))
    last = 0
    for index, field in enumerate(fields):
        if field.get("default") is not None or field.get("mandatory") == "true":
            last = index + 1
    items = []
    for field in fields[:last]:
        value = field_value(types, field)
        items.append(value if value is not None else {"type": "null"})
    return {"type": "described", "descriptor": {"type": "ulong", "value": code},
            "value": {"type": "list", "items": items}}


def performatives(types: dict[str, ElementTree.Element]) -> list[tuple[str, int, int]]:
    """Every performative the artifacts give a frame role, as (name, descriptor code,
    frame type octet). The role is the artifact's own `provides`, not a list here."""
    found: list[tuple[str, int, int]] = []
    for artifact, provides, frame_type in (
            ("amqp-core-transport-v1.0-os.xml", "frame", AMQP_FRAME),
            ("amqp-core-security-v1.0-os.xml", "sasl-frame", SASL_FRAME)):
        root = ElementTree.parse(ROOT / "spec" / "oasis" / artifact).getroot()
        for element in root.iter("type"):
            if provides in (element.get("provides") or "").split():
                descriptor = next(element.iter("descriptor"))
                code = int(descriptor.get("code").split(":")[1], 16)
                found.append((element.get("name"), code, frame_type))
    return found


def frame_octets(frame_type: int, doff: int, body: bytes, payload: bytes = b"",
                 extended: bytes = b"", channel: int = 0) -> bytes:
    """The frame a body is carried in, with SIZE computed from the octets exactly as the
    layout requires: header, extended header and frame body."""
    size = FRAME_HEADER + len(extended) + len(body) + len(payload)
    return be(size, 4) + bytes([doff, frame_type]) + be(channel, 2) + extended + body + payload


def frame_pair(vectors: list[dict], name: str, frame_type: int, doff: int, body: dict,
               payload: bytes = b"", extended: bytes = b"",
               clauses: list[str] | None = None, note: str = "") -> None:
    """One frame as both directions of the corpus: its octets decode to it, and it
    encodes to those octets."""
    clause_list = clauses if clauses is not None else [FRAMING_CLAUSE, PERFORMATIVE_CLAUSE]
    body_bytes = encode(body)
    octets = frame_octets(frame_type, doff, body_bytes, payload, extended)
    frame: dict = {"size": len(octets), "doff": doff, "type": f"{frame_type:02x}",
                   "channel": 0, "body": [body]}
    if extended:
        frame["extended"] = extended.hex()
    if payload:
        frame["payload"] = payload.hex()
    vectors.append({"vector": f"gen-frame-{name}", "kind": "frame-decode",
                    "clauses": clause_list, "bytes": octets.hex(), "frame": frame,
                    "note": note})
    vectors.append({"vector": f"gen-frame-{name}-encode", "kind": "frame-encode",
                    "clauses": clause_list, "bytes": octets.hex(), "frame": frame,
                    "note": f"{note}; the write direction, where SIZE is computed rather "
                            f"than carried"})


def frame_reject(vectors: list[dict], name: str, octets: bytes, reason: str, note: str,
                 clauses: list[str] | None = None) -> None:
    vectors.append({
        "vector": f"gen-frame-{name}", "kind": "frame-reject",
        "clauses": clauses if clauses is not None else [FRAMING_CLAUSE],
        "bytes": octets.hex(),
        "expectError": {"condition": "amqp:connection:framing-error",
                        "endpoint": "connection", "reason": reason},
        "note": note,
    })


def frame_corpus() -> list[dict]:
    """The frame corpus: every performative in both directions and in the frame type its
    role gives it, the size and DOFF arithmetic at the boundaries, the layout's malformed
    arithmetic, and the mutation controls that require a body to be read rather than
    skipped."""
    types = declared_types()
    vectors: list[dict] = []
    bodies: dict[str, dict] = {}
    for name, _, frame_type in performatives(types):
        bodies[name] = performative_value(types, types[name])
        clauses = [FRAMING_CLAUSE, PERFORMATIVE_CLAUSE]
        if frame_type == SASL_FRAME:
            clauses.append(SASL_CLAUSE)
        role = "SASL" if frame_type == SASL_FRAME else "AMQP"
        frame_pair(vectors, f"performative-{name}", frame_type, FRAME_MIN_DOFF, bodies[name],
                   clauses=clauses,
                   note=f"the {name} performative in a {role} frame, carrying every field "
                        f"the declared surface makes mandatory or gives a default, with the "
                        f"trailing nulls dropped")

    open_body = bodies["open"]
    open_octets = len(encode(open_body))
    limit = int(defined_constant("MIN-MAX-FRAME-SIZE"))
    for label, total in (("at-min-max-frame-size", limit),
                         ("one-over-min-max-frame-size", limit + 1)):
        frame_pair(vectors, f"size-{label}", AMQP_FRAME, FRAME_MIN_DOFF, open_body,
                   payload=b"\x2a" * (total - FRAME_HEADER - open_octets),
                   note=f"a frame of exactly {total} octets: MIN-MAX-FRAME-SIZE is "
                        f"{limit}, the bound the artifact defines and this counts to")
    frame_pair(vectors, "doff-three", AMQP_FRAME, 3, open_body,
               extended=b"\x00" * (3 * FRAME_WORD - FRAME_HEADER),
               note="DOFF of three: four octets of extended header, which an AMQP frame "
                    "ignores rather than refuses")
    largest = (FRAME_HEADER + (3 * FRAME_WORD - FRAME_HEADER) + open_octets) // FRAME_WORD
    frame_pair(vectors, "doff-largest-for-body", AMQP_FRAME, largest, open_body,
               extended=b"\x00" * (largest * FRAME_WORD - FRAME_HEADER),
               note=f"DOFF of {largest}, the largest that still leaves the body inside SIZE "
                    f"for this frame, with the body beginning at the extended header's end")

    good = frame_octets(AMQP_FRAME, FRAME_MIN_DOFF, encode(open_body))
    below = bytearray(good)
    below[3] = FRAME_HEADER + open_octets - 2
    frame_reject(vectors, "size-below-body", bytes(below), "sizeMismatch",
                 "SIZE claims fewer octets than the performative needs")
    inside = bytearray(good)
    inside[4] = FRAME_MIN_DOFF - 1
    frame_reject(vectors, "doff-below-minimum", bytes(inside), "sizeMismatch",
                 "DOFF of one puts the body inside the eight-octet header")
    beyond = bytearray(good)
    beyond[4] = FRAME_MIN_DOFF + 2
    frame_reject(vectors, "doff-beyond-size", bytes(beyond), "sizeMismatch",
                 "DOFF puts the body past the octets SIZE declares")
    unassigned_type = bytearray(good)
    unassigned_type[5] = 0x02
    frame_reject(vectors, "type-unknown", bytes(unassigned_type), "unsupported",
                 "TYPE 0x02 is not a frame type this specification assigns")
    frame_reject(vectors, "header-truncated", bytes(good[:FRAME_HEADER - 1]), "truncated",
                 "seven octets where the header alone needs eight")

    # The mutation controls: a frame layer that skipped the body rather than reading it
    # would accept both of these.
    open_bytes = encode(open_body)
    frame_reject(vectors, "descriptor-unassigned",
                 frame_octets(AMQP_FRAME, FRAME_MIN_DOFF, bytes([0x01]) + open_bytes[1:]),
                 "unassigned",
                 "the performative's descriptor octet replaced by 0x01, which is below "
                 "every format-code range, so refusing this needs the body to be read")
    frame_reject(vectors, "body-not-described",
                 frame_octets(AMQP_FRAME, FRAME_MIN_DOFF, bytes([0x40]) + open_bytes[1:]),
                 "malformed",
                 "the body's first octet replaced by null: still a value, but not the "
                 "described type the layout requires a performative to be")
    return vectors
