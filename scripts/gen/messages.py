"""The message corpus: the Part 3 section types and the delivery states, generated.

    (dispatched from `scripts/gen-value-vectors.py --messages PATH`)

The families here are the ones whose expectations are *closed over the declared surface*
rather than chosen: every descriptor code the types artifact could carry in a section's
position, the payload and item-count boundaries where a section's body changes form, the
annotation keys whose understanding the clause makes a rule, and the delivery states with
the quantities their own texts move. Each is a sweep rather than a sample, so a wrong
boundary is a failing vector rather than a case nobody thought of.

**Where the expectations come from.** The section set, the body shape each declaration
implies, the descriptors and the fields are read from the vendored messaging and types
artifacts (`spec/oasis/`), through the same `ElementTree` reading the other families use.
The octets are written by `gen/values.py`'s `encode`, which is the Part 1 encoder checked
against the artifact's own worked examples. Nothing here runs either Lean artefact: a
vector produced by the thing under test would prove only that it equals itself.

**The readings the family inherits.** The conditions a refusal carries are the ones the
hand-authored corpus pins and the plan records: a structural, arity or declared-type
violation is `amqp:decode-error`, and an annotation key the endpoint does not implement is
`amqp:not-implemented`, because the clause mandates a detach with a family of conditions
rather than with a member of it.
"""

from __future__ import annotations

import pathlib
import sys
from xml.etree import ElementTree

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from gen import values

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
SPEC = ROOT / "spec" / "oasis"
MESSAGING = "amqp-core-messaging-v1.0-os.xml"

MESSAGE_FORMAT = f"{MESSAGING}#amqp:messaging/section:message-format.1"
ANNOTATION_KEYS = f"{MESSAGING}#amqp:messaging/section:message-format/type:annotations.1"
ANNOTATION_UNDERSTOOD = f"{MESSAGING}#amqp:messaging/section:message-format/type:annotations.2"
TERMINAL = f"{MESSAGING}#amqp:messaging/section:delivery-state/doc:more-resuming-deliveries.15"
# The Part 1 type table: which subcategory a form code belongs to and how wide its
# size or count field is, which is what a payload-form boundary is a boundary of.
TYPE_TABLE = "amqp-core-types-v1.0-os.xml#picture.5"

DECODE_ERROR = "amqp:decode-error"
NOT_IMPLEMENTED = "amqp:not-implemented"
ILLEGAL_STATE = "amqp:illegal-state"


def parse(artifact: str) -> ElementTree.Element:
    return ElementTree.parse(SPEC / artifact).getroot()


def descriptor_code(element: ElementTree.Element) -> int:
    """A declaration's descriptor code: the artifact writes it as `domain:code`, and the
    domain is zero for every messaging type."""
    text = element.find("descriptor").get("code")
    domain, _, code = text.partition(":")
    if int(domain, 16) != 0:
        raise ValueError(f"a nonzero descriptor domain {domain} is not a shape this reads")
    return int(code, 16)


class Section:
    """A declared section type: its name, its class, the body shape its declaration fixes,
    its descriptor, and its fields with the ones the artifact makes mandatory."""

    def __init__(self, element: ElementTree.Element) -> None:
        self.name = element.get("name")
        self.klass = element.get("class")
        self.source = element.get("source")
        self.code = descriptor_code(element)
        self.fields = element.findall("field")
        self.mandatory = [f.get("name") for f in self.fields if f.get("mandatory") == "true"]

    @property
    def shape(self) -> str:
        if self.klass == "composite":
            return "fields"
        if self.source == "annotations":
            return "annotations"
        if self.source == "map":
            return "string-keyed map"
        if self.source == "binary":
            return "payload"
        if self.source == "list":
            return "items"
        if self.source == "*":
            return "value"
        raise ValueError(f"{self.name} restricts {self.source}, which this generator has no shape for")


def sections() -> list[Section]:
    """The declared section types, in the order the artifact declares them."""
    return [Section(element) for element in parse(MESSAGING).iter("type")
            if element.get("provides") == "section"]


def by_code() -> dict[int, Section]:
    return {section.code: section for section in sections()}


def body_value(section: Section, shape_body: dict) -> dict:
    """A section's body as a corpus value, in the form its shape gives it."""
    if section.shape in ("fields", "items"):
        return {"type": "list", "items": shape_body["items"]}
    if section.shape in ("annotations", "string-keyed map"):
        return {"type": "map", "pairs": shape_body["pairs"]}
    if section.shape == "payload":
        return {"type": "binary", "hex": shape_body["hex"]}
    return shape_body["value"]


def section_json(section: Section, shape_body: dict) -> dict:
    """A section in the corpus's vocabulary."""
    body = body_value(section, shape_body)
    out = {"kind": section.name}
    if section.shape == "fields":
        out["fields"] = body["items"]
    elif section.shape == "items":
        out["items"] = body["items"]
    elif section.shape in ("annotations", "string-keyed map"):
        out["pairs"] = body["pairs"]
    elif section.shape == "payload":
        out["payload"] = body["hex"]
    else:
        out["value"] = body
    return out


def octets(section: Section, shape_body: dict) -> bytes:
    return values.encode({
        "type": "described",
        "descriptor": {"type": "ulong", "value": section.code},
        "value": body_value(section, shape_body),
    })


def empty_body(section: Section) -> dict:
    """The smallest body the declaration admits, in the shape it fixes: an empty list for a
    composite, an empty map for a map, a zero-octet payload for a binary, and null for a
    wildcard — the wildcard has no empty form, so its smallest body is the null value."""
    if section.shape in ("fields", "items"):
        return {"items": []}
    if section.shape in ("annotations", "string-keyed map"):
        return {"pairs": []}
    if section.shape == "payload":
        return {"hex": ""}
    return {"value": {"type": "null"}}


def note_octets(octets_bytes: bytes, limit: int = 40) -> str:
    """The octets of a vector as the note quotes them, abbreviated where a payload is long
    enough that quoting it would be noise rather than evidence."""
    shown = " ".join(f"{byte:02x}" for byte in octets_bytes[:limit])
    if len(octets_bytes) > limit:
        return f"{shown} … ({len(octets_bytes)} octets)"
    return shown


def descriptor_sweep() -> list[dict]:
    """Every descriptor code a described value could carry in a section's position, with the
    smallest body the declaration admits where the code names a section type and an empty
    list where it does not.

    The domain is closed: 256 codes, and the expectation for each is decided by the declared
    surface rather than by a reading. A code that names a section type whose declaration has
    a mandatory field is refused even with the smallest body, because the mandatory prefix is
    what the declaration requires; every other code that names a section type is admitted as
    that section; and a code that names nothing, or names a type that provides no section
    role, is refused.
    """
    declared = by_code()
    out: list[dict] = []
    for code in range(256):
        section = declared.get(code)
        if section is None:
            empty = {"type": "described", "descriptor": {"type": "ulong", "value": code},
                     "value": {"type": "list", "items": []}}
            payload = values.encode(empty)
            out.append({
                "vector": f"gen-section-descriptor-{code:02x}-undeclared",
                "kind": "section-reject",
                "clauses": [MESSAGE_FORMAT],
                "note": f"Descriptor {code} (0x{code:02x}) names no type the declared surface "
                        f"carries, so a described value carrying it is not a message section. "
                        f"The octets are {note_octets(payload)}: the descriptor, then the "
                        f"smallest list. The sweep is closed over the descriptor space, so a "
                        f"code the artifact starts carrying changes this vector's expectation "
                        f"rather than being a case nobody listed.",
                "bytes": payload.hex(),
                "expectError": {"condition": DECODE_ERROR, "reason": "malformed"},
            })
        else:
            body = empty_body(section)
            payload = octets(section, body)
            name = f"gen-section-descriptor-{code:02x}-{section.name}"
            if section.mandatory:
                out.append({
                    "vector": name,
                    "kind": "section-reject",
                    "clauses": [MESSAGE_FORMAT],
                    "note": f"Descriptor {code} names {section.name}, whose declaration makes "
                            f"{', '.join(section.mandatory)} mandatory, and the body carries "
                            f"none of them: the mandatory prefix is exactly what a decoder must "
                            f"see, so the smallest body the shape admits is not a "
                            f"{section.name} section. Octets: {note_octets(payload)}.",
                    "bytes": payload.hex(),
                    "expectError": {"condition": DECODE_ERROR, "reason": "malformed"},
                })
            else:
                out.append({
                    "vector": name,
                    "kind": "section-decode",
                    "clauses": [MESSAGE_FORMAT],
                    "note": f"Descriptor {code} names {section.name}, a {section.shape} section, "
                            f"and its smallest body is the empty one: the declared surface "
                            f"gives this type the section role, so a described value of it is a "
                            f"message section of that type. Octets: {note_octets(payload)}, "
                            f"which are also the canonical form the writer must produce.",
                    "bytes": payload.hex(),
                    "section": section_json(section, body),
                    "canonical": True,
                })
    return out


def payload_boundaries() -> list[dict]:
    """A `data` section's payload at every length where its encoding changes form: the
    eight-bit variable form holds up to 255 octets, and one more needs the thirty-two-bit
    form. The lengths below the boundary are the ones a reader could get wrong by writing a
    wide form early or a narrow form late, so each is a vector rather than one at the edge.
    """
    section = by_code()[0x75]
    out: list[dict] = []
    for length in (0, 1, 254, 255, 256):
        payload = b"\xab" * length
        body = {"hex": payload.hex()}
        octets_bytes = octets(section, body)
        wide = "the thirty-two-bit variable form" if length > 255 else "the eight-bit variable form"
        out.append({
            "vector": f"gen-data-payload-{length}",
            "kind": "section-decode",
            "clauses": [MESSAGE_FORMAT, TYPE_TABLE],
            "note": f"A data section carrying {length} octet(s), which the declared surface "
                    f"writes in {wide}: the boundary is 255, where the one-octet length field "
                    f"stops being able to announce the payload. Octets: "
                    f"{note_octets(octets_bytes)}.",
            "bytes": octets_bytes.hex(),
            "section": section_json(section, body),
            "canonical": True,
        })
    return out


def item_boundaries() -> list[dict]:
    """An `amqp-sequence` section's item count at every length where its encoding changes
    form. The bound is the *size* field rather than the count: a one-octet count plus the
    items must fit in the one-octet size, so 254 nulls still fit in the narrow form and 255
    do not.
    """
    section = by_code()[0x76]
    out: list[dict] = []
    for count in (0, 1, 127, 128, 254, 255, 256):
        items = [{"type": "null"} for _ in range(count)]
        body = {"items": items}
        octets_bytes = octets(section, body)
        narrow = len(octets_bytes) < 8 or octets_bytes[0] == 0xC0
        out.append({
            "vector": f"gen-sequence-items-{count}",
            "kind": "section-decode",
            "clauses": [MESSAGE_FORMAT, TYPE_TABLE],
            "note": f"An amqp-sequence section carrying {count} null element(s): each takes one "
                    f"octet, so the size field is 1 + {count} and the form is "
                    f"{'list8' if narrow else 'list32'}. The boundary is where the size stops "
                    f"fitting in one octet, which is a bound a reader that counted elements "
                    f"instead of octets would place at 255. Octets: "
                    f"{note_octets(octets_bytes)}.",
            "bytes": octets_bytes.hex(),
            "section": section_json(section, body),
            "canonical": True,
        })
    return out


def annotation_keys() -> list[dict]:
    """The annotation key rules, over the three sections whose keys are symbols or ulongs and
    over `application-properties`, whose keys are strings.

    The clause has two sides and both are swept: a key beginning with `x-opt` may be ignored,
    and any other key the endpoint does not implement is a detach. The keys that matter are
    the boundary of the prefix itself (`x-opt` with nothing after it, and a key one character
    short of it), the ulong keys the reserved space is made of, and a policy that names a key
    the empty policy refuses.
    """
    declared = by_code()
    out: list[dict] = []

    def annotation_vector(name: str, section: Section, key: dict, expect_policy: list[str] | None,
                          admitted: bool, why: str) -> dict:
        body = {"pairs": [[key, {"type": "string", "text": "v"}]]}
        octets_bytes = octets(section, body)
        vector = {
            "vector": name,
            "clauses": [ANNOTATION_KEYS, ANNOTATION_UNDERSTOOD],
            "note": why + f" Octets: {note_octets(octets_bytes)}.",
            "bytes": octets_bytes.hex(),
        }
        if expect_policy is not None:
            vector["policy"] = {"understood": expect_policy}
        if admitted:
            vector["kind"] = "section-decode"
            vector["section"] = section_json(section, body)
            vector["canonical"] = True
        else:
            vector["kind"] = "section-reject"
            vector["expectError"] = {"condition": NOT_IMPLEMENTED, "reason": "unsupported",
                                     "endpoint": "link"}
        return vector

    for section in (declared[0x71], declared[0x72], declared[0x78]):
        short = section.name.replace("-", "")
        cases = [
            (f"gen-{short}-key-x-opt-bare", {"type": "symbol", "text": "x-opt"}, None, True,
             "The symbolic key x-opt is the prefix itself with nothing after it: the clause "
             "makes keys *beginning with* x-opt the ones a receiver may ignore, so the bare "
             "prefix is one of them."),
            (f"gen-{short}-key-x-opt-one", {"type": "symbol", "text": "x-opt-1"}, None, True,
             "A one-character symbolic key after the x-opt prefix: the shortest key that is "
             "not the bare prefix."),
            (f"gen-{short}-key-x-o-short", {"type": "symbol", "text": "x-op"}, None, False,
             "A key one character short of the x-opt prefix: it is a reserved symbolic key "
             "the endpoint does not implement, so the clause's detach applies — the prefix "
             "test is a prefix, not a substring."),
            (f"gen-{short}-key-reserved-symbol", {"type": "symbol", "text": "reserved"}, None,
             False, "A reserved symbolic key the endpoint does not implement, which is the "
                    "case the clause makes a detach."),
            (f"gen-{short}-key-reserved-symbol-implemented",
             {"type": "symbol", "text": "reserved"}, ["reserved"], True,
             "The same reserved symbolic key with a policy that implements it: the detach is "
             "for keys the receiver does not understand, and this endpoint does."),
            (f"gen-{short}-key-ulong-zero", {"type": "ulong", "value": 0}, None, False,
             "ulong keys are all reserved, and this endpoint implements none of them."),
            (f"gen-{short}-key-ulong-255", {"type": "ulong", "value": 255}, ["255"], True,
             "A one-octet ulong key, implemented by the policy: the boundary on the ulong's "
             "own narrowest form, which is what a policy that keyed on the encoded form "
             "rather than the value would get wrong."),
            (f"gen-{short}-key-ulong-256", {"type": "ulong", "value": 256}, ["256"], True,
             "A two-octet ulong key, implemented by the policy: one past the one-octet form, "
             "so the vector distinguishes the value the policy names from the octets it "
             "arrives in."),
        ]
        for name, key, policy, admitted, why in cases:
            out.append(annotation_vector(name, section, key, policy, admitted, why))

    properties = declared[0x74]
    for name, key, admitted, why in (
        ("gen-applicationproperties-key-string", {"type": "string", "text": "k"}, True,
         "An application-properties key is a string, which is the shape its own text gives "
         "the section rather than an annotation rule: this section's keys are not in the "
         "reserved symbolic space at all."),
        ("gen-applicationproperties-key-symbol", {"type": "symbol", "text": "k"}, False,
         "An application-properties key that is a symbol where the section's text requires a "
         "string: the section is well formed as a map and wrong as this type."),
    ):
        body = {"pairs": [[key, {"type": "string", "text": "v"}]]}
        octets_bytes = octets(properties, body)
        vector = {
            "vector": name,
            "clauses": [MESSAGE_FORMAT],
            "note": why + f" Octets: {note_octets(octets_bytes)}.",
            "bytes": octets_bytes.hex(),
        }
        if admitted:
            vector.update({"kind": "section-decode",
                           "section": section_json(properties, body), "canonical": True})
        else:
            vector.update({"kind": "section-reject",
                           "expectError": {"condition": DECODE_ERROR, "reason": "malformed"}})
        out.append(vector)
    return out


def received_state(section_number: int, section_offset: int) -> dict:
    return {"type": "described", "descriptor": {"type": "ulong", "value": 35},
            "value": {"type": "list", "items": [{"type": "uint", "value": section_number},
                                                {"type": "ulong", "value": section_offset}]}}


def outcome_state(code: int, items: list[dict]) -> dict:
    return {"type": "described", "descriptor": {"type": "ulong", "value": code},
            "value": {"type": "list", "items": items}}


def delivery_step(state: dict, settled: bool, expect: dict) -> dict:
    return {"apply": state, "settled": settled, "expect": expect}


def delivery_states() -> list[dict]:
    """The five delivery states the messaging layer defines, each applied to a delivery with
    no state, then each of the terminal ones applied twice.

    The observables are the ones the states' own texts move: the delivery-count (rejected
    increments it, modified increments it exactly when delivery-failed is set, released and
    accepted do not), the redelivery flag (released leaves the message available, accepted
    retires it, modified says so by undeliverable-here), and the resume point, which only a
    received state reports.
    """
    out: list[dict] = []
    admitted = {
        "received": (received_state(0, 0), {"state": "delivery:RECEIVED", "delivery-count": 0,
                                           "redelivery-allowed": True, "section-number": 0,
                                           "section-offset": 0}),
        "accepted": (outcome_state(36, []), {"state": "delivery:ACCEPTED", "delivery-count": 0,
                                             "redelivery-allowed": False}),
        "rejected": (outcome_state(37, []), {"state": "delivery:REJECTED", "delivery-count": 1,
                                             "redelivery-allowed": False}),
        "released": (outcome_state(38, []), {"state": "delivery:RELEASED", "delivery-count": 0,
                                             "redelivery-allowed": True}),
        "modified delivery-failed": (
            outcome_state(39, [{"type": "boolean", "value": True}]),
            {"state": "delivery:MODIFIED", "delivery-count": 1, "redelivery-allowed": True}),
        "modified undeliverable-here": (
            outcome_state(39, [{"type": "null"}, {"type": "boolean", "value": True}]),
            {"state": "delivery:MODIFIED", "delivery-count": 0, "redelivery-allowed": False}),
        "modified both": (
            outcome_state(39, [{"type": "boolean", "value": True},
                               {"type": "boolean", "value": True}]),
            {"state": "delivery:MODIFIED", "delivery-count": 1, "redelivery-allowed": False}),
    }
    for name, (state, expectation) in admitted.items():
        out.append({
            "vector": f"gen-delivery-{name.replace(' ', '-')}",
            "kind": "delivery",
            "clauses": [TERMINAL],
            "note": f"A delivery with no recorded state has {name} applied. The count and the "
                    f"redelivery flag are the quantities the state's own text moves: rejected "
                    f"and modified-with-delivery-failed count the attempt, released and "
                    f"accepted do not, accepted retires the message, and modified says whether "
                    f"the message may come back to this link by undeliverable-here.",
            "start": "delivery:UNSETTLED",
            "steps": [delivery_step(state, True, {"status": "admitted", **expectation})],
        })

    out.append({
        "vector": "gen-delivery-settled-not-unsettled",
        "kind": "delivery",
        "clauses": [TERMINAL],
        "note": "Two states for one delivery, the first carrying the settled flag and the "
                "second not. The reading is that settlement is absorbing: settling a "
                "delivery causes the endpoint to remove its delivery-tag from the unsettled "
                "map, and that map is the record of *unsettled* deliveries, so a later "
                "disposition cannot put the entry back. The vector exists because the two "
                "readings — absorbing, and the step's own flag overwriting what was carried "
                "— differ only here, and a corpus without it cannot tell them apart.",
        "start": "delivery:UNSETTLED",
        "steps": [
            delivery_step(received_state(0, 0), True,
                          {"status": "admitted", "state": "delivery:RECEIVED",
                           "settled": True, "delivery-count": 0, "redelivery-allowed": True,
                           "section-number": 0, "section-offset": 0}),
            delivery_step(received_state(1, 5), False,
                          {"status": "admitted", "state": "delivery:RECEIVED",
                           "settled": True, "delivery-count": 0, "redelivery-allowed": True,
                           "section-number": 1, "section-offset": 5}),
        ],
    })

    for number in (0, 255, 256, 4294967295):
        for offset in (0, 255, 256):
            if (number, offset) not in ((0, 0),):
                out.append({
                    "vector": f"gen-delivery-received-{number}-{offset}",
                    "kind": "delivery",
                    "clauses": [TERMINAL],
                    "note": f"A received state at section-number {number} and section-offset "
                            f"{offset}: the two mandatory fields of received, each written in "
                            f"the narrowest form its declared type allows, so the vector "
                            f"distinguishes a reader that decodes the field's value from one "
                            f"that only accepts one width.",
                    "start": "delivery:UNSETTLED",
                    "steps": [delivery_step(
                        received_state(number, offset), False,
                        {"status": "admitted", "state": "delivery:RECEIVED",
                         "delivery-count": 0, "redelivery-allowed": True,
                         "section-number": number, "section-offset": offset})],
                })

    for key, label, state in (
            ("accepted", "accepted", outcome_state(36, [])),
            ("rejected", "rejected", outcome_state(37, [])),
            ("released", "released", outcome_state(38, [])),
            ("modified delivery-failed", "modified", outcome_state(
                39, [{"type": "boolean", "value": True}]))):
        first = admitted[key][1]
        out.append({
            "vector": f"gen-delivery-terminal-{label}-then-released",
            "kind": "delivery",
            "clauses": [TERMINAL],
            "note": f"A terminal state ({label}) followed by a second state: the delivery-state "
                    f"section's own words are that once a delivery reaches a terminal delivery "
                    f"state the state for that delivery will no longer change, so the second "
                    f"step is refused with the shared condition for what the current state does "
                    f"not permit, and the delivery keeps the count and flag the first step set.",
            "start": "delivery:UNSETTLED",
            "steps": [
                delivery_step(state, True, {"status": "admitted", **first}),
                delivery_step(outcome_state(38, []), True,
                              {"status": "refused", "condition": ILLEGAL_STATE,
                               "reason": "illegalState", "state": first["state"],
                               "delivery-count": first["delivery-count"],
                               "redelivery-allowed": first["redelivery-allowed"]}),
            ],
        })
    return out


def corpus() -> list[dict]:
    vectors = descriptor_sweep() + payload_boundaries() + item_boundaries()
    vectors += annotation_keys() + delivery_states()
    names = [vector["vector"] for vector in vectors]
    if len(set(names)) != len(names):
        raise ValueError("two vectors share an id, which the corpus does not allow")
    return vectors


def self_check() -> None:
    """The generator's own control: the section set it reads is the nine the messaging
    artifact declares, with the descriptors the artifact gives them. A changed artifact
    changes this check before it changes a vector."""
    found = {section.name: section for section in sections()}
    expected = {"header": 112, "delivery-annotations": 113, "message-annotations": 114,
                "properties": 115, "application-properties": 116, "data": 117,
                "amqp-sequence": 118, "amqp-value": 119, "footer": 120}
    if {name: section.code for name, section in found.items()} != expected:
        raise ValueError(f"the declared section set changed: {sorted(found)}")
    if found["received" if "received" in found else "header"].mandatory:
        raise ValueError("the header declaration has no mandatory field; this check is stale")
