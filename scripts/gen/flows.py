"""The fragmentation adequacy control: one message, at every split point the artifact permits.

    (dispatched from `scripts/gen-value-vectors.py --flow PATH --flow-negative PATH`)

The slot asks for "a vector family that fragments the same message at different permitted
split points is admitted", and this is that family. It exists because fragmentation is the
one rule in the link layer whose whole content is latitude about framing: the artifact says a
message MAY be split, so a corpus that carries one framing per message — as every other
family here does — cannot tell a peer that reassembles the octets from one that reads a
single-frame message and happens to accept a two-frame one. The control is the sweep: one
message, every interior octet boundary, each boundary a vector of its own.

**The rule.** `amqp:transport/section:links.29`: *"For messages that are too large to fit
within the maximum frame size, additional data MAY be transferred in additional «transfer»
frames by setting the more flag on all but the last «transfer» frame."* Read as the split
points it permits, that sentence admits every boundary *inside* the message: nothing in the
artifact constrains a split to a section boundary, a field boundary or any other element
boundary, because what the receiver has is the octets it reassembles and what the message
layer reads is what those octets mean. The two framings the clause's own words tie it to are
the two negatives: a frame over the maximum frame size it names as the reason to split, and a
delivery that does not end — `more` on every frame, including the last.

**Where the message's octets come from.** Nowhere here. They are written by
`gen/messages.py`'s declared-shape reading of the messaging artifact and `gen/values.py`'s
Part 1 encoder: the section descriptors are the artifact's and the length prefixes and the
value's form are the types grammar's. The message is two sections — `data`, then `amqp-value`
carrying the same text as a `string` — so the sweep crosses two descriptor prefixes, two
length fields and the value's own encoding rather than repeating one shape's boundary. A
changed descriptor or a changed length rule moves the octets before it moves an expectation,
which is the property the S5 corpus has and this family inherits.

**Who reads them.** Every step in the family is a `receive` step: the octets are the vector's
and the reader is the artefact — the same two readers the message differential runs, over
octets neither of them wrote. A `send` step would have the artefact write the fragmentation,
and the family would then be checking the writer against itself. Both artefacts run this
corpus under the exchange contract, so each split point is admitted by two independent
readers or the family fails.

**What the sweep does not claim.** `links.31` ("messages transferred along a single link MUST
NOT be interleaved") and the three first-field equality sentences (`delivery-id.u1`,
`delivery-tag.u1`, `message-format.u1`: "It is an error if X on a continuation transfer
differs from X on the first transfer of a delivery") are *not* exercised here and cannot be:
the session model keeps no first transfer's tag, no delivery-id of its own and no
per-delivery framing, so an interleaved or re-tagged continuation is admitted by both
artefacts and a vector asserting a refusal would fail. They are reported as the plan
questions they are — each needs a field the model does not have — rather than weakened into a
vector that asserts whatever the model happens to do.
"""

from __future__ import annotations

import pathlib
import sys

# The families are a package beside this script; the entry points say why this is stated
# rather than assumed.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from gen import messages, slices

TRANSPORT = slices.TRANSPORT
TYPES = "amqp-core-types-v1.0-os.xml"

# -- the clauses the family is authored from --------------------------------- #

# The rule, and the sentence about the flag that is its instrument.
SPLIT_POINTS = f"{TRANSPORT}#amqp:transport/section:links.29"
NO_INTERLEAVING = f"{TRANSPORT}#amqp:transport/section:links.31"
ABORTED_TAKES_PRECEDENCE = (
    f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:more.1")
MORE_WITH_ABORTED = (
    f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:more.2")
ABORTED_DISCARDS = (
    f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:aborted.2")
# The three fields a first transfer must carry, which is what makes the end of a delivery
# observable: a transfer offered after the message ended has none of them to carry.
TRANSFER_FIELD_ANCHOR = f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer/field:"
FIRST_TRANSFER_FIELDS = [
    f"{TRANSFER_FIELD_ANCHOR}{field}.1"
    for field in ("delivery-id", "delivery-tag", "message-format")]
# The unkeyed sentence each of those three fields states its *continuation* rule with — "It is
# an error if the delivery-tag on a continuation transfer differs from the delivery-tag on the
# first transfer of a delivery" — which is the rule the family's three difference negatives
# carry, and which neither artefact enforced before them. The `.u1` index is the ledger's: the
# sentence carries no RFC 2119 keyword, so its disposition keys on the unkeyed form.
CONTINUATION_IDENTITY = {
    field: f"{TRANSFER_FIELD_ANCHOR}{field}.u1"
    for field in ("delivery-id", "delivery-tag", "message-format")}
# The value each difference negative gives the field it contradicts. The values the first
# transfer carries are `fragment_body`'s — delivery-id 0, delivery-tag `b"tag"`, message-format
# 0 — so each of these differs from the value it is compared against, and `self_check` says so
# rather than this comment.
DIFFERING_CONTINUATIONS = (
    ("delivery-id", {"type": "uint", "value": 1}),
    ("delivery-tag", {"type": "binary", "hex": b"elsewhere".hex()}),
    ("message-format", {"type": "uint", "value": 1}))
TRANSFER_CARRIES_A_MESSAGE = (
    f"{TRANSPORT}#amqp:transport/section:performatives/type:transfer.1")
# The size the split rule defers to, in both halves: the field that declares it and the
# sentence that makes a frame over it a connection error.
MAX_FRAME_SIZE = (
    f"{TRANSPORT}#amqp:transport/section:performatives/type:open/field:max-frame-size.1")
OVERSIZED_FRAME = (
    f"{TRANSPORT}#amqp:transport/section:performatives/type:open/field:max-frame-size.2")
PRE_NEGOTIATION_LIMITS = f"{TRANSPORT}#amqp:transport/section:connections.1"
# Part 3's section framing, which is what makes the octets a message rather than a payload.
SECTION_FRAMING = "amqp-core-messaging-v1.0-os.xml#amqp:messaging/section:message-format.1"
# Part 1's type table, where the length prefixes and the value's form come from.
TYPE_TABLE = f"{TYPES}#picture.5"

# The message the sweep fragments. Short on purpose: the split points are the vector's
# business, and a family whose every vector carries a kilobyte of text is a family nobody
# reads.
SWEPT_TEXT = "fragmented"
# The sentence the frame-size negative's message is grown from, in whole repetitions, until
# the message is long enough for a split whose first frame leaves the announced limit. The
# length is computed from the limit rather than chosen; see `oversized_message`.
OVERSIZED_SENTENCE = "a message does not have to fit in one frame, "


def section_named(name: str) -> messages.Section:
    """A declared section type, read from the messaging artifact rather than named by its
    descriptor code: a family that typed the code would survive the artifact changing it."""
    found = [section for section in messages.sections() if section.name == name]
    if len(found) != 1:
        raise SystemExit(f"the messaging artifact declares {len(found)} {name} sections")
    return found[0]


def declared_message(text: str) -> bytes:
    """One message in the octets the declared tables write: a `data` section carrying
    `text` as octets, then an `amqp-value` section carrying the same text as a `string`.

    The descriptors come from the messaging artifact and the length prefixes and the
    `string`'s form from the types grammar, through `gen/messages.py` and `gen/values.py` —
    the same derivation the S5 corpus uses. So the message is two sections, and the sweep
    crosses both of their framings: a peer that reassembled octets only at a section
    boundary would pass a family that split at boundaries and fail this one.
    """
    payload = text.encode("utf-8")
    first = messages.octets(section_named("data"), {"hex": payload.hex()})
    second = messages.octets(section_named("amqp-value"),
                             {"value": {"type": "string", "text": text}})
    return first + second


def fragments(tables: slices.Corpus, octets: bytes, splits: tuple[int, ...],
              delivery_id: int = 0) -> list[dict]:
    """One delivery in `len(splits) + 1` transfers, cut at the given octet offsets.

    `more` is set on every transfer but the last, and the first transfer carries the three
    fields `delivery-id.1`, `delivery-tag.1` and `message-format.1` require of it: that is
    the framing `links.29` describes. The chunks are the message's own octets, and
    `self_check` rebuilds the message from them, so no vector can silently fragment
    something other than the message the family names.
    """
    if list(splits) != sorted(splits) or any(k <= 0 or k >= len(octets) for k in splits):
        raise SystemExit(f"a split point outside the message: {splits} of {len(octets)}")
    bounds = (0,) + tuple(splits) + (len(octets),)
    count = len(bounds) - 1
    return [tables.receive_frame(
        slices.AMQP_FRAME, tables.fragment_body(index, count, delivery_id=delivery_id),
        state=slices.s("MAPPED"), channel=1,
        payload=octets[bounds[index]:bounds[index + 1]])
        for index in range(count)]


def link_up(tables: slices.Corpus, peer_handle: int = 0) -> list[dict]:
    """The three steps that attach a link on a MAPPED session with the peer as the sender,
    which is the direction this family reads: our attach, the peer's attach, and the peer's
    flow.

    The receiver's direction is the one that can carry the octets as the vector wrote them.
    A `send` step would have the artefact write the fragmentation, and the family would then
    be checking a writer against itself rather than a reader against octets it did not
    write. Every state is pinned, so a setup step that drifted under a rule the family is
    not about would fail here rather than silently re-frame the question.
    """
    return [tables.send_frame(slices.AMQP_FRAME, tables.attach_body(role=True),
                              state=slices.s("MAPPED"), channel=1),
            tables.receive_frame(slices.AMQP_FRAME,
                                 tables.attach_body(role=False, handle=peer_handle),
                                 state=slices.s("MAPPED"), channel=1),
            tables.receive_frame(slices.AMQP_FRAME,
                                 tables.flow_body(handle=peer_handle, delivery_count=0,
                                                  link_credit=0),
                                 state=slices.s("MAPPED"), channel=1)]


def exchange(vector: str, *, start: str, steps: list[dict], clauses: list[str],
             note: str) -> dict:
    return {"vector": vector, "kind": "exchange", "clauses": clauses, "start": start,
            "steps": steps, "note": note}


# -- the family -------------------------------------------------------------- #

def flow_corpus(tables: slices.Corpus) -> list[dict]:
    """The adequacy control: one message, every interior split point, all admitted.

    A message of `N` octets has `N - 1` interior boundaries and each is one vector: the
    delivery is two transfers cut there. The one-transfer framing is the baseline every
    other corpus here carries, and the three-transfer vectors are the composition check — a
    boundary pair rather than a single boundary — so a peer that reassembled exactly two
    chunks passes the sweep and fails there.
    """
    octets = declared_message(SWEPT_TEXT)
    count = len(octets)
    clauses = [SPLIT_POINTS, NO_INTERLEAVING, TRANSFER_CARRIES_A_MESSAGE, SECTION_FRAMING,
               TYPE_TABLE] + FIRST_TRANSFER_FIELDS
    vectors: list[dict] = []

    vectors.append(exchange(
        "flow-fragment-whole-message", start=slices.s("MAPPED"), clauses=clauses,
        steps=link_up(tables) + fragments(tables, octets, ()),
        note=f"the baseline: the {count}-octet message in one transfer, with `more` unset "
             f"because there is nothing more. Octets: {messages.note_octets(octets)}. Every "
             f"other vector in this family carries the same octets cut somewhere else, so a "
             f"refusal here and an admission there would make the difference the framing "
             f"rather than the message"))

    for split in range(1, count):
        vectors.append(exchange(
            f"flow-fragment-split-{split}", start=slices.s("MAPPED"), clauses=clauses,
            steps=link_up(tables) + fragments(tables, octets, (split,)),
            note=f"the same {count}-octet message in two transfers, cut at octet {split}: "
                 f"the first carries {split} octet(s) with `more` set and the second the "
                 f"remaining {count - split}. Nothing in the artifact constrains where a "
                 f"split may fall — not a section boundary, not a field boundary, not a "
                 f"boundary of the value the second section carries — so a receiver works "
                 f"from the octets it reassembles rather than from the framing they arrived "
                 f"in"))

    for first, second in ((1, 2), (count // 2, count // 2 + 1), (count - 2, count - 1)):
        vectors.append(exchange(
            f"flow-fragment-three-transfers-{first}-{second}", start=slices.s("MAPPED"),
            clauses=clauses, steps=link_up(tables) + fragments(tables, octets, (first, second)),
            note=f"the same message in three transfers, cut at octets {first} and {second}: "
                 f"the sweep above fixes one boundary at a time and this is the composition, "
                 f"so a peer that reassembled exactly two chunks would pass every vector "
                 f"above and fail this one"))

    # A continuation that repeats the first transfer's fields. `delivery-tag.1` and its two
    # siblings make those fields required on the first transfer and *omissible* on a
    # continuation; the error the artifact names is a continuation that *differs*. So this
    # framing is admitted, and carrying the vector is what keeps the negative corpus's five
    # refusals from reading as a rule that a continuation must not repeat the fields: the
    # difference negatives refuse a *different* value, and this one is the same values again.
    cut = count // 2
    repeated = tables.body("transfer", handle={"type": "uint", "value": 0},
                           **{"delivery-id": {"type": "uint", "value": 0},
                              "delivery-tag": {"type": "binary", "hex": b"tag".hex()},
                              "message-format": {"type": "uint", "value": 0}})
    vectors.append(exchange(
        "flow-fragment-continuation-repeats-the-first-fields", start=slices.s("MAPPED"),
        clauses=clauses,
        steps=link_up(tables) + [
            tables.receive_frame(slices.AMQP_FRAME, tables.fragment_body(0, 2),
                                 state=slices.s("MAPPED"), channel=1,
                                 payload=octets[:cut]),
            tables.receive_frame(slices.AMQP_FRAME, repeated, state=slices.s("MAPPED"),
                                 channel=1, payload=octets[cut:])],
        note="a continuation that carries delivery-id, delivery-tag and message-format "
             "again: the three clauses make those fields required on the first transfer and "
             "omissible on a continuation, and the error they name is a continuation whose "
             "value *differs* from the first transfer's — so a sender that repeats them is "
             "admitted. The negative corpus's two split-point refusals are then about the "
             "split points, and its three difference refusals are about a *different* value, "
             "not about the fields a continuation repeats"))

    return vectors


def continuation_difference(tables: slices.Corpus) -> list[dict]:
    """The three difference negatives' pieces, one entry per field: the legitimate framing's two
    bodies and steps, and the body of the continuation that contradicts the first of them.

    One function for the family and for `self_check`, so the control reads the bodies the vectors
    are made of rather than a second copy of them: `first` and `middle` are what the two framing
    steps carry, and `body` is what the refusing step carries.
    """
    octets = declared_message(SWEPT_TEXT)
    count = len(octets)
    first_cut, second_cut = count // 3, (2 * count) // 3
    # Two transfers of a three-transfer framing, `more` set on both so the delivery is still in
    # progress when the third arrives. The second is a continuation, and `fragment_body` writes a
    # continuation carrying none of the three fields, which is what one is allowed to do.
    first, middle = tables.fragment_body(0, 3), tables.fragment_body(1, 3)
    framing = [tables.receive_frame(slices.AMQP_FRAME, body, state=slices.s("MAPPED"), channel=1,
                                    payload=octets[start:end])
               for body, start, end in ((first, 0, first_cut), (middle, first_cut, second_cut))]
    return [{"field": field, "first": first, "middle": middle, "framing": framing,
             "payload": octets[second_cut:],
             "body": tables.body("transfer", handle={"type": "uint", "value": 0},
                                 **{"more": {"type": "boolean", "value": True},
                                    field: differing})}
            for field, differing in DIFFERING_CONTINUATIONS]


def declared_item(tables: slices.Corpus, body: dict, type_name: str, field: str) -> dict:
    """One field's value in a described field list, positioned by the declared order.

    `Corpus.body` writes the fields in that order and `described` drops the trailing nulls, so
    an index past the list is the null the shorter list means.
    """
    index = tables.fields[type_name].index(field)
    items = body["value"]["items"]
    return items[index] if index < len(items) else {"type": "null"}


def differing_continuation_negatives(tables: slices.Corpus) -> list[dict]:
    """The three fields `delivery-id.u1`, `delivery-tag.u1` and `message-format.u1` make an
    error to *contradict* on a continuation transfer, one vector each.

    Each vector is a three-transfer framing of the swept message. The first transfer carries the
    three fields, as the first transfer of a delivery must; the second *omits* all three, which
    the same field's first sentence permits on a continuation; and the third carries one field
    again with a different value from the first transfer's. So the omission is observed admitted
    in the same run as the contradiction is refused, and the refusal can only be about the
    difference — a rule that refused a continuation for omitting the fields, or for carrying
    them at all, would fail this vector at the step above rather than at the one that refuses.
    `flow-fragment-continuation-repeats-the-first-fields` is the other side of that contrast: a
    continuation carrying all three fields *unchanged* stays admitted.

    Three vectors rather than one because a refusal leaves the session in `DISCARDING` and one
    framing cannot observe three refusals; a family that tested only the tag would leave
    `delivery-id.u1` and `message-format.u1` with no carrier in either artefact.
    """
    vectors: list[dict] = []
    for entry in continuation_difference(tables):
        field = entry["field"]
        vectors.append(exchange(
            f"flow-negative-continuation-{field}-differs", start=slices.s("MAPPED"),
            clauses=[SPLIT_POINTS, TRANSFER_CARRIES_A_MESSAGE,
                     f"{TRANSFER_FIELD_ANCHOR}{field}.1", CONTINUATION_IDENTITY[field]],
            steps=link_up(tables) + entry["framing"] + [
                tables.refused(
                    "receive", reason="malformed", condition=slices.INVALID_FIELD,
                    state=slices.s("DISCARDING"), body=entry["body"], channel=1,
                    payload=entry["payload"],
                    note=f"the third transfer of this delivery carries {field} again, with a "
                         f"value the first transfer's does not have: `{field}.u1` says \"It is "
                         f"an error if the {field} on a continuation transfer differs from the "
                         f"{field} on the first transfer of a delivery\"")],
            note=f"a legitimate two-transfer framing of the message, followed by a continuation "
                 f"whose {field} contradicts the first transfer's. The step above shows the same "
                 f"framing admitted with the field omitted (`{field}.1` lets a continuation omit "
                 f"it); carrying a *different* value is the error, and both artefacts must refuse "
                 f"it with {slices.INVALID_FIELD} and the malformed class"))
    return vectors


def flow_negative_corpus(tables: slices.Corpus) -> list[dict]:
    """The framings the artifact does not permit: the two directions `links.29` names — a
    delivery that does not end, and a frame over the size the clause defers to — and the
    continuation whose `delivery-id`, `delivery-tag` or `message-format` contradicts the first
    transfer's, which `.u1` makes an error and no artefact enforced before this family."""

    octets = declared_message(SWEPT_TEXT)
    count = len(octets)
    vectors: list[dict] = []

    # -- a split after the message ends ------------------------------------- #
    #
    # `more` is set on all but the last transfer, so a transfer offered after the message
    # ended begins a *new* delivery — and a delivery that begins without the three fields no
    # continuation may originate is the one thing those clauses forbid. The point after the
    # message ended is not a place a continuation may start: a sender that keeps cutting has
    # nothing left to cut, and what it writes is a delivery a receiver cannot attach to the
    # message it believes it is assembling.
    cut = count // 2
    vectors.append(exchange(
        "flow-negative-transfer-after-the-message-ended", start=slices.s("MAPPED"),
        clauses=[SPLIT_POINTS, TRANSFER_CARRIES_A_MESSAGE] + FIRST_TRANSFER_FIELDS,
        steps=link_up(tables) + fragments(tables, octets, (cut,)) + [
            tables.refused(
                "receive", reason="malformed", condition=slices.INVALID_FIELD,
                state=slices.s("DISCARDING"),
                body=tables.body("transfer", handle={"type": "uint", "value": 0},
                                 **{"more": {"type": "boolean", "value": True}}),
                channel=1, payload=octets[cut:],
                note="`more` was unset on the transfer that completed the delivery, so this "
                     "one begins another: a delivery that begins without a delivery-id, a "
                     "delivery-tag and a message-format is what those three clauses refuse, "
                     "and no continuation of the finished delivery exists for these octets "
                     "to continue")],
        note="the split that is one cut too far: the same octets, offered as a continuation "
             "of a delivery that has already completed, are refused because there is no "
             "delivery for them to continue — the `more` flag's other half, which a family "
             "that only ever admits framings cannot show"))

    # -- a frame over the size the clause defers to ------------------------- #
    #
    # The clause's own subject and its own reason for splitting: a peer announces a maximum
    # frame size, and a split that leaves a frame over it is not a framing the artifact
    # permits however interior the boundary is. The vector carries both sides — a split that
    # fits, admitted, and one octet more, refused — so the refusal is about the size and not
    # about fragmentation.
    limit = tables.min_max_frame_size
    fixed = slices.FRAME_HEADER + len(slices.encode(tables.fragment_body(0, 2)))
    fits = limit - fixed - 1
    over = limit - fixed + 1
    long_octets = oversized_message(limit - fixed + 1)
    vectors.append(exchange(
        "flow-negative-fragment-over-the-announced-frame-size", start=slices.c("START"),
        clauses=[SPLIT_POINTS, MAX_FRAME_SIZE, OVERSIZED_FRAME, PRE_NEGOTIATION_LIMITS,
                 TRANSFER_CARRIES_A_MESSAGE],
        steps=[tables.send_header("amqp"),
               tables.send_frame(slices.AMQP_FRAME, tables.open_body(max_frame_size=limit),
                                 state=slices.c("OPEN_PIPE")),
               tables.receive_header("amqp", state=slices.c("OPEN_SENT")),
               tables.receive_frame(slices.AMQP_FRAME,
                                    tables.open_body("server",
                                                     max_frame_size=tables.max_frame_size_default,
                                                     channel_max=tables.channel_max_default),
                                    state=slices.c("OPENED")),
               tables.send_frame(slices.AMQP_FRAME, tables.begin_body(),
                                 state=slices.s("BEGIN_SENT"), channel=1),
               tables.receive_frame(slices.AMQP_FRAME,
                                    tables.begin_body(remote_channel=1),
                                    state=slices.s("MAPPED"), channel=1)] +
              link_up(tables) + fragments(tables, long_octets, (fits,)) + [
            tables.refused(
                "receive", reason="limit", state=slices.c("DISCARDING"),
                body=tables.fragment_body(0, 2, delivery_id=1), channel=1,
                payload=long_octets[:over],
                note=f"this peer announced a maximum frame size of {limit}, and the first "
                     f"frame of this delivery would total {over + fixed}: one octet over the "
                     f"limit, which is the smallest framing the artifact refuses. The split "
                     f"at {fits} two steps above is the same sender, the same message and the "
                     f"same single cut with one octet less in the first frame, and it is "
                     f"admitted — which is what makes this a limit on the framing rather "
                     f"than on fragmentation")],
        note="the clause's own subject: `links.29` allows a message to be split because it is "
             "too large for one frame, and the size it defers to is the peer's announced "
             "maximum — so a split point that fits is admitted and one that does not is "
             "refused, in one vector, from one sender, on one link"))

    # -- a continuation that contradicts the first transfer ------------- #
    #
    # The third rule the family carries, and the only one that is about the *continuation*
    # transfer a split produces rather than about where the split falls: `delivery-id.u1`,
    # `delivery-tag.u1` and `message-format.u1` each make it an error for a continuation to
    # differ from the first transfer of its delivery. `differing_continuation_negatives` builds
    # one vector per field, each with the omission admitted before the contradiction refused.
    vectors.extend(differing_continuation_negatives(tables))

    return vectors


def oversized_message(needed: int) -> bytes:
    """A message long enough for a split point whose first frame leaves the announced limit.

    Grown from a sentence in whole repetitions until the message is at least `needed` octets
    long, so the length is computed from the limit rather than chosen: a limit the artifact
    changed, or a transfer encoding that grew, moves this message rather than silently
    turning the vector into one that fits.
    """
    text = OVERSIZED_SENTENCE
    while len(declared_message(text)) <= needed:
        text += OVERSIZED_SENTENCE
    return declared_message(text)


def report(vectors: list[dict], negatives: list[dict]) -> None:
    """The counts and the split points, which is what makes the family's coverage legible
    without reading the corpus."""
    splits = [vector["vector"].removeprefix("flow-fragment-split-") for vector in vectors
              if vector["vector"].startswith("flow-fragment-split-")]
    triples = [vector["vector"].removeprefix("flow-fragment-three-transfers-")
               for vector in vectors
               if vector["vector"].startswith("flow-fragment-three-transfers-")]
    admitted = sum(1 for vector in vectors for step in vector["steps"]
                   if step["expect"]["status"] == "admitted")
    refused = sum(1 for vector in negatives for step in vector["steps"]
                  if step["expect"]["status"] == "refused")
    print(f"  the message: {len(declared_message(SWEPT_TEXT))} octets")
    print(f"  split points swept: {','.join(splits)} ({len(splits)} interior boundaries)")
    print(f"  three-transfer framings: {', '.join(triples)}")
    print(f"  {len(vectors)} positive vector(s), {admitted} admitted step(s); "
          f"{len(negatives)} negative vector(s), {refused} refused step(s)")


def self_check() -> None:
    """The generator's own controls, and the two of them that would otherwise be readings.

    * The message is the declared sections' octets — `data` then `amqp-value`, with the
      descriptors the messaging artifact declares and the length prefixes the types grammar
      fixes. A descriptor or a length rule that changed would move this check before it moved
      a vector.
    * The message is those two sections and no others, and the second section's octets are
      the tail of the message: a message that was one section repeated would make the sweep
      weaker than the family claims while every vector still passed.
    * Every vector's chunks rebuild that message. A split point that dropped, duplicated or
      reordered an octet would produce a family that fragments something other than the
      message it names — invisible in the sweep, because every vector would still be
      admitted.
    * The frame-size negative's two split points are on opposite sides of the limit it
      names, so the vector cannot decay into one that is refused for another reason.
    * Each difference negative's middle transfer omits all three continuation fields and its
      last carries exactly one, with a value the first transfer's is not: the omission is what
      the vector observes admitted, and a single field is what makes the refusal attributable.
    """
    first, second = section_named("data"), section_named("amqp-value")
    if first.code == second.code:
        raise SystemExit("the two sections the message is made of share a descriptor")
    message = declared_message(SWEPT_TEXT)
    head = messages.octets(first, {"hex": SWEPT_TEXT.encode("utf-8").hex()})
    tail = messages.octets(second, {"value": {"type": "string", "text": SWEPT_TEXT}})
    if message != head + tail or head == tail:
        raise SystemExit("the message is not exactly the two declared sections, in order")
    if len(message) < 2:
        raise SystemExit("a message of fewer than two octets has no interior split point")
    for split in range(1, len(message)):
        if message[:split] + message[split:] != message:
            raise SystemExit(f"the chunks at split {split} do not rebuild the message")
    for cuts in ((1, 2), (len(message) // 2, len(message) // 2 + 1)):
        first_cut, second_cut = cuts
        if message[:first_cut] + message[first_cut:second_cut] + message[second_cut:] != message:
            raise SystemExit(f"the chunks at {cuts} do not rebuild the message")
    tables = slices.Corpus()
    limit = tables.min_max_frame_size
    fixed = slices.FRAME_HEADER + len(slices.encode(tables.fragment_body(0, 2)))
    long_message = oversized_message(limit - fixed + 1)
    if fixed + (limit - fixed - 1) > limit:
        raise SystemExit("the fitting split is not under the limit")
    if fixed + (limit - fixed + 1) <= limit:
        raise SystemExit("the refused split is not over the limit")
    if len(long_message) <= limit - fixed + 1:
        raise SystemExit("the long message has no split point that leaves the limit")
    # The three difference negatives are only *about* the difference if the difference is all
    # that changed: the middle transfer must carry none of the three fields — which is the
    # omission the vector observes admitted before it refuses — and the last must carry one whose
    # value is not the first transfer's. A copy-paste that left the first transfer's value in the
    # last step would produce a vector that refuses nothing, and one that filled the middle step
    # in would produce a vector whose admitted step is not the omission it claims.
    for entry in continuation_difference(tables):
        field = entry["field"]
        if declared_item(tables, entry["middle"], "transfer", field) != {"type": "null"}:
            raise SystemExit(f"the difference negative's middle transfer carries {field}, so the "
                             f"omission it must observe admitted is not in it")
        if declared_item(tables, entry["body"], "transfer", field) == \
                declared_item(tables, entry["first"], "transfer", field):
            raise SystemExit(f"the difference negative's last transfer repeats the first "
                             f"transfer's {field}, so it contradicts nothing")
        for other in CONTINUATION_IDENTITY:
            if other != field and \
                    declared_item(tables, entry["body"], "transfer", other) != {"type": "null"}:
                raise SystemExit(f"the difference negative for {field} also carries {other}, so "
                                 f"its refusal would not be attributable to one field")
