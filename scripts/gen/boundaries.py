"""The rule-boundary family: the buffers where the type system's rules bite.

This is one family of the corpus generator, and `scripts/gen-value-vectors.py` is the
command line that dispatches to it.

The other value families sweep *values*: `gen/values.py` encodes a value and asserts
the octets, rejects malformed inputs the grammar already forbids, and sweeps every
one- and two-octet input for decode stability. None of them probes a *rule's
boundary* — the octet counts at which a rule stops holding, and the buffers where two
rules disagree about what is wrong. That gap is not theoretical: two artefacts can
agree that a buffer must be refused while reporting different conditions for it, and a
corpus that only asserts refusal cannot see the difference. Measured against the pinned
toolchain, this is exactly what happens at one point (see `boundary-negative-*` below).

## Where the expectations come from

Every vector here is authored from a clause of Part 1, and the clause is cited on the
vector. The rules this family probes, and the reading each expectation follows:

* **parity** (`MAP_CLAUSE`) — a map's items are keys and values in pairs, so an odd
  item count is not a map. A buffer that is *only* odd is refused as a malformed value:
  the count is what makes the pairing claim, and nothing about the octets is
  mis-framed.
* **the size field** (`ENCODINGS_CLAUSE`, and the array table at `ARRAY_ANCHOR`) — a
  compound announces the octets that follow its size field. A buffer whose announced
  count disagrees with what the content measures is refused as a size mismatch, and
  the artifact's own array example fixes what "measures" means: ten null elements are
  `e0 02 0a 40`, so the size counts the count octet *and* the element constructor, and
  the element data is empty because null occupies no octets. `self_check` pins the
  builder to that example rather than to a reading of the prose.
* **the declared element constructor** (`ARRAY_ANCHOR`) — an array's elements are
  carried in the constructor it declares, so element data that does not fit that
  constructor's width is a framing fault, not a property of the elements.
* **zero-width and fixed-width payloads** (`WIDTHS_ANCHOR`, `FIXED_ANCHOR`) — the
  encodings with no payload carry none, and the fixed-width ones carry exactly their
  width. A buffer that gives them more is asking the reader to consume octets no
  encoding accounts for.

## Two rules at once, and the order they are checked in

The artifact's published example settles the accounting for *legal* buffers, but it
cannot settle what a reader should say about an *illegal* one. Two faults can coexist: a
compound may declare a size that disagrees with its content **and** an odd item count. The
rules are then in an order the artifact does not state, and this family carries each such
buffer **under both size accountings** so that the order is what the vectors probe rather
than something they assume.

That order is now settled, and the vectors state it: **form checks first, then the size
comparison.** So a buffer that breaks both draws the parity class — `malformed` — while
`sizeMismatch` is for a buffer whose size is the *only* thing wrong. The decision is the
plan's, in the ambiguity register's `check-precedence-unspecified` entry, which was
extended from the frame layer to this one rather than duplicated: the frame layer had
already adopted form-first, the reference's array path was already checking its count-based
rule before reading elements and before the size — so its map path was the outlier inside
itself — and the parity rule is decidable from the count field alone, before any element
octet is touched. What this family contributes is the buffers that made the question
concrete, and the record of what the two artefacts said before the order was written down.

The rows in that record were: the reference answered `sizeMismatch` and the specification
`malformed` on the two-rule buffers, each internally consistent, which is why the question
could not be settled from either artefact alone.

## Why the class is pinned rather than the verdict

Measured against the pinned toolchain over a first probe of nineteen buffers at these
boundaries: the two artefacts agreed on *status* in all nineteen — nothing was admitted
by one and refused by the other — and disagreed on the *class* for two, both of them
buffers breaking parity and the size rule at once. Four more differed only in the wording
of their detail strings, within a single class.

So a corpus that asserts reject-or-admit can pass while two artefacts report different
conditions for the same buffer, and one that compares detail strings fails on wording
that no clause governs. That is why every refusal here names `expectError.reason` — the
schema's class — and why the class is stated from the clause rather than copied from a
run: the divergence this family exists to show is unreachable from a verdict. The runner
had to be changed to compare the field before any of this was visible at all; until it
did, a vector naming one class and an artefact reporting another still passed.

The same probe settled the arithmetic, which is worth recording because a simpler reading
of it was believed first: **the accounting is shared**. Both artefacts count the count
octet inside the size the artifact's examples use, and a buffer breaking only the size
rule draws the same class from both. What differed was *precedence* — which of two broken
rules a reader reports — and that is the question the two-rule vectors below put to the
register.

## Why there are no trailing-octet vectors here

A first draft of this family carried seven refusals built from a value followed by an
octet that no encoding accounts for — `40 00`, `41 00`, `43 00`, `50 01 02` and the rest —
on the reading that a decode must consume *all* the octets it is handed. Both artefacts
decoded the value and ignored the octet, and both are right: **a value's octets are a
prefix of whatever carries them.** A frame body holds several values in sequence, so
requiring a value to consume its whole carrier is a property of the *carrier*, not of the
value, and the contract "consuming all of them" is a frame-level one. The vectors are
withdrawn rather than re-stated, because the value vocabulary here cannot express the case
without claiming a defect that belongs to the carrier; and the place for it is a
frame-level family, where consuming the whole body is the contract being tested. The
behaviour is recorded here so that the next reader does not re-derive it and re-file it as
a value-layer defect, which is what this draft did.

## Nothing here is produced by running an artefact

The builders are arithmetic and a few octet constants, written from the clauses above.
Where a vector's expectation was corrected after a run, the correction is a note on the
vector saying what the run showed — the artefacts are never the source of the
expectation, and a class that the plan has not yet settled is marked pending rather than
copied from whichever artefact was run first.
"""

from __future__ import annotations

from gen import values

# The clauses this family cites. The bare `anchor.index` form and the picture register's
# `picture.N` form both resolve; which one is used says whether the rule is stated in
# prose or in the artifact's encoding tables.
MAP_CLAUSE = values.MAP_CLAUSE
ENCODINGS_CLAUSE = values.ENCODINGS_CLAUSE
ARRAY_ANCHOR = values.ARRAY_ANCHOR
WIDTHS_ANCHOR = values.WIDTHS_ANCHOR
FIXED_ANCHOR = values.FIXED_ANCHOR

# ------------------------------------------------------------------ the builders


def map8_declaring(declared: int, count: int, items: bytes) -> bytes:
    """A map8 whose size field says exactly what the caller says, right or wrong.

    The two-rule vectors and the size-only negatives need the declared size to be stated
    rather than computed, because the whole point of those vectors is that the declared
    size and the content disagree; a builder that computed it could not express them.
    """
    return bytes([0xC1, declared, count]) + items


def map8(items: bytes, count: int, *, count_in_size: bool) -> bytes:
    """A map8 whose size field is computed one of the two ways.

    `count_in_size` follows the accounting the artifact's examples use (the count octet
    is part of what the size announces); `False` is the other reading, which this family
    carries so that a buffer breaking two rules can be stated under both.
    """
    return map8_declaring(len(items) + (1 if count_in_size else 0), count, items)


def array8_declaring(declared: int, count: int, constructor: int, element_data: bytes) -> bytes:
    """An array8 whose size field says exactly what the caller says."""
    return bytes([0xE0, declared, count, constructor]) + element_data


def array8(count: int, constructor: int, element_data: bytes, *, count_in_size: bool) -> bytes:
    """An array8: size, count, one element constructor, then the element data.

    The declared size counts the count octet, the element constructor and the element
    data — the artifact's `e0020a40` for ten null elements is the pin for that, since it
    declares two octets with no element data at all.
    """
    body = bytes([count, constructor]) + element_data
    size = len(body) if count_in_size else len(body) - 1
    return bytes([0xE0, size]) + body


def list8(items: bytes, count: int, *, count_in_size: bool) -> bytes:
    """A list8, on the same two accountings as `map8`."""
    size = len(items) + (1 if count_in_size else 0)
    return bytes([0xC0, size, count]) + items


def list8_declaring(declared: int, count: int, items: bytes) -> bytes:
    """A list8 whose size field says exactly what the caller says.

    The count-against-items negatives need the size and the count stated independently:
    their whole subject is a buffer where one of the two disagrees with what is present,
    and a builder that derived either from the items could not express it.
    """
    return bytes([0xC0, declared, count]) + items


def reject(name: str, octets: bytes, clauses: list[str], reason: str, note: str) -> dict:
    """A vector whose octets a clause-conforming reader must refuse.

    `reason` is the *class* the clause implies, from the schema's vocabulary. It is part
    of the expectation rather than a detail: two artefacts can agree that a buffer is
    refused and disagree about the class, and a vector that does not name the class
    cannot show it.
    """
    return {
        "vector": name,
        "kind": "reject",
        "clauses": clauses,
        "bytes": octets.hex(),
        "expectError": {
            "condition": "amqp:decode-error",
            "endpoint": "connection",
            "reason": reason,
        },
        "note": note,
    }


def admitted(name: str, octets: bytes, clauses: list[str], value: dict, note: str,
             *, canonical: bool = False) -> dict:
    """A vector at the boundary that is *inside* the rule, so it must be read."""
    vector = {
        "vector": name,
        "kind": "decode",
        "clauses": clauses,
        "bytes": octets.hex(),
        "value": value,
        "note": note,
    }
    if canonical:
        vector["canonical"] = True
    return vector


# ------------------------------------------------------- the admitted boundary


def boundary_corpus() -> list[dict]:
    """The inside of every boundary this family probes: the buffers a reader must read.

    Each one sits exactly where a rule stops applying — an empty compound, a zero-width
    encoding with nothing after it, a constructor whose element data is exactly the
    width it declares — so that the negatives on the other side of the same boundary
    have something to be the other side *of*.
    """
    vectors: list[dict] = []

    # The smallest well-formed compounds: size 1, count 0, no items at all. The count
    # octet is the whole content, which is what makes an empty map's size 1 rather than
    # 0, and the boundary the negatives below are one octet away from.
    vectors.append(admitted(
        "boundary-map-empty", map8(b"", 0, count_in_size=True), [MAP_CLAUSE],
        {"type": "map", "pairs": []},
        "An empty map: the size announces the count octet and nothing else (size 1). "
        "The boundary the malformed sizes below are adjacent to.",
        canonical=True))
    vectors.append(admitted(
        "boundary-map-one-pair", map8(bytes([0x40, 0x40]), 2, count_in_size=True), [MAP_CLAUSE],
        {"type": "map", "pairs": [[{"type": "null"}, {"type": "null"}]]},
        "One pair: count 2 (even), size 3 = the count octet and the two item octets. "
        "The smallest map the parity rule admits.",
        canonical=True))
    vectors.append(admitted(
        "boundary-list-empty", list8(b"", 0, count_in_size=True), [ENCODINGS_CLAUSE],
        {"type": "list", "items": []},
        "An empty list, sized like the empty map: the count octet is the whole content. "
        "Legal but *not* canonical — the narrowest encoding of an empty list is list0 "
        "(0x45) — so this vector does not claim the octets are the canonical form, which "
        "is the distinction the two vectors together pin."))

    # The array boundary, pinned to the artifact's own example shape.
    vectors.append(admitted(
        "boundary-array-empty", array8(0, 0x40, b"", count_in_size=True), [ARRAY_ANCHOR],
        {"type": "array", "constructor": "40", "items": []},
        "An empty array: the size counts the count octet and the element constructor, so "
        "two octets with no element data. Same accounting as the artifact's ten-null "
        "example, one step down at the empty case.",
        canonical=True))
    vectors.append(admitted(
        "boundary-array-two-nulls", array8(2, 0x40, b"", count_in_size=True), [ARRAY_ANCHOR],
        {"type": "array", "constructor": "40",
         "items": [{"type": "null"}, {"type": "null"}]},
        "Two zero-width elements: the count says two, the constructor says null, and the "
        "element data is empty because null carries no payload.",
        canonical=True))
    vectors.append(admitted(
        "boundary-array-one-ubyte", array8(1, 0x50, bytes([0x07]), count_in_size=True), [ARRAY_ANCHOR],
        {"type": "array", "constructor": "50", "items": [{"type": "ubyte", "value": 7}]},
        "One fixed-width element: the element data is exactly the one octet the declared "
        "constructor carries. The boundary the short and long element data below crosses.",
        canonical=True))

    # Zero-width and fixed-width payloads, with nothing after them.
    for name, octet, value in [
        ("null", 0x40, {"type": "null"}),
        ("true", 0x41, {"type": "boolean", "value": True}),
        ("false", 0x42, {"type": "boolean", "value": False}),
        ("uint0", 0x43, {"type": "uint", "value": 0}),
        ("ulong0", 0x44, {"type": "ulong", "value": 0}),
        ("list0", 0x45, {"type": "list", "items": []}),
    ]:
        vectors.append(admitted(
            f"boundary-{name}-alone", bytes([octet]), [WIDTHS_ANCHOR], value,
            f"{name} carries no payload at all, so one octet is the whole encoding. The "
            f"boundary the trailing-octet negatives are adjacent to.",
            canonical=True))

    # A fixed-width payload exactly its width.
    vectors.append(admitted(
        "boundary-ubyte-exact", bytes([0x50, 0x01]), [FIXED_ANCHOR],
        {"type": "ubyte", "value": 1},
        "A fixed-width encoding with exactly the one octet it declares.",
        canonical=True))

    # The control for the duplicate-key rule: the same shape as the two duplicate
    # vectors, with the keys differing. Without it a reader that refused every two-pair
    # string-keyed map would look as though it enforced the rule.
    vectors.append(admitted(
        "boundary-map-two-distinct-string-keys",
        map8_declaring(9, 4, bytes([0xA1, 0x01, 0x61, 0x40, 0xA1, 0x01, 0x62, 0x40])),
        ["amqp:types/section:primitive-type-definitions/type:map.u1"],
        {"type": "map", "pairs": [[{"type": "string", "text": "a"}, {"type": "null"}],
                                  [{"type": "string", "text": "b"}, {"type": "null"}]]},
        "Two pairs with keys that differ, which is the same octet shape as the duplicate "
        "negatives with one payload octet changed. The control that keeps a refusal of "
        "those from being read as enforcement of the rule.",
        canonical=True))

    return vectors


# ------------------------------------------------------------ the refused boundary


def boundary_negative_corpus() -> list[dict]:
    """The outside of every boundary: the buffers a reader must refuse, with the class.

    Three groups, and the grouping is the point. The first two are buffers that break
    exactly one rule, so the class follows from that rule and both artefacts are
    expected to agree. The third breaks two at once — a size that disagrees with the
    content *and* an odd item count — and the artifact does not state which rule a
    reader reports first, so its class is marked as a pending reading rather than
    settled here.
    """
    vectors: list[dict] = []

    # --- one fault: parity only, on a size that is correct ---------------------------
    # Size 4 = the count octet and three item octets, so the framing is sound and the
    # only thing wrong is that three items cannot be keys and values in pairs.
    vectors.append(reject(
        "boundary-negative-map-odd-items-only", map8(bytes([0x40, 0x40, 0x40]), 3, count_in_size=True),
        [MAP_CLAUSE], "malformed",
        "Three items on a size that measures exactly: the framing is sound, so the only "
        "rule broken is parity. The count is what makes the pairing claim, so the class "
        "is the value's, not the framing's."))
    vectors.append(reject(
        "boundary-negative-map-single-item", map8(bytes([0x40]), 1, count_in_size=True),
        [MAP_CLAUSE], "malformed",
        "The smallest odd map: one item, size 2, no size disagreement. Parity alone."))

    # --- one fault: the size field only, with an even count --------------------------
    # The count is even, so the pairing rule is satisfied and the framing rule is the
    # only one broken. `map8_declaring` states the size rather than computing it, because
    # a vector whose declared size and content agree is not this vector.
    vectors.append(reject(
        "boundary-negative-map-size-short", map8_declaring(2, 2, bytes([0x40, 0x40])),
        [ENCODINGS_CLAUSE], "sizeMismatch",
        "Two items and an even count, but the size announces only the two item octets and "
        "leaves the count octet unaccounted for: 2 declared, 3 measured."))
    vectors.append(reject(
        "boundary-negative-map-size-long", map8_declaring(4, 2, bytes([0x40, 0x40])),
        [ENCODINGS_CLAUSE], "sizeMismatch",
        "The same even-count map with the size one octet too long: 4 declared, 3 "
        "measured. The framing rule is the only one broken, which is what makes this the "
        "control for the pair of two-rule vectors below."))
    vectors.append(reject(
        "boundary-negative-array-size-short", array8_declaring(1, 1, 0x50, bytes([0x07])),
        [ARRAY_ANCHOR], "sizeMismatch",
        "One ubyte element with the size announcing the element data alone: 1 declared, 3 "
        "measured, since the count octet and the element constructor are inside the size "
        "the artifact's own array example fixes."))
    vectors.append(reject(
        "boundary-negative-array-size-long", array8_declaring(4, 1, 0x50, bytes([0x07])),
        [ARRAY_ANCHOR], "sizeMismatch",
        "The same array with the size one octet too long: 4 declared, 3 measured."))

    # --- one fault: the duplicate-key rule, which the ledger tracks as uncovered -------
    # Part 1 says a map in which two identical keys appear is invalid, and states it
    # without an RFC 2119 keyword: the ledger holds it as `.../type:map.u1` with class
    # UNKEYED and disposition `deferred:map-duplicate-keys`, whose own note records that
    # no vector covers it. These two are that vector, at the two smallest cases — a
    # string key and the null key — so that the rule is exercised without depending on
    # string comparison being the mechanism a reader uses.
    vectors.append(reject(
        "boundary-negative-map-duplicate-string-keys",
        map8_declaring(9, 4, bytes([0xA1, 0x01, 0x61, 0x40, 0xA1, 0x01, 0x61, 0x40])),
        ["amqp:types/section:primitive-type-definitions/type:map.u1"], "malformed",
        "Two pairs whose keys are the same one-octet string 'a', with the size and the "
        "even count both consistent, so the duplicate key is the only rule broken. (An "
        "earlier form of this vector wrote the key as `a1 61`, which is str8 with a "
        "*length* of 0x61 and was refused as truncated before reaching the rule — both "
        "artefacts said so identically, and the note is here because the difference "
        "between a length octet and a payload octet is exactly what this family is "
        "sensitive to.) Part 1 states the rule without a keyword and the artifact states "
        "no class for it, so the class here is this corpus's value rule rather than a "
        "reading of the text, and the ledger's disposition remains the record of what is "
        "owed."))
    vectors.append(reject(
        "boundary-negative-map-duplicate-null-keys",
        map8_declaring(5, 4, bytes([0x40, 0x40, 0x40, 0x40])),
        ["amqp:types/section:primitive-type-definitions/type:map.u1"], "malformed",
        "Two pairs whose keys are both null: the same rule with the smallest possible "
        "key, which removes the question of how a key is compared."))

    # --- one fault: an array's element data against its declared constructor ----------
    vectors.append(reject(
        "boundary-negative-array-null-constructor-with-data", bytes([0xE0, 0x01, 0x01, 0x40, 0x40]),
        [ARRAY_ANCHOR], "sizeMismatch",
        "The declared constructor is null, which occupies no octets, so the size claims "
        "one octet of element data that no element of this constructor can explain."))
    vectors.append(reject(
        "boundary-negative-array-uint-constructor-short-data", bytes([0xE0, 0x05, 0x01, 0x70, 0x00, 0x00, 0x01]),
        [ARRAY_ANCHOR], "truncated",
        "The declared constructor is the four-octet uint form and the element data holds "
        "three octets: the array's own size is consistent, and the element cannot be read."))
    vectors.append(reject(
        "boundary-negative-array-smalluint-constructor-extra-data",
        array8(1, 0x52, bytes([0x01, 0x02]), count_in_size=True),
        [ARRAY_ANCHOR], "sizeMismatch",
        "One element declared as the one-octet smalluint form with two octets of element "
        "data: the second octet is data no element of this constructor accounts for. The "
        "artifact constrains the constructor's *grammar* and its own example uses a "
        "variable-width constructor, so it states no class for data that does not fit the "
        "declared constructor; both artefacts report the framing class, and the vector "
        "states that with the artifact's silence recorded rather than filled."))

    # --- one fault: a count that disagrees with the items present ---------------------
    # The size field says how many octets there are to read the items from; the count field
    # says how many items there are. The negatives above move the *size* and leave the count
    # matching, so a reader that trusted the count and one that trusted the size answer the
    # same on all of them. These are the other axis, and they are the compound half of the
    # declared-versus-actual family: the container's own declaration against its contents.
    vectors.append(reject(
        "boundary-negative-list8-count-over-items", list8_declaring(2, 2, bytes([0x40])),
        [ENCODINGS_CLAUSE], "truncated",
        "A list8 whose size announces the count octet and one item octet, and whose count "
        "announces two items: the framing is self-consistent and the items are not there, so "
        "what runs out is the second item."))
    vectors.append(reject(
        "boundary-negative-list8-items-over-count", list8_declaring(4, 1, bytes([0x40, 0x40])),
        [ENCODINGS_CLAUSE], "sizeMismatch",
        "A list8 whose size announces the count octet and three item octets while the count "
        "announces one item and two are present: the count is satisfied and the octets are not "
        "all accounted for, so the disagreement is the size's."))
    vectors.append(reject(
        "boundary-negative-list8-zero-count-with-item", list8_declaring(2, 0, bytes([0x40])),
        [ENCODINGS_CLAUSE], "sizeMismatch",
        "A list8 that declares no items at all and carries one: the smallest count-versus-items "
        "disagreement there is, and the one a reader that only counted to `count` would read as "
        "an empty list while the octet sat unaccounted for."))
    vectors.append(reject(
        "boundary-negative-map8-count-over-items", map8_declaring(2, 2, bytes([0x40])),
        [MAP_CLAUSE, ENCODINGS_CLAUSE], "truncated",
        "A map8 whose even count of two items is satisfied by one item's octets only: parity is "
        "sound, so the count against the items is the only rule broken. The control the parity "
        "vectors need, since a reader that refused every two-item map would look as though it "
        "enforced something."))
    vectors.append(reject(
        "boundary-negative-map8-items-over-count", map8_declaring(5, 2, bytes([0x40, 0x40])),
        [MAP_CLAUSE, ENCODINGS_CLAUSE], "sizeMismatch",
        "A map8 with an even count of two items, two items present, and a size two octets "
        "larger than the count and items measure: the size is the only rule broken."))
    vectors.append(reject(
        "boundary-negative-array-count-over-data", array8_declaring(2, 2, 0x50, b""),
        [ARRAY_ANCHOR], "truncated",
        "An array8 declaring two elements of the one-octet ubyte form with no element data: "
        "the declared size counts the count octet and the element constructor, so the array is "
        "self-consistent and the elements are what run out."))
    vectors.append(reject(
        "boundary-negative-array-data-over-count",
        array8_declaring(4, 1, 0x50, bytes([0x07, 0x07])),
        [ARRAY_ANCHOR], "sizeMismatch",
        "The same array with one element declared and two elements' octets present: the size "
        "accounts for count, constructor and both octets, and the second octet is data no "
        "declared element accounts for. The ubyte twin of the smalluint extra-data vector "
        "above, so the class is a property of the count and not of the constructor's width."))

    # --- withheld: the trailing-octet case belongs to the carrier, not the value -------
    # A first draft carried seven refusals here — a zero-width or fixed-width value
    # followed by an octet its encoding does not account for. They are withdrawn rather
    # than re-stated. Both artefacts decode the value and ignore the octet, and both are
    # right: a value's octets are a *prefix* of whatever carries them, since a frame body
    # holds several values in sequence, so "consuming all of them" is a property of the
    # carrier and not of the value. The value vocabulary cannot express the case without
    # claiming a defect that belongs elsewhere, and the place for it is a frame-level
    # family. See the header section "Why there are no trailing-octet vectors here".

    # --- two faults at once: the order the register settles ---------------------------
    # These are the vectors this family exists for. Each breaks the framing rule *and*
    # the parity rule, under one of the two size accountings, so a reader that checks
    # either first refuses the same buffer and reports a different condition. The class is
    # the parity one, on the register's settled order — form checks before the size
    # comparison, `check-precedence-unspecified`, extended from the frame layer — and the
    # history is on the vector because these two buffers are what made the question
    # concrete: the reference answered `sizeMismatch` and the specification `malformed`
    # until the order was written down, and both were internally consistent.
    vectors.append(reject(
        "boundary-negative-map-odd-and-size-small", map8(bytes([0x40, 0x40, 0x40]), 3, count_in_size=False),
        [MAP_CLAUSE, ENCODINGS_CLAUSE], "malformed",
        "Odd item count on a size that counts the item octets alone: 3 declared, 4 "
        "measured. Two rules broken at once, so the class is the one the settled order "
        "gives the first check — parity is decidable from the count field alone, before "
        "any element octet is read — and the size disagreement is not reported because "
        "the value is already not a map."))
    vectors.append(reject(
        "boundary-negative-map-odd-and-size-large", bytes([0xC1, 0x08, 0x03, 0x40, 0x40, 0x40]),
        [MAP_CLAUSE, ENCODINGS_CLAUSE], "malformed",
        "Odd item count with a size of 8 where the content measures 4. The same two-rule "
        "overlap as the vector above with the size disagreement four octets rather than "
        "one, so that a reader reporting the class settles the *order* rather than the "
        "size of the discrepancy."))
    vectors.append(reject(
        "boundary-negative-map-odd-and-size-smallest", map8(bytes([0x40]), 1, count_in_size=False),
        [MAP_CLAUSE, ENCODINGS_CLAUSE], "malformed",
        "The smallest buffer that breaks both rules: one item, so parity is broken by the "
        "least it can be, on a size that counts the item octet alone (1 declared, 2 "
        "measured). This is the witness the two readers disagreed on — the reference "
        "reported `sizeMismatch` and the specification `malformed` until the order was "
        "settled — and `Proofs.ValueLayerLaws.mapWitness` is the same octets as a theorem."))
    vectors.append(reject(
        "boundary-negative-map-odd-and-truncated", map8_declaring(4, 3, bytes([0x40, 0x40])),
        [MAP_CLAUSE, ENCODINGS_CLAUSE], "malformed",
        "Odd count 3 with only two item octets present and a size of 4. Three checks "
        "would give three classes on this buffer — parity `malformed`, the declared size "
        "`sizeMismatch`, the items `truncated` — so it separates the settled order from "
        "both alternatives rather than only from the size-first one."))
    vectors.append(reject(
        "boundary-negative-map32-odd-and-size-large",
        bytes([0xD1, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x03, 0x40, 0x40, 0x40]),
        [MAP_CLAUSE, ENCODINGS_CLAUSE], "malformed",
        "The four-octet-width twin of the size-large two-rule vector: same two rules, "
        "same class, so the settled order is a property of the check rather than of the "
        "width field that carries the count."))
    vectors.append(reject(
        "boundary-negative-list-holding-odd-map", bytes([0xC0, 0x05, 0x01, 0xC1, 0x08, 0x03, 0x40]),
        [MAP_CLAUSE, ENCODINGS_CLAUSE], "malformed",
        "A well-formed list8 whose one item is a map8 with an odd count and a size of 8 "
        "that nothing supports. The outer framing is sound and the outer size is exact, "
        "so the refusal can only come from the inner map's own rule: the two-rule case is "
        "not a property of a buffer's first octet, and a reader that reports it from the "
        "inner value is the one that reports it from the outer one too."))

    return vectors


# ---------------------------------------------------------------------- the pins


def self_check() -> None:
    """Pin the builders against the artifact's own example, before building anything.

    The array example fixes the accounting the whole family is stated against: ten null
    elements are `e0 02 0a 40`. If the builder ever computed a different size for a
    legal array, every boundary vector below would be measuring the wrong thing, and the
    negatives would be refused for the builder's arithmetic rather than the rule's.
    """
    ten_nulls = array8(10, 0x40, b"", count_in_size=True)
    if ten_nulls.hex() != "e0020a40":
        raise SystemExit(
            f"self_check: ten null elements built as {ten_nulls.hex()}, the artifact's "
            f"example is e0020a40")
    # The same accounting on the map side, cross-checked against the value family's own
    # empty map (`gen-map-0`, three octets: the constructor, a size of 1, a count of 0),
    # so the two families cannot drift apart about what a compound's size counts.
    empty_map = map8(b"", 0, count_in_size=True)
    if empty_map.hex() != "c10100":
        raise SystemExit(
            f"self_check: the empty map built as {empty_map.hex()}, the value family's "
            f"gen-map-0 is c10100")


def report(boundary: list[dict], negatives: list[dict]) -> None:
    """What the family is, and how much of it there is."""
    admitted_count = sum(1 for v in boundary if v["kind"] == "decode")
    two_rule = [v for v in negatives if len(v["clauses"]) > 1]
    print(f"  rule boundaries: {len(boundary)} admitted ({admitted_count} decode) "
          f"and {len(negatives)} refused")
    print(f"  of the refusals, {len(two_rule)} break two rules at once, so they state the "
          f"settled check order rather than a single rule's class")
