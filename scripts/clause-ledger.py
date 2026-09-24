#!/usr/bin/env python3
"""Extract the normative statements of the pinned OASIS AMQP 1.0 artifacts.

    scripts/clause-ledger.py generate [--artifacts DIR] [--out DIR]
    scripts/clause-ledger.py check    [--artifacts DIR] [--out DIR] [--dispositions DIR]

`generate` walks the pinned XML in document order and emits one record per
normative statement, plus a coverage report. `check` validates the disposition
files against the generated ledger and reports undispositioned MUST-class
clauses; it also resolves the declarations and vectors those dispositions name
against `lean/**` and `vectors/*.ndjson`, so a claim about a carrier that does not
exist fails rather than sitting in the record unnoticed. It exits non-zero on any
problem.

Why a token-aware walk rather than a keyword grep (§6 of PLAN.md):

* inline emphasis wraps the keyword in the real markup (`<b>MUST</b>`);
* keywords are split across source lines (`MUST\\nNOT`);
* `<picture>` diagrams, `revhistory` and `acknowledgements` are not normative;
* dispositions must be keyed to a clause's *text hash*, so editing the source
  text invalidates a stale decision instead of silently leaving it in place.

Clause identity is `<artifact>#<anchor path>.<n>`, where the anchor path is the
chain of enclosing named elements (`section:framing/type:open/field:container-id`)
and `n` is the 1-based index of the statement inside that anchor in document
order. A bare `name` is not enough: `field name="value"` occurs inside many
types, so the path is what makes an id unique and stable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from xml.etree import ElementTree

# Prose-bearing leaf blocks. A block is a statement unit; blocks nested inside
# other blocks (for example `<dd>` holding `<p>`) are not counted twice.
BLOCK_TAGS = {"p", "li", "dt", "dd", "th", "td", "pre"}

# Subtrees that carry no normative statements.
EXCLUDED_TAGS = {"picture", "revhistory", "acknowledgements"}

# Normative statements the keyword scan cannot see. The artifacts sometimes state a
# requirement without an RFC 2119 keyword — Part 1's map type says "A map in which
# there exist two identical key values is invalid" — and a ledger that only counts
# keywords would report completeness while missing exactly that kind of sentence.
# These are captured as reviewable statements, like pictures: an omission must be a
# decision rather than a blind spot.
#
# The last two alternatives are one shape, and it was found by a slice rather than by a
# reading: Part 4 states an obligation the whole transaction layer rests on as the
# *consequence* of an action, in the indicative and with no keyword — "If the control
# link is closed while there exist non-discharged transactions it created, then all such
# transactions are immediately rolled back, and attempts to perform further
# transactional work on them will lead to failure." That sentence is the rule the
# transactions section is about; it was invisible to the census, and a slice whose
# behaviour depends on it could not cite it.
#
# The shape is "a stated consequence": a conditional whose consequent is asserted in the
# indicative (`then … is/are/will/…`), and a consequence named as leading to a failure.
# It is deliberately not keyed on the one sentence's wording: measured against the pinned
# artifacts it captures 25 statements beyond the previous vocabulary — in `links`,
# `sessions`' flow-control doc, `attach`'s `source`/`target`, and `txn-work` — of which
# several are plainly normative ("If no source is specified on an outgoing link, then
# there is no source currently attached to the link") and the rest are for review, which
# is what a captured statement is. `check_unkeyed` requires a disposition for each, so
# the addition lands with its reviews rather than instead of them.
UNKEYED_PHRASES = re.compile(
    r"\bis invalid\b|\bis not valid\b|\bis undefined\b|\bis reserved\b"
    r"|\bis not permitted\b|\bis not allowed\b|\bshall\b|\bis required to\b"
    r"|\bcannot\b|\bonly the [\w-]+(?: [\w-]+)? can\b"
    r"|\bthen\b[^.]{0,160}?\b(?:is|are|will|has|have|does|remains|can no longer)\b"
    r"|\bwill lead to\b|\bwill result in\b"
    # A census over the pinned artifacts named the class below and measured each
    # alternative alone against them: indicative statements of prohibition, error and
    # no-effect that carry no keyword ("It is an error if the delivery-tag on a
    # continuation transfer differs…", "It is illegal to send any more frames after
    # sending a close frame", "A link with no source will never produce outgoing
    # messages"), and plural or variant phrasings of alternatives already above
    # ("*are* reserved", "results in" against `will result in`, "*does not* increment",
    # "will *not* be able to be resumed", "can only be", "will no longer", "takes
    # precedence", "can be up to"). Each was measured on its own before landing, and each
    # captures at least one statement no other alternative does; the count after a phrase
    # is the statements it captured alone beyond the previous vocabulary, and a shape
    # whose unique contribution is smaller says so in brackets:
    #
    #   a stated error ........... 6      can be up to ............. 2
    #   it is illegal ............ 3      takes precedence ......... 1
    #   will never ............... 3      if and only if ........... 1
    #   will not be able to ...... 3      is not mandatory ......... 2
    #   will no longer ........... 2      is ineligible ............ 1
    #   is/are ignored ........... 2      are transitioned ......... 1
    #   is/are allowed ........... 1      will remain .............. 2
    #   be ignored ............... 1      is not set ............... 4 (3)
    #   are reserved ............. 2      does not <verb> ......... 20 (19)
    #   results in ............... 3      can only be .............. 3
    #   will be <participle> ..... 9
    #
    # Together they capture 71 statements beyond the previous vocabulary, and with the
    # declared-choice rule below the change adds 125. Of the 125, 78 state behaviour a
    # peer must implement and 47 define or explain a symbol, which is the split a reviewer
    # should expect: capturing the commentary is what makes the class visible, and the
    # disposition is where the judgement is made.
    #
    # One measured alternative is deliberately absent: `is not retained` captured two
    # sentences and no others, both of which `does not <verb>` already captures — a
    # phrase with no unique contribution in this corpus is not worth its weight in the
    # list. `does not <verb>` is the broadest shape here and the definition term it
    # matches is handled by the label guard below rather than by narrowing the shape to
    # a verb list, which would trade a rule for a word list. `is used` was measured and
    # declined: it captures the distribution node's fallback outcome for the default
    # outcome *and* fourteen sentences describing what a frame or a section is for, so
    # the one statement it would close does not pay for the fourteen.
    r"|\bis (?:an? )?(?:\w+ )?error\b|\bit is illegal\b"
    r"|\bwill never\b|\bwill not be able to\b|\bwill no longer\b"
    r"|\b(?:is|are) (?:ignored|allowed)\b|\bbe ignored\b"
    r"|\bdoes not \w+"
    r"|\bare reserved\b|\bresults in\b"
    r"|\bcan only be\b|\bcan be up to\b"
    r"|\btakes precedence\b|\bif and only if\b"
    r"|\bis not set\b|\bis not mandatory\b|\bis ineligible\b|\bare transitioned\b"
    r"|\bwill remain\b"
    r"|\bwill be (?:discarded|deleted|chosen|cleared|applied|retained|rolled back)\b",
    re.IGNORECASE,
)

# What a statement captured for a declared choice carries in `unkeyed_phrases`.
CHOICE_MEANING = "a declared choice's meaning"


def is_label_unit(unit: str) -> bool:
    """True when a statement unit is a label rather than prose.

    A definition term labels the definition beside it: `redirect`'s doc is a definition
    list whose terms are `hostname`, `network-host`, `port` and `address`, and
    `txn-work`'s two "Delivery Sent Unsettled By…" entries are the terms of the cases
    below them. The definition's own prose is a statement unit in its own right (the
    `dd`, or the `p` inside it), so nothing is lost by declining the term: measured over
    the pinned artifacts, no clause in the ledger — keyword or keyword-free — comes from
    a `dt` unit, and the phrase and declared-choice rules would otherwise capture seven
    of them as statements.
    """
    return unit == "dt"


def documents_a_choice(path: str) -> bool:
    """True when the anchor path names a declared `choice`.

    A choice's doc is the artifact's only statement of what its symbolic value means:
    `Generated/Oasis/Choices.lean` carries the owner path, the name and the value, and
    the meaning is written in prose beside the choice — "The sender will send all
    deliveries initially unsettled to the receiver" for `snd-settle-mode=unsettled`,
    "once successfully transferred over the link, the message will no longer be
    available to other links from the same node" for `move`. A symbol a peer's behaviour
    depends on cannot be carried by prose the census cannot see, so these are captured
    for review like the rest of the class.
    """
    return "/choice:" in path


# Pictures are excluded from clause extraction because most are sequence
# diagrams, but some carry formal grammar (`Constructor BNF`) or normative
# keywords. Those are surfaced for disposition rather than dropped: excluding a
# subtree is not the same as having decided it carries nothing.
# A picture earns review when it states a grammar (`%x`), carries a normative
# keyword, shows concrete encoded octets (`0x..`), or is a *table that assigns
# obligations* — a state machine's legal sends and receives, a dispatch table saying
# which endpoint handles which performative. That last clause was missing, and it
# mattered: the Connection State Table, the Frame Dispatch Table and the Protocol
# Header Layout were all classified as carrying nothing, while being the only
# normative statement in the artifact for the connection lifecycle. A diagram can be
# skipped after review; a table that says what a peer may send in each state cannot.
PICTURE_REVIEW_PATTERN = re.compile(
    r"%x|\bMUST\b|\bSHOULD\b|\bMAY\b|\bREQUIRED\b|\bOPTIONAL\b|0x[0-9A-Fa-f]{1,2}\b|0x[0-9A-Fa-f]{8}:0x[0-9A-Fa-f]{8}"
    r"|\bLegal (Sends|Receives|Connection Actions)\b|\bState\s+Legal\b|handled by the endpoint"
)

# Some normative pictures are named by their *title* and say nothing extractable in
# their text: the protocol header's layout is a row of columns, and the connection
# state diagram is arrows between state names. Matching the title is blunter than
# matching the content, and it is here because the alternative was a picture that
# carried the only statement of the header's layout while being classified as
# carrying nothing. A title match means "a human decides", which is what review is.
PICTURE_TITLE_REVIEW_PATTERN = re.compile(
    r"State (Table|Diagram)|Dispatch Table|Header Layout|Frame Layout|SASL Frame"
)

# Sections excluded by name: in the artifacts these are section *names*, not
# element tags, so matching on the tag alone silently keeps revision history and
# acknowledgement boilerplate in the ledger.
EXCLUDED_SECTION_NAMES = {"revhistory", "acknowledgements"}


def is_excluded(element: ElementTree.Element) -> bool:
    """True when the element and its subtree carry no normative statements."""
    if element.tag in EXCLUDED_TAGS:
        return True
    return element.tag == "section" and element.attrib.get("name") in EXCLUDED_SECTION_NAMES

# Elements that can carry a `name` attribute and therefore extend the anchor
# path. Any element with a `name` attribute is used, which is deliberate: the
# OASIS definition language names sections, types, fields, choices, encodings,
# descriptors and standalone docs.
ANCHOR_TAGS = {
    "amqp",
    "section",
    "type",
    "field",
    "choice",
    "encoding",
    "descriptor",
    "definition",
    "doc",
}

# Multi-token keywords are matched first and consume their tokens, so that
# `MUST NOT` is one clause rather than a MUST plus a stray NOT.
MULTI_KEYWORDS = (
    ("MUST", "NOT", "MUST NOT"),
    ("SHOULD", "NOT", "SHOULD NOT"),
    ("NOT", "RECOMMENDED", "NOT RECOMMENDED"),
)
SINGLE_KEYWORDS = ("MUST", "SHOULD", "REQUIRED", "OPTIONAL", "RECOMMENDED", "MAY")

# RFC 2119-class keywords are uppercase in the OASIS text. Lowercase uses are
# ordinary English; they are reported as a review signal, never as clauses.
KEYWORD_CLASSES = ("MUST", "MUST NOT", "SHOULD", "SHOULD NOT", "MAY")

ABBREVIATIONS = {"e.g", "i.e", "cf", "etc", "vs", "resp", "al", "approx", "seq"}

DISPOSITION_PREFIXES = (
    "formalized:",
    "deferred:",
    "environment:",
    "out-of-scope:",
    "underspecified:",
    "test:",
    "superseded:",
)

# Dispositions make two claims about the tree they sit beside: `formalized:` names
# the declaration that carries a clause, and `test:` names the vector that witnesses
# it. Neither claim was checked, so a declaration renamed or a vector never generated
# left a disposition pointing at nothing while every gate stayed green — the one such
# claim found so far was found by reading the code, which was the only tier that
# could find it. These two gates read the thing that would have to exist.
FORMALIZED_PREFIX = "formalized:"
TEST_PREFIX = "test:"

# A file's conventions block declares what its own vocabulary means, including
# whether its `formalized:` values are claims about the tree present now or promises
# the plan carries later. `part1-types.json` writes "the value domain and codec that
# the remaining dispositions name land with the rest of S1"; `part0` writes that its
# declarations were "verified present in the module it names". A commitment has
# nothing in the tree to resolve against, so it is exempt; the declaration is read
# from the record, never from a list of file names here, so the exemption ends when
# the file's own words are rewritten. A file that documents the vocabulary without
# declaring a commitment is making the existence claim, and a file that carries
# `formalized:` values while documenting nothing is reported by name.
FORWARD_COMMITMENT_MARKERS = ("commitment", "does not exist yet", "land with", "lands with")

# Declaration forms a `formalized:` carrier can take. Attributes and modifiers sit in
# front of the keyword, so the scan reads through them rather than missing an
# `@[simp] theorem` or a `private def`. The kind is captured because an `inductive`'s
# constructors are declarations too: `Spec.Connection.Submission.frame` names a
# constructor of `Submission`, and a scan that only read `inductive Submission` would
# file a false positive against a correct entry. `axiom` and `constant` are
# deliberately not collected — a carrier declared as an axiom is not a declaration
# this record accepts (the trust scan forbids them), so naming one must fail.
LEAN_DECLARATION_PATTERN = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(def|theorem|lemma|structure|inductive|abbrev|class|instance|opaque)\s+"
    r"([A-Za-z_][\w.']*[?!]?)"
)
LEAN_CONSTRUCTOR_PATTERN = re.compile(r"^\s*\|\s*([A-Za-z_][\w.']*)")
LEAN_NAMESPACE_PATTERN = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.']*)")
# `mutual ... end` is a block, and its `end` closes that block rather than whatever
# encloses it. Read as a frame of its own because the alternative is not a cosmetic
# error: without it the `end` pops the namespace, and every declaration after the
# module's first `mutual` block is registered under a bare name — so the gate would
# reject the correct qualified path and accept a name that resolves to nothing.
LEAN_MUTUAL_PATTERN = re.compile(r"^\s*mutual\s*$")
LEAN_SECTION_PATTERN = re.compile(r"^\s*section(?:\s+([A-Za-z_][\w.']*))?\s*$")
LEAN_END_PATTERN = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w.']*))?\s*(?:--.*)?$")

# The other spelling a `formalized:` value may take: the module itself, with an
# optional anchor — `lean/Spec/Session.lean`, `…#step`, `…:940-942`.
LEAN_MODULE_PATTERN = re.compile(r"^(?:lean/)?([A-Za-z0-9_./-]+\.lean)([#:].*)?$")
LEAN_ANCHOR_NAME_PATTERN = re.compile(r"^#([A-Za-z_][\w.']*)$")
LEAN_ANCHOR_LINES_PATTERN = re.compile(r"^:L?(\d+)(?:-L?(\d+))?$")

# Keywords counted by the audit. Multi-token keywords (`MUST NOT`) are counted
# through their first token, so the ledger-derived expectation for `MUST` is
# `clauses(MUST) + clauses(MUST NOT)`.
AUDIT_KEYWORDS = ("MUST", "SHOULD", "MAY", "RECOMMENDED", "REQUIRED", "OPTIONAL")

DERIVATION = {
    "MUST": ("MUST", "MUST NOT"),
    "SHOULD": ("SHOULD", "SHOULD NOT"),
    "MAY": ("MAY",),
    "RECOMMENDED": ("RECOMMENDED", "NOT RECOMMENDED"),
    "REQUIRED": ("REQUIRED",),
    "OPTIONAL": ("OPTIONAL",),
}


def die(message: str) -> "None":
    print(f"clause-ledger: {message}", file=sys.stderr)
    raise SystemExit(1)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def anchor_path(stack: list[str]) -> str:
    return "/".join(stack) if stack else "(root)"


def flatten_tokens(
    element: ElementTree.Element,
    drop_blocks: bool,
    constants: dict[str, str],
    refs: list[str],
) -> list[str]:
    """Tokens of an element's text, including inline markup, in document order.

    With `drop_blocks`, nested block-level children are skipped: their text is
    emitted as their own statement unit instead.

    Cross-references are rendered for a reader: `<xref name="MIN-MAX-FRAME-SIZE"/>`
    becomes `512`, because the artifact defines that constant, while a reference
    to a named element becomes `«open»`. Every referenced name is recorded, so the
    ledger keeps the link even where the rendered text resolves it.

    An `<xref>` may instead select a *choice* of the element it names —
    `<xref name="sender-settle-mode" choice="settled"/>`. What the sentence says is
    the chosen value, and the artifact names it (`<choice name="settled">`), so the
    choice renders as `«settled»`: the same name-in-guillemets convention as an
    element reference, applied to the declaration the cross-reference resolves to.
    Rendering the element's name instead made two clauses with opposite obligations
    read identically, which is how one came to be applied under the other's
    condition. The `choice` attribute decides, rather than the constant table: an
    `<xref>` naming a choice selects a value of a declared type, and no constant is
    a choice (the 13 `<definition>` names and every choice-carrying name in the
    pinned artifacts are disjoint). A choice-bearing reference records both halves —
    `sender-settle-mode/choice:settled` — so the link keeps the selection, which is
    the collapse that recording the bare name alone reintroduced.
    """
    tokens: list[str] = []

    def add(text: str | None) -> None:
        if text:
            tokens.extend(text.split())

    if element.tag == "xref" and element.attrib.get("name"):
        name = element.attrib["name"]
        choice = element.attrib.get("choice")
        if choice:
            refs.append(f"{name}/choice:{choice}")
            add(f"«{choice}»")
            return tokens
        refs.append(name)
        add(constants.get(name, f"«{name}»"))
        return tokens

    add(element.text)
    for child in element:
        if is_excluded(child):
            add(child.tail)
            continue
        if drop_blocks and child.tag in BLOCK_TAGS:
            add(child.tail)
            continue
        tokens.extend(flatten_tokens(child, drop_blocks, constants, refs))
        add(child.tail)
    return tokens


def glue_punctuation(tokens: list[str]) -> list[str]:
    """Attach standalone punctuation to the preceding token.

    The artifacts write `an opaque <i>payload</i>.`, which tokenises to
    `payload` then `.`. Gluing restores `payload.`, which is what makes sentence
    splitting and human reading work.
    """
    glued: list[str] = []
    for token in tokens:
        if glued and token and all(character in ".,;:)]}" for character in token):
            glued[-1] += token
        else:
            glued.append(token)
    return glued


def is_statement_unit(element: ElementTree.Element) -> bool:
    """True when the element itself carries prose rather than only sub-blocks."""
    if element.tag in BLOCK_TAGS:
        return not any(child.tag in BLOCK_TAGS for child in element)
    if element.tag == "doc":
        return bool((element.text or "").strip())
    return False


def sentence_spans(tokens: list[str]) -> list[tuple[int, int]]:
    """Half-open token spans of sentences within a statement unit."""
    spans: list[tuple[int, int]] = []
    start = 0
    for index, token in enumerate(tokens):
        if not token.endswith("."):
            continue
        bare = token[:-1]
        if not bare:
            continue
        if bare in ABBREVIATIONS or token.endswith("e.g.") or token.endswith("i.e."):
            continue
        if len(bare) == 1 and bare.isalpha():
            continue
        # Decimals such as `1.0` and dotted identifiers such as `amqp.open` do
        # not end a sentence.
        if bare[-1].isdigit() or bare[-1] in ".:/-_":
            continue
        spans.append((start, index + 1))
        start = index + 1
    if start < len(tokens):
        spans.append((start, len(tokens)))
    return spans


def find_keywords(tokens: list[str]) -> list[tuple[int, str]]:
    """Keyword occurrences as (token index, kind), longest match first."""
    found: list[tuple[int, str]] = []
    index = 0
    while index < len(tokens):
        matched = False
        for first, second, kind in MULTI_KEYWORDS:
            if tokens[index] == first and index + 1 < len(tokens) and tokens[index + 1] == second:
                found.append((index, kind))
                index += 2
                matched = True
                break
        if matched:
            continue
        if tokens[index] in SINGLE_KEYWORDS:
            found.append((index, tokens[index]))
        index += 1
    return found


def walk(
    element: ElementTree.Element,
    stack: list[str],
    artifact: str,
    counters: dict[str, int],
    clauses: list[dict],
    lowercase_only: list[dict],
    constants: dict[str, str],
) -> None:
    name = element.attrib.get("name")
    if name and element.tag in ANCHOR_TAGS:
        stack = stack + [f"{element.tag}:{name}"]

    if is_excluded(element):
        return

    if is_statement_unit(element):
        refs: list[str] = []
        tokens = glue_punctuation(
            flatten_tokens(element, drop_blocks=True, constants=constants, refs=refs)
        )
        if tokens:
            emit_statements(tokens, stack, artifact, counters, clauses, lowercase_only, refs,
                            element.tag)

    for child in element:
        walk(child, stack, artifact, counters, clauses, lowercase_only, constants)


def emit_statements(
    tokens: list[str],
    stack: list[str],
    artifact: str,
    counters: dict[str, int],
    clauses: list[dict],
    lowercase_only: list[dict],
    refs: list[str],
    unit: str,
) -> None:
    path = anchor_path(stack)
    spans = sentence_spans(tokens)
    text = " ".join(tokens)
    references = sorted(set(refs))

    for position, kind in find_keywords(tokens):
        counters[path] = counters.get(path, 0) + 1
        index = counters[path]
        span = next(((a, b) for a, b in spans if a <= position < b), (0, len(tokens)))
        sentence = " ".join(tokens[span[0] : span[1]])
        clauses.append(
            {
                "ref": f"{artifact}#{path}.{index}",
                "artifact": artifact,
                "anchor": path,
                "index": index,
                "kind": kind,
                "class": "MUST" if kind in ("MUST", "MUST NOT") else kind,
                "text": sentence,
                "text_sha256": sha256_text(sentence),
                "statement_sha256": sha256_text(text),
                "references": references,
            }
        )

    keyword_positions = [position for position, _ in find_keywords(tokens)]

    # Statements the keyword scan cannot see, at *sentence* granularity: a paragraph
    # may carry both a keyword-bearing requirement and a keyword-free one. Part 1's
    # map type is the case that forced this — "Map encodings MUST contain an even
    # number of items" and "A map in which there exist two identical key values is
    # invalid" are in the same paragraph, so a unit-level check sees the first and
    # silently loses the second.
    for start, stop in spans:
        if any(start <= position < stop for position in keyword_positions):
            continue
        sentence = " ".join(tokens[start:stop])
        if not sentence:
            continue
        # The paragraph that *defines* the keyword vocabulary is boilerplate about the
        # specification's own language, not a requirement: it was captured as a
        # statement until this exclusion, and it is not one.
        if sentence.startswith("The key words"):
            continue
        matched = sorted({phrase.strip().lower() for phrase in UNKEYED_PHRASES.findall(sentence)})
        if matched and is_label_unit(unit):
            # A phrase matched a definition term's text, which labels the definition
            # beside it rather than stating anything: see `is_label_unit`.
            matched = []
        if not matched and documents_a_choice(path) and not is_label_unit(unit):
            # The artifact's only statement of what this symbolic value means.
            matched = [CHOICE_MEANING]
        if matched:
            key = f"{path}#unkeyed"
            counters[key] = counters.get(key, 0) + 1
            clauses.append(
                {
                    "ref": f"{artifact}#{path}.u{counters[key]}",
                    "artifact": artifact,
                    "anchor": path,
                    "index": counters[key],
                    "kind": "UNKEYED",
                    "class": "UNKEYED",
                    "text": sentence,
                    "text_sha256": sha256_text(sentence),
                    "statement_sha256": sha256_text(sentence),
                    "references": references,
                    "unkeyed_phrases": matched,
                }
            )
        elif re.search(r"\b(must|should|may)\b", sentence):
            lowercase_only.append(
                {
                    "artifact": artifact,
                    "anchor": path,
                    "text": sentence if len(sentence) <= 240 else sentence[:237] + "...",
                }
            )


def collect_audit_tokens(
    element: ElementTree.Element, excluded: bool, included: list[str], excluded_tokens: list[str]
) -> None:
    """Collect every text node once, split by whether it sits in an excluded subtree.

    This is deliberately cruder than the ledger walk: it does not care about
    statement units or anchors. Its only job is to prove that no keyword token
    anywhere in the document escapes the ledger's accounting.
    """
    if is_excluded(element):
        excluded = True
    sink = excluded_tokens if excluded else included

    def add(text: str | None) -> None:
        if text:
            sink.extend(text.split())

    add(element.text)
    for child in element:
        collect_audit_tokens(child, excluded, included, excluded_tokens)
        add(child.tail)


def direct_text_keyword_snippets(element: ElementTree.Element, excluded: bool = False) -> list[dict]:
    """Elements whose own text carries a keyword but which are not statement units.

    Reported when the audit fails: this is the shape a missed statement would
    take (prose hanging directly off a `<section>` or `<type>` rather than living
    in a `<p>`/`<li>`/`<dd>`/`<doc>`).
    """
    if is_excluded(element):
        return []
    found: list[dict] = []
    if not is_statement_unit(element):
        tokens = (element.text or "").split()
        hits = [token for token in tokens if token in AUDIT_KEYWORDS]
        if hits:
            text = " ".join(tokens)
            found.append(
                {
                    "element": f"{element.tag}:{element.attrib.get('name', '')}".rstrip(":"),
                    "keywords": sorted(set(hits)),
                    "text": text if len(text) <= 200 else text[:197] + "...",
                }
            )
    for child in element:
        found.extend(direct_text_keyword_snippets(child, excluded))
    return found


def audit_ledger(root: ElementTree.Element, clauses: list[dict]) -> dict:
    """Compare a crude token census against what the ledger accounted for."""
    included: list[str] = []
    excluded: list[str] = []
    collect_audit_tokens(root, False, included, excluded)

    crude = {key: sum(1 for token in included if token == key) for key in AUDIT_KEYWORDS}
    crude_excluded = {key: sum(1 for token in excluded if token == key) for key in AUDIT_KEYWORDS}

    kinds: dict[str, int] = {}
    for clause in clauses:
        kinds[clause["kind"]] = kinds.get(clause["kind"], 0) + 1
    derived = {
        key: sum(kinds.get(kind, 0) for kind in DERIVATION[key]) for key in AUDIT_KEYWORDS
    }

    mismatches = {
        key: {"prose": crude[key], "ledger": derived[key]}
        for key in AUDIT_KEYWORDS
        if crude[key] != derived[key]
    }
    return {
        "prose": crude,
        "ledger": derived,
        "excluded": crude_excluded,
        "mismatches": mismatches,
        "unledgered_text": direct_text_keyword_snippets(root) if mismatches else [],
    }


def load_artifacts(directory: Path) -> list[Path]:
    files = sorted(directory.glob("amqp-core-*-v1.0-os.xml"))
    if not files:
        die(f"no amqp-core-*-v1.0-os.xml artifacts found in {directory}")
    return files


def collect_pictures(path: Path, artifact: str) -> list[dict]:
    """Every picture, with the ones that look normative flagged for review."""
    pictures: list[dict] = []
    for index, picture in enumerate(ElementTree.parse(path).getroot().iter("picture"), 1):
        text = " ".join("".join(picture.itertext()).split())
        title = picture.attrib.get("title", "")
        matches = sorted({match.group(0) for match in PICTURE_REVIEW_PATTERN.finditer(text)}
                         | {match.group(0) for match in PICTURE_TITLE_REVIEW_PATTERN.finditer(title)})
        pictures.append(
            {
                "ref": f"{artifact}#picture.{index}",
                "artifact": artifact,
                "index": index,
                "title": picture.attrib.get("title", ""),
                "content_sha256": sha256_text(text),
                "looks_normative": bool(matches),
                "matches": matches,
                "excerpt": text if len(text) <= 160 else text[:157] + "...",
            }
        )
    return pictures


def collect_constants(files: list[Path]) -> dict[str, str]:
    """Named constants (`<definition name value>`) across all artifacts.

    Cross-artifact on purpose: Part 5 refers to the transport layer's
    `MIN-MAX-FRAME-SIZE` constant.
    """
    constants: dict[str, str] = {}
    for path in files:
        for element in ElementTree.parse(path).getroot().iter("definition"):
            name = element.attrib.get("name")
            value = element.attrib.get("value")
            if name and value is not None:
                constants[name] = value
    return constants


def generate(artifacts_dir: Path, out_dir: Path) -> dict:
    clauses: list[dict] = []
    lowercase_only: list[dict] = []
    per_artifact: dict[str, dict] = {}

    files = load_artifacts(artifacts_dir)
    constants = collect_constants(files)

    for path in files:
        counters: dict[str, int] = {}
        before = len(clauses)
        root = ElementTree.parse(path).getroot()
        walk(root, [], path.name, counters, clauses, lowercase_only, constants)
        produced = clauses[before:]
        kinds: dict[str, int] = {}
        for clause in produced:
            kinds[clause["kind"]] = kinds.get(clause["kind"], 0) + 1
        per_artifact[path.name] = {
            "bytes": path.stat().st_size,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "anchors": len(counters),
            "statements": len(produced),
            "kinds": dict(sorted(kinds.items())),
            "must_class": sum(v for k, v in kinds.items() if k in ("MUST", "MUST NOT")),
            "audit": audit_ledger(root, produced),
        }

    clauses.sort(key=lambda c: c["ref"].split("#", 1)[0])
    clauses.sort(key=lambda c: (c["artifact"], c["anchor"], c["index"]))

    pictures: list[dict] = []
    for path in files:
        pictures.extend(collect_pictures(path, path.name))

    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "pictures.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "note": "Pictures are excluded from clause extraction. Those that contain formal "
                "grammar or normative keywords must carry a disposition: an exclusion is a "
                "decision, not a default.",
                "pictures": pictures,
            },
            indent=1,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (out_dir / "clauses.json").write_text(
        json.dumps({"schema_version": 1, "clauses": clauses}, indent=1, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / "lowercase-keywords.json").write_text(
        json.dumps(
            {
                "note": "Statements with no uppercase RFC 2119 keyword but lowercase "
                "must/should/may: a review signal, never clauses.",
                "statements": lowercase_only,
            },
            indent=1,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return {
        "per_artifact": per_artifact,
        "clauses": clauses,
        "lowercase_only": lowercase_only,
        "pictures": pictures,
    }


def disposition_files(directory: Path) -> list[Path]:
    if not directory.is_dir():
        return []
    return sorted(directory.glob("*.json"))


def load_dispositions(directory: Path) -> tuple[dict[str, dict], list[str]]:
    problems: list[str] = []
    merged: dict[str, dict] = {}
    for path in disposition_files(directory):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as error:
            problems.append(f"{path.name}: not valid JSON ({error})")
            continue
        for ref, entry in (data.get("dispositions") or {}).items():
            if ref in merged:
                problems.append(f"{path.name}: duplicate disposition for {ref}")
            value = entry.get("disposition", "")
            if value != "informative" and not value.startswith(DISPOSITION_PREFIXES):
                problems.append(
                    f"{path.name}: {ref}: disposition '{value}' is not one of "
                    "formalized:/deferred:/environment:/out-of-scope:/test:/superseded:/"
                    "underspecified:/informative"
                )
            if not entry.get("text_sha256"):
                problems.append(f"{path.name}: {ref}: missing text_sha256")
            merged[ref] = {**entry, "file": path.name}
    return merged, problems


def check_pictures(report: dict, dispositions: dict[str, dict]) -> list[str]:
    """Normative-looking pictures must carry a disposition, keyed to their content."""
    problems: list[str] = []
    for picture in report.get("pictures", []):
        if not picture["looks_normative"]:
            continue
        entry = dispositions.get(picture["ref"])
        if entry is None:
            problems.append(
                f"{picture['ref']}: picture contains {'/'.join(picture['matches'])} but has no "
                f"disposition — decide what carries its meaning ({picture['title'] or 'untitled'})"
            )
        elif entry["text_sha256"] != picture["content_sha256"]:
            problems.append(
                f"{picture['ref']}: STALE picture disposition — the picture text changed"
            )
    return problems


def coverage(report: dict, dispositions: dict[str, dict]) -> dict:
    clauses = report["clauses"]
    by_kind: dict[str, dict[str, int]] = {}
    undispositioned_must: dict[str, list[str]] = {}

    for clause in clauses:
        entry = by_kind.setdefault(clause["kind"], {"total": 0, "dispositioned": 0})
        entry["total"] += 1
        if clause["ref"] in dispositions:
            entry["dispositioned"] += 1
        elif clause["class"] == "MUST":
            undispositioned_must.setdefault(clause["anchor"], []).append(clause["ref"])

    by_disposition: dict[str, int] = {}
    for clause in clauses:
        entry = dispositions.get(clause["ref"])
        if not entry:
            continue
        key = entry["disposition"].split(":", 1)[0]
        by_disposition[key] = by_disposition.get(key, 0) + 1

    pictures = report.get("pictures", [])
    reviewable = [p for p in pictures if p["looks_normative"]]

    return {
        "schema_version": 1,
        "pictures": {
            "total": len(pictures),
            "reviewable": len(reviewable),
            "dispositioned": sum(1 for p in reviewable if p["ref"] in dispositions),
            "note": "Pictures are excluded from clause extraction; those containing formal grammar "
            "or normative keywords require a disposition, because an exclusion is a decision.",
        },
        "unkeyed": {
            "total": sum(1 for c in clauses if c["kind"] == "UNKEYED"),
            "dispositioned": sum(
                1 for c in clauses if c["kind"] == "UNKEYED" and c["ref"] in dispositions
            ),
            "note": "Statements that carry no conformance keyword but are still normative, or still "
            "an explicit silence the specification chooses. Captured because the keyword scan cannot "
            "see them: Part 1's duplicate-key rule is one sentence of a paragraph whose other "
            "sentences do carry keywords. Every one requires a disposition.",
        },
        "per_artifact": report["per_artifact"],
        "by_kind": dict(sorted(by_kind.items())),
        "by_disposition": dict(sorted(by_disposition.items())),
        "must_class_undispositioned": sum(len(v) for v in undispositioned_must.values()),
        "must_class_undispositioned_by_anchor": dict(
            sorted(undispositioned_must.items(), key=lambda kv: (-len(kv[1]), kv[0]))
        ),
        "lowercase_keyword_statements": len(report["lowercase_only"]),
        "totals": {
            "clauses": len(clauses),
            "anchors": sum(v["anchors"] for v in report["per_artifact"].values()),
            "must_class": sum(
                1 for c in clauses if c["class"] == "MUST"
            ),
        },
    }


def check_unkeyed(report: dict, dispositions: dict[str, dict]) -> list[str]:
    """Every keyword-free normative statement must carry a disposition.

    These are the statements the keyword scan cannot see. Leaving one
    undispositioned is how a requirement disappears while every gate stays green,
    so this check is unconditional rather than a report: the list is short by
    construction, and each entry is either an obligation somebody must carry or an
    explicit silence worth recording.
    """
    problems: list[str] = []
    for clause in report["clauses"]:
        if clause["kind"] != "UNKEYED" or clause["ref"] in dispositions:
            continue
        problems.append(
            f"{clause['ref']}: no conformance keyword, but states {'/'.join(clause['unkeyed_phrases'])} "
            f"— decide what carries it: {' '.join(clause['text'].split())[:110]}"
        )
    return problems


def check_dispositions(report: dict, dispositions: dict[str, dict]) -> list[str]:
    """Validate dispositions against the ledger, for clauses and pictures alike.

    A disposition is keyed to the digest of whatever it decided about: a clause's
    sentence, or a picture's content. Both live in one identity space, so a
    decision cannot attach to something that does not exist, and cannot survive a
    change to the text it was made about.
    """
    problems: list[str] = []
    known = {clause["ref"]: clause["text_sha256"] for clause in report["clauses"]}
    known.update({picture["ref"]: picture["content_sha256"] for picture in report.get("pictures", [])})
    stale = 0
    for ref, entry in sorted(dispositions.items()):
        digest = known.get(ref)
        if digest is None:
            problems.append(f"{entry['file']}: {ref}: no such clause or picture in the ledger")
            continue
        if entry["text_sha256"] != digest:
            stale += 1
            problems.append(
                f"{entry['file']}: {ref}: STALE disposition — the text it decides about changed\n"
                f"    disposition recorded for: {entry['text_sha256']}\n"
                f"    ledger now has:            {digest}"
            )
    if stale:
        problems.insert(
            0, f"{stale} stale disposition(s): the pinned text and the decisions disagree"
        )
    return problems


def disposition_values(entry: dict, prefix: str) -> list[str]:
    """The values of one disposition's `prefix:` claims, in the order written.

    A disposition is a `;`-separated set of decisions (`formalized:X; test:y`), so a
    value is read by prefix rather than by taking the whole string.
    """
    return [
        token.strip()[len(prefix):]
        for token in entry.get("disposition", "").split(";")
        if token.strip().startswith(prefix)
    ]


def declaration_spellings(namespace: list[str], written: list[str]) -> set[str]:
    """Every spelling a disposition may use for one declaration, and no other.

    Lean stores a declaration under its enclosing namespace joined to the name as
    written: `def Session.atState` inside `namespace SpecAMQP.Spec.Session` is
    `SpecAMQP.Spec.Session.Session.atState`. A disposition quotes the path a reader
    would write, and the ledger abbreviates in exactly two ways — it drops the root
    namespace (`Spec.Session.afterEnd`), and it writes the join once where the
    declaration repeats the namespace segment (`SpecAMQP.Spec.Session.atState`). Both
    are derived from the declaration here, because a rule that ignored the namespace
    would accept a path that names nothing at all.
    """
    paths = [namespace + written]
    if namespace:
        paths.append(namespace[1:] + written)
        if written and written[0] == namespace[-1]:
            paths.append(namespace + written[1:])
            paths.append(namespace[1:] + written[1:])
    return {".".join(path) for path in paths}


def lean_code_lines(text: str) -> list[tuple[int, str]]:
    """A module's lines as `(indent, code)`, with comments removed.

    Structure is read from code rather than quoted from documentation, so a
    constructor drawn in a docstring and a `| error e =>` arm inside a proof are both
    invisible here. Lean's block comments nest and docstrings are block comments, so
    this tracks depth rather than matching delimiters.
    """
    lines: list[tuple[int, str]] = []
    depth = 0
    for line in text.splitlines():
        code: list[str] = []
        index = 0
        while index < len(line):
            if depth == 0 and line.startswith("--", index):
                break
            if line.startswith("/-", index):
                depth += 1
                index += 2
                continue
            if depth and line.startswith("-/", index):
                depth -= 1
                index += 2
                continue
            if depth == 0:
                code.append(line[index])
            index += 1
        stripped = "".join(code)
        lines.append((len(stripped) - len(stripped.lstrip()), stripped))
    return lines


def lean_declarations(root: Path) -> dict[Path, set[str]]:
    """Declarations under `lean/**`, keyed by module, in every accepted spelling.

    The modules are read rather than the build: a name that is not in the tree the
    dispositions point at does not exist, however recently it was proved. The build
    directory is skipped — the sources under it belong to dependencies, not to this
    ledger. Constructors are declarations too: `Spec.Connection.Submission.frame`
    names the constructor `frame` of `inductive Submission`, and a scan that stopped
    at the inductive's own name would reject a correct disposition.
    """
    modules: dict[Path, set[str]] = {}
    for path in sorted(root.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        stack: list[tuple[str, list[str]]] = []
        names: set[str] = set()
        inductive: tuple[int, list[str], list[str]] | None = None
        for indent, code in lean_code_lines(path.read_text(encoding="utf-8")):
            if not code.strip():
                continue
            constructor = LEAN_CONSTRUCTOR_PATTERN.match(code)
            if inductive is not None and constructor is not None:
                names.update(
                    declaration_spellings(inductive[1], inductive[2] + [constructor.group(1)])
                )
                continue
            if inductive is not None and indent <= inductive[0]:
                inductive = None
            namespace = LEAN_NAMESPACE_PATTERN.match(code)
            if namespace:
                stack.append(("namespace", namespace.group(1).split(".")))
                continue
            section = LEAN_SECTION_PATTERN.match(code)
            if section:
                stack.append(("section", [section.group(1)] if section.group(1) else []))
                continue
            if LEAN_MUTUAL_PATTERN.match(code):
                stack.append(("mutual", []))
                continue
            end = LEAN_END_PATTERN.match(code)
            if end:
                closing = end.group(1)
                if closing:
                    for index in range(len(stack) - 1, -1, -1):
                        if ".".join(stack[index][1]) == closing:
                            del stack[index:]
                            break
                elif stack:
                    stack.pop()
                continue
            declaration = LEAN_DECLARATION_PATTERN.match(code)
            if declaration is None:
                continue
            enclosing = [
                segment for kind, frame in stack if kind == "namespace" for segment in frame
            ]
            written = declaration.group(2).split(".")
            names.update(declaration_spellings(enclosing, written))
            # A declaration's name may end in `?` or `!` — `reservedKey?`, `flowCountRefusal?` — and the
            # pattern above did not capture the suffix until a message-layer clause needed it: every
            # declaration was recorded truncated, which is why older entries name `flowCountRefusal`
            # where the declaration is `flowCountRefusal?`. Both spellings resolve now, the exact one and
            # the truncated one an entry written before this fix carries. **The leniency runs one way on
            # purpose**: a value naming the suffixed form is resolved by the declaration, while a value
            # naming a declaration the tree does not have still fails — which is the direction that
            # matters, since the check exists to refuse a `formalized:` nobody implemented.
            if written and written[-1][-1:] in "?!":
                names.update(
                    declaration_spellings(enclosing, written[:-1] + [written[-1][:-1]])
                )
            if declaration.group(1) == "inductive":
                inductive = (indent, enclosing, written)
        modules[path] = names
    return modules


def unresolved_module(value: str, root: Path, modules: dict[Path, set[str]]) -> str | None:
    """Why a module-spelled `formalized:` value names nothing, or None when it does."""
    match = LEAN_MODULE_PATTERN.match(value)
    if match is None:
        return (
            f"names neither a declaration nor a module under {root.name}/** — a module "
            "reference reads `lean/<path>.lean`, with an optional #declaration or :line anchor"
        )
    module = root / match.group(1)
    anchor = match.group(2) or ""
    if not module.is_file():
        return f"names no module under {root.name}/** — {match.group(1)} does not exist"
    if not anchor:
        return None
    named = LEAN_ANCHOR_NAME_PATTERN.match(anchor)
    if named:
        target = named.group(1)
        # The anchor is bounded by the module it names, so a declaration may be
        # written short (`#step`) or qualified (`#Session.atState`) — a spelling the
        # module does not declare, but whose tail names one of its declarations.
        if any(
            spelling == target or spelling.endswith("." + target)
            for spelling in modules.get(module, set())
        ):
            return None
        return f"names {match.group(1)}{anchor}, which declares no declaration by that name"
    lines = LEAN_ANCHOR_LINES_PATTERN.match(anchor)
    if lines:
        count = len(module.read_text(encoding="utf-8").splitlines())
        if int(lines.group(1)) <= int(lines.group(2) or lines.group(1)) <= count:
            return None
        return f"names {match.group(1)}{anchor}, but the module has {count} line(s)"
    return f"names {match.group(1)} with an anchor this check cannot read: {anchor}"


def unresolved_declaration(
    value: str, root: Path, declared: set[str], modules: dict[Path, set[str]]
) -> str | None:
    """Why `value` names no declaration under `lean/**`, or None when it does."""
    if "/" in value:
        return unresolved_module(value, root, modules)
    if value in declared:
        return None
    return (
        f"names no declaration under {root.name}/**: no def, theorem, structure, "
        "inductive or constructor declares it — correct the path to the declaration that "
        "carries the clause, or record the clause as deferred with the gap named. A "
        "conventions block declaring its values promises does not exempt this one: the "
        "exemption reaches a module the plan names and the tree lacks, and this module is "
        "not both"
    )


def formalized_conventions(directory: Path) -> dict[str, str]:
    """Each disposition file's own statement of what a `formalized:` value means."""
    statements: dict[str, str] = {}
    for path in disposition_files(directory):
        try:
            conventions = json.loads(path.read_text(encoding="utf-8")).get("conventions") or {}
        except json.JSONDecodeError:
            continue  # load_dispositions reports the unreadable file
        statements[path.name] = conventions.get(FORMALIZED_PREFIX, "")
    return statements


# The plan's own record of the modules it promises. `planned_modules` reads every
# module path PLAN.md writes down: the §9 architecture block names the S0-era set, and
# the milestone amendments name the modules that replaced them. The exemption's second
# half is read from this, so a module nobody planned cannot be promised.
PLAN_MODULE_PATTERN = re.compile(
    r"(?:lean/)?((?:Spec|Ref|Harness|Impl|Shell|Contracts|Proofs|Generated)/[\w.-]+\.lean)"
)


def planned_modules(root: Path) -> set[str]:
    """The module paths the plan names, relative to `lean/`, read as the tree it is.

    The plan writes its architecture as a tree — a directory line (`lean/Spec/`) and
    then a bare `Name.lean` per module — and elsewhere as a path. Both are read, the
    bare form bound to the directory line above it, because a reader of that block
    takes `Endpoint.lean` to mean `lean/Spec/Endpoint.lean`; a reader that ignored the
    block would find no module planned at all and would resolve every promise in the
    ledger against a tree those names do not occur in.
    """
    plan = root / "PLAN.md"
    if not plan.is_file():
        return set()
    named: set[str] = set()
    directory = ""
    fenced = False
    for line in plan.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if stripped.startswith("```"):
            fenced = not fenced
            directory = ""
            continue
        if not fenced:
            named.update(match.group(1).removeprefix("lean/") for match in PLAN_MODULE_PATTERN.finditer(line))
            continue
        header = re.fullmatch(r"(?:lean/)?([A-Za-z0-9_./-]+)/", stripped)
        if header is not None:
            directory = header.group(1)
            continue
        entry = re.match(r"([A-Za-z][\w]*\.lean)\b", stripped)
        if entry is not None:
            named.add(f"{directory}/{entry.group(1)}" if directory else entry.group(1))
    return named


def existing_modules(lean_root: Path) -> set[str]:
    """The module paths the tree holds, relative to `lean/`."""
    return {
        path.relative_to(lean_root).as_posix()
        for path in sorted(lean_root.rglob("*.lean"))
        if ".lake" not in path.parts
    }


def module_of_value(value: str, existing: set[str], planned: set[str]) -> tuple[str, str]:
    """The module a `formalized:` value names, and which record names it.

    Returns `(module, record)` where the record is `tree`, `plan` or `none`. A
    module-spelled value (`lean/Spec/Session.lean#step`) carries its module in the path.
    A dotted one is read against the records, longest candidate first: the segments
    before the declaration, taken as module paths from the longest down, so
    `Spec.Value.MapOrdering` names `Spec/Value.lean` and
    `SpecAMQP.Spec.Transactions.Layer.retireAll` names `Spec/Transactions.lean` even
    though `Layer` is a namespace inside it. A value whose segments name nothing in
    either record is reported as `none` — the honest answer for a path like
    `SpecAMQP.Contracts.<name>`, where the spelling names a namespace rather than the
    module that holds the declaration. Both records are read because both are records:
    the tree says what exists to resolve against, the plan says what was promised
    before it did.
    """
    match = LEAN_MODULE_PATTERN.match(value)
    if match is not None:
        module = match.group(1).removeprefix("lean/")
        record = "tree" if module in existing else ("plan" if module in planned else "none")
        return module, record
    segments = value.split(".")
    if len(segments) > 1 and segments[0] == "SpecAMQP":
        segments = segments[1:]
    candidates = ["/".join(segments[:index]) + ".lean" for index in range(len(segments) - 1, 0, -1)]
    for module in candidates:
        if module in existing:
            return module, "tree"
    for module in candidates:
        if module in planned:
            return module, "plan"
    return (candidates[0] if candidates else f"{value}.lean"), "none"


def formalized_claims(
    dispositions: dict[str, dict], directory: Path, root: Path
) -> list[tuple[str, str, str, str]]:
    """Every `formalized:` claim, with the standing its own file gives it.

    Returns `(standing, file, ref, value)`. The standings are `present` when a file
    documents the vocabulary without declaring its values promises, `undeclared` when
    it carries `formalized:` values while documenting no convention at all — which the
    check output reports by name rather than assuming either way — and, for a file that
    does declare its values promises, three standings the two records below decide
    between: `commitment` (exempt), `demoted` (the exemption no longer applies, so the
    value is resolved like any other) and `unplanned` (a promise no record names,
    resolved because resolving it is the only way to find out whether it means
    anything).

    **The exemption is scoped by the record rather than by the word.** A conventions
    block declares its values promises the plan lands later, and the justification is
    in its own parenthesis: nothing in the tree to resolve against. That is checkable,
    so it is checked. A value is exempt only while the module it names is absent from
    the tree, and only if the plan names that module. A module the tree holds means
    there *is* something to resolve against, and the value must resolve like any other
    — a declaration that module never declared is a false claim however the file's
    conventions read, which is the shape this rule was written after finding: a
    disposition whose note asserted a picture's rule was carried by
    `formalized:Spec.Message.resumedTransfer`, a declaration no commit ever created,
    exempt because its file's conventions used the word.

    What the scope does not reach is stated rather than implied: a module the plan
    names and the tree lacks is still exempt, because a planned module has no
    declaration yet by definition — so a value whose module was planned under one name
    and built under another stays exempt until the plan's own record is corrected.
    """
    conventions = formalized_conventions(directory)
    plan = planned_modules(root)
    existing = existing_modules(root / "lean")
    claims: list[tuple[str, str, str, str]] = []
    for ref, entry in sorted(dispositions.items()):
        declared = conventions.get(entry["file"], "")
        promises = any(marker in declared for marker in FORWARD_COMMITMENT_MARKERS)
        for value in disposition_values(entry, FORMALIZED_PREFIX):
            module, record = module_of_value(value, existing, plan)
            if not declared:
                standing = "undeclared"
            elif not promises:
                standing = "present"
            elif record == "tree":
                standing = "demoted"
            elif record == "plan":
                standing = "commitment"
            else:
                standing = "unplanned"
            claims.append((standing, entry["file"], ref, value))
    return claims


def formalized_census(
    dispositions: dict[str, dict], directory: Path, root: Path
) -> tuple[int, int, dict[str, int], int, int]:
    """What the gate resolves, what the record exempts, and what declares nothing.

    Returns `(checked, commitments, undeclared, demoted, unplanned)`: the number of
    values the gate resolves, the number still exempt as commitments, the count per
    file of values in a file that documents no `formalized:` convention, the number
    whose exemption was withdrawn because the module they name is in the tree, and the
    number that name a module no record names. A commitment is a property of the claim
    rather than of the file it sits in, so the declaration counts wherever the value is
    written. The counts are printed by `check`, because an exemption nobody can see is
    the failure this file exists to remove — and an exemption with a scope nobody can
    see is the same failure one level out.
    """
    claims = formalized_claims(dispositions, directory, root)
    committed = {value for standing, _, _, value in claims if standing == "commitment"}
    checked = sum(
        1
        for standing, _, _, value in claims
        if standing != "commitment" and value not in committed
    )
    commitments = sum(1 for _, _, _, value in claims if value in committed)
    undeclared: dict[str, int] = {}
    for standing, file, _, value in claims:
        if standing == "undeclared":
            undeclared[file] = undeclared.get(file, 0) + 1
    demoted = sum(1 for standing, _, _, value in claims if standing == "demoted")
    unplanned = sum(1 for standing, _, _, value in claims if standing == "unplanned")
    return checked, commitments, undeclared, demoted, unplanned


def check_resolves(
    dispositions: dict[str, dict], directory: Path, root: Path, required: bool
) -> list[str]:
    """Every `formalized:` value declared present must name a declaration that exists.

    This is the claim no other gate can see: the text hash still matches, the picture
    is still reviewed, the coverage report still counts the clause as decided — and
    the declaration the disposition points at is not in the tree. The gate reads the
    repository's own modules, and a fixture ledger has no tree beside it, so the rule
    is stated where it can be read, like the baseline reconciliation.
    """
    if not required:
        return []
    lean_root = root / "lean"
    if not lean_root.is_dir():
        return [f"{lean_root}: the module tree every formalized: value claims is missing"]
    modules = lean_declarations(lean_root)
    declared = set().union(*modules.values()) if modules else set()
    claims = formalized_claims(dispositions, directory, root)
    committed = {value for standing, _, _, value in claims if standing == "commitment"}
    problems: list[str] = []
    for standing, file, ref, value in claims:
        if standing == "commitment" or value in committed:
            continue
        reason = unresolved_declaration(value, lean_root, declared, modules)
        if reason is not None:
            problems.append(f"{file}: {ref}: formalized:{value} {reason}")
    return problems


def check_carries(dispositions: dict[str, dict], vectors_dir: Path, required: bool) -> list[str]:
    """Every `test:` value must name a vector that exists in the corpus tree.

    A vector id is the ledger's handle on an observable: the disposition says the
    clause is witnessed by that vector's verdict. A vector renamed or never generated
    leaves the claim unwitnessed while the disposition still reads as decided. There
    is no exemption here, because a `test:` value names something the repository
    already commits to: it resolves or it is wrong.

    The corpus is read whole rather than at the top level alone. The message and
    exchange families write into subdirectories, so a glob of `*.ndjson` would report
    a legitimate disposition as pointing at nothing — a false failure whose message
    says the id does not resolve, which is the hardest kind to attribute. Measured
    before the change: a `test:` value naming `msg-bare-properties-data` (which exists
    in `vectors/message/messages.ndjson`) was reported as "no vector in
    vectors/*.ndjson".
    """
    if not required:
        return []
    if not vectors_dir.is_dir():
        return [f"{vectors_dir}: the vector corpus every test: value claims is missing"]
    ids = set().union(*corpus_ids(vectors_dir).values())
    problems: list[str] = []
    for ref, entry in sorted(dispositions.items()):
        for value in disposition_values(entry, TEST_PREFIX):
            if value not in ids:
                problems.append(
                    f"{entry['file']}: {ref}: test:{value} is no vector under "
                    f"{vectors_dir.name}/"
                )
    return problems


CORPUS_REFERENCE_PATTERN = re.compile(r"vectors/[\w./-]+\.ndjson")
BACKTICKED_TOKEN_PATTERN = re.compile(r"`([^`]+)`")
WORD_PATTERN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

# The words a note may quote as vocabulary rather than as a name. The prefixes are the
# disposition values' own forms — `deferred:S4` names a milestone, `test:` is a prefix
# quoted for what it is — and `informative` is the one value with no prefix. A token
# that resolves against these is read as vocabulary and not as a cited vector.
LEDGER_VOCABULARY = (*DISPOSITION_PREFIXES, "informative")


def ledger_strings(root: Path):
    """Every string in every JSON document under `root`, with file and JSON path.

    The ledger's documents have several shapes — a list of clauses, a mapping of refs, a
    document with a file-level conventions block — and the record that started this check
    lived in two of them at once: a per-clause `note` and a file-level
    `design_consequences`. Walking the documents rather than a schema is what lets the
    check see all of a ledger's prose, and the trail it carries is what a report quotes.
    """
    for path in sorted(root.rglob("*.json")):
        try:
            document = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue  # a malformed file is another check's problem

        def walk(node, trail: tuple[str, ...]):
            if isinstance(node, str):
                yield trail, node
            elif isinstance(node, list):
                for index, item in enumerate(node):
                    yield from walk(item, (*trail, str(index)))
            elif isinstance(node, dict):
                for key, item in node.items():
                    yield from walk(item, (*trail, str(key)))

        for trail, text in walk(document, (str(path),)):
            yield "/".join(trail), text


def corpus_ids(vectors_dir: Path) -> dict[str, set[str]]:
    """Every vector id, by the corpus file that holds it, for every corpus under the tree.

    The corpus tree is read whole. The message and exchange families write into
    subdirectories, and a reader that globbed the top level alone would report a correct
    name as absent — which is why `check_carries` resolves `test:` values against this
    rather than against a top-level glob.
    """
    corpora: dict[str, set[str]] = {}
    for path in sorted(vectors_dir.rglob("*.ndjson")):
        relative = str(path.relative_to(vectors_dir.parent))
        corpora[relative] = {
            json.loads(line).get("vector")
            for line in path.read_text(encoding="utf-8").splitlines()
            if line.strip()
        }
    return corpora


def corpus_named_strings(root: Path) -> list[tuple[str, str]]:
    """Every ledger string that names a corpus file, with where it sits."""
    return [
        (where, text)
        for where, text in ledger_strings(root)
        if CORPUS_REFERENCE_PATTERN.search(text)
    ]


def lean_words(root: Path) -> set[str]:
    """Every whole word under `lean/**`: the vocabulary a note may quote as a name.

    A note discussing the code it is about names things that no corpus holds and no disposition
    defines: `position.deliveryCount` is a field of `position`, `hdrExch` is a constructor, and a
    check that knows only corpus ids and ledger names reports the repository's own identifiers as
    broken citations — 34 of them when this was measured, every one a false positive.

    The vocabulary is therefore read from the tree rather than listed, and the last dotted segment of
    a token is what gets looked up, so a qualified name resolves by the name it ends in. The build
    directory is skipped exactly as `lean_declarations` skips it, and it matters more here than there:
    a dependency's words would resolve anything, because `resumedTransfer` and `hdrExch` alike would
    have a namesake in mathlib.
    """
    words: set[str] = set()
    for path in sorted(root.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        words.update(WORD_PATTERN.findall(path.read_text(encoding="utf-8")))
    return words


def check_note_names(root: Path, vectors_dir: Path, lean_root: Path, report: dict) -> list[str]:
    """Every vector a ledger note names must be a vector that exists.

    A note is evidence, and evidence that names an artifact is only evidence if the
    artifact is there: a disposition saying two vectors carry a clause is read by whoever
    audits that clause, and if the ids do not exist they find nothing while the note still
    reads as a witness. `check_carries` resolves the `test:` a disposition *claims*; the
    citation gate resolves the clauses a *vector* cites; this is the third direction — what
    a note says beside a corpus — and it was invisible until a disposition named two ids
    that had never existed, in prose, where no check was reading.

    The rule is not "anything vector-shaped", because that would guess at the boundary and
    fail on the ledger's own vocabulary. A backticked token is resolved against the
    namespaces that are already here: the ids of the corpus the note names, the ledger's
    clause and picture refs, the ambiguity register's ids, and the disposition values'
    forms. Measured against the ledger as it stood, the literal reading — every token must
    be an id in the named corpus — flagged `test:` and `deferred:S4`, both vocabulary, and
    nothing else; resolving them as vocabulary is what fixed this shape, and a note that
    cites a clause or quotes a value form is read as what it is. A `test:<id>` token is
    *not* re-validated here: that value's own check owns it, and duplicating the rule
    would give a rename two places to fail.

    A note may also quote the repository's own vocabulary, which is not a citation failure but the
    opposite: the vocabulary is every whole word under `lean/**`, and a token resolves when its last
    dotted segment is one of them, so `position.deliveryCount` is read as the field it names. A token
    beginning with a dot is a fragment of an id the note is discussing, and is not a name at all.
    Measured against the ledger as it stood, the literal reading flagged 34 tokens of this shape, every
    one a false positive; the vocabulary rule drops all of them and keeps the catch this check exists
    for — `Spec.Message.resumedTransfer` resolves nowhere, because that declaration was never created.

    Unlike the existence gates, this one is not restricted to the repository's ledger: it
    compares a ledger's prose with a corpus on disk, and both are readable from a fixture
    directory, so a planted note in a fixture exercises it. That is deliberate — a check
    that can only ever see the passing direction is the failure this repository keeps
    finding.
    """
    corpora = corpus_ids(vectors_dir)
    known = {clause["ref"] for clause in report["clauses"]}
    known.update(picture["ref"] for picture in report.get("pictures", []))
    register = root / "ambiguities"
    if register.is_dir():
        known.update(path.stem for path in register.glob("*.json"))
    vocabulary = lean_words(lean_root)

    problems: list[str] = []
    for where, text in corpus_named_strings(root):
        named = set(CORPUS_REFERENCE_PATTERN.findall(text))
        for token in BACKTICKED_TOKEN_PATTERN.findall(text):
            # A citation is a single word: no vector id and no name this ledger defines contains
            # whitespace. A multi-word span is prose or code being *quoted* — `set == session.peerBegun`,
            # `delivery.settled || settled` — and reading those as failed citations is a false positive,
            # which is worse than no check: the failure is real and it points at the wrong thing.
            if any(c.isspace() for c in token):
                continue
            # A token that begins with a dot is a *fragment* — `.3`, `.1` — the tail of a clause id the
            # note is discussing, not a name in its own right.
            if token.startswith("."):
                continue
            if CORPUS_REFERENCE_PATTERN.fullmatch(token):
                continue  # a corpus named in backticks is a file, not a vector
            if token in known or token in LEDGER_VOCABULARY:
                continue
            if any(token.startswith(prefix) for prefix in DISPOSITION_PREFIXES):
                continue
            if any(token in corpora.get(name, set()) for name in named):
                continue
            # The vocabulary a note may quote is the repository's own, and the last dotted segment is
            # the name: `position.deliveryCount` is a field of `position`, which the Lean tree declares.
            # This is what keeps the check's real catch while dropping its false ones — a note citing
            # `Spec.Message.resumedTransfer` still fails, because that declaration is nowhere in the tree.
            if token.rsplit(".", 1)[-1] in vocabulary:
                continue
            problems.append(
                f"{where}: names {', '.join(sorted(named))} but cites {token!r}, which is "
                f"no vector id in it and no name this ledger defines"
            )
    return problems


def check_ambiguities(report: dict, dispositions: dict[str, dict], path: Path) -> list[str]:
    """Validate the ambiguity register against the ledger it cites.

    The register is where a clause whose reading is genuinely open gets decided, and
    a disposition may cite a decision by id (`superseded:<id>`, `underspecified:<id>`).
    Unvalidated, it is documentation that drifts: a decision id nobody can find, a clause
    that was reworded, a reading list with one entry. These are cheap invariants and they
    are the difference between a register and a folder.

    The ids a disposition *cites* are resolved here too, and that half was missing: the
    register was validated against itself and the ledger, while the values pointing into it
    were exempt — the same shape as a `formalized:` naming a declaration nobody created, in
    the one namespace where the pointer *is* the whole content of the value. Three sites
    naming two ids that did not exist survived several green runs of this check before a
    disposition audit read them by hand. Resolution is not conditional on the register
    existing: a citation into a directory that is not there resolves nowhere, and saying so
    is the point.
    """
    problems: list[str] = []
    known = {clause["ref"] for clause in report["clauses"]}
    known.update({picture["ref"] for picture in report.get("pictures", [])})
    seen: dict[str, str] = {}
    for file in sorted(path.glob("*.json")):
        document = json.loads(file.read_text(encoding="utf-8"))
        identifier = document.get("id")
        if identifier != file.stem:
            problems.append(f"{file.name}: id {identifier!r} does not match the file name")
        if identifier in seen:
            problems.append(f"{file.name}: duplicate ambiguity id {identifier!r}, also in {seen[identifier]}")
        seen[identifier] = file.name
        readings = document.get("readings") or []
        names = [reading.get("name") for reading in readings]
        if len(readings) < 2:
            problems.append(f"{file.name}: an ambiguity needs at least two readings to be one")
        for reading in readings:
            if not reading.get("statement"):
                problems.append(f"{file.name}: reading {reading.get('name')!r} states nothing")
        if document.get("adopted") not in names:
            problems.append(
                f"{file.name}: adopted {document.get('adopted')!r} is not one of the readings "
                f"{names}"
            )
        if not isinstance(document.get("open"), bool):
            problems.append(f"{file.name}: `open` must be a boolean")
        for ref in document.get("clauses", []):
            if ref not in known:
                problems.append(f"{file.name}: cites {ref}, which is not a clause or picture in the ledger")
    for ref, entry in dispositions.items():
        value = entry.get("disposition", "")
        for prefix in ("superseded:", "underspecified:"):
            if value.startswith(prefix) and value[len(prefix) :] not in seen:
                problems.append(
                    f"{entry.get('file', '?')}: {ref}: {value} cites a decision that is not in "
                    f"{path} (a value in this namespace resolves nowhere else)"
                )
    return problems


def check_reconciliation(report: dict, path: Path, required: bool) -> list[str]:
    """Verify the recorded baseline reconciliation still matches the ledger.

    `ledger/reconciliation.json` explains every difference between the crude
    baseline scan in PLAN.md §1 and this ledger. If the ledger moves, the record
    is stale and must be revised deliberately rather than drifting.
    """
    if not path.is_file():
        # The reconciliation record explains the repository ledger against the
        # baseline scan in PLAN.md §1. Fixture ledgers have no baseline, so the
        # requirement is stated rather than assumed.
        return [f"{path.name}: missing baseline reconciliation record"] if required else []
    record = json.loads(path.read_text(encoding="utf-8"))
    problems: list[str] = []
    known_mechanisms = set(record.get("mechanisms", {}))

    recorded = record.get("artifacts", {})
    actual = report["per_artifact"]
    for name in sorted(set(recorded) | set(actual)):
        if name not in recorded:
            problems.append(f"{path.name}: {name} is missing from the reconciliation record")
            continue
        if name not in actual:
            problems.append(f"{path.name}: {name} is recorded but no longer present")
            continue
        entry = actual[name]
        kinds = entry["kinds"]
        expected = {
            "statements": entry["statements"],
            "must_class": entry["must_class"],
            "must": kinds.get("MUST", 0),
            "must_not": kinds.get("MUST NOT", 0),
            "should": kinds.get("SHOULD", 0),
            "should_not": kinds.get("SHOULD NOT", 0),
            "may": kinds.get("MAY", 0),
        }
        for key, value in expected.items():
            if recorded[name]["ledger"].get(key) != value:
                problems.append(
                    f"{path.name}: {name}: recorded ledger {key}={recorded[name]['ledger'].get(key)} "
                    f"but the ledger now reports {value} — revise the reconciliation deliberately"
                )
        for difference in recorded[name].get("differences", []):
            for mechanism in difference.get("explained_by", []):
                if mechanism not in known_mechanisms:
                    problems.append(
                        f"{path.name}: {name}: unexplained difference mechanism '{mechanism}'"
                    )
    return problems


def command_generate(args: argparse.Namespace) -> int:
    report = generate(Path(args.artifacts), Path(args.out))
    summary = coverage(report, load_dispositions(Path(args.dispositions))[0])
    (Path(args.out) / "coverage.json").write_text(
        json.dumps(summary, indent=1, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(f"clauses: {summary['totals']['clauses']} across {summary['totals']['anchors']} anchors")
    print(f"must-class: {summary['totals']['must_class']}")
    for kind, entry in summary["by_kind"].items():
        print(f"  {kind:<14} {entry['total']:>4}  dispositioned {entry['dispositioned']:>4}")
    print(f"undispositioned must-class: {summary['must_class_undispositioned']}")
    print(f"lowercase-keyword statements (review signal): {summary['lowercase_keyword_statements']}")
    print(f"wrote {Path(args.out) / 'clauses.json'}")
    print(f"wrote {Path(args.out) / 'coverage.json'}")
    return 0


def command_check(args: argparse.Namespace) -> int:
    report = generate(Path(args.artifacts), Path(args.out))
    dispositions, problems = load_dispositions(Path(args.dispositions))
    summary = coverage(report, dispositions)
    (Path(args.out) / "coverage.json").write_text(
        json.dumps(summary, indent=1, sort_keys=True) + "\n", encoding="utf-8"
    )
    problems.extend(check_dispositions(report, dispositions))
    problems.extend(check_pictures(report, dispositions))
    problems.extend(check_unkeyed(report, dispositions))
    problems.extend(check_ambiguities(report, dispositions, Path(Path(args.out) / "ambiguities")))
    repository = Path(__file__).resolve().parent.parent
    repository_artifacts = (repository / "spec" / "oasis").resolve()
    problems.extend(
        check_reconciliation(
            report,
            Path(args.out) / "reconciliation.json",
            required=Path(args.artifacts).resolve() == repository_artifacts,
        )
    )
    # The existence gates read the tree beside the ledger. A fixture ledger is about a
    # planted artifact rather than about this tree, so the rules are stated for the
    # repository's own record — the shape the reconciliation check already uses.
    repository_dispositions = (repository / "ledger" / "dispositions").resolve()
    dispositions_required = Path(args.dispositions).resolve() == repository_dispositions
    problems.extend(
        check_resolves(dispositions, Path(args.dispositions), repository, dispositions_required)
    )
    problems.extend(check_carries(dispositions, repository / "vectors", dispositions_required))
    # The note check compares the ledger's prose with the corpus on disk, and both are
    # readable from any ledger directory, so it is deliberately not restricted to the
    # repository's own ledger: a planted note in a fixture exercises it, which is what
    # keeps a name-resolving check from only ever seeing the passing direction.
    problems.extend(check_note_names(Path(args.out), repository / "vectors", repository / "lean", report))

    for name, entry in sorted(report["per_artifact"].items()):
        audit = entry["audit"]
        if audit["mismatches"]:
            problems.append(
                f"{name}: keyword tokens escape the ledger: {json.dumps(audit['mismatches'])}"
            )
            for snippet in audit["unledgered_text"][:4]:
                problems.append(
                    f"    unledgered prose in {snippet['element']}: {snippet['text']}"
                )

    print(f"clauses: {summary['totals']['clauses']}, must-class: {summary['totals']['must_class']}")
    print(
        f"dispositions: {len(dispositions)} in {len(disposition_files(Path(args.dispositions)))} file(s)"
    )
    print(f"undispositioned must-class: {summary['must_class_undispositioned']}")
    if summary["must_class_undispositioned"]:
        print("undispositioned must-class clauses by anchor (largest first):")
        for anchor, refs in list(summary["must_class_undispositioned_by_anchor"].items())[:12]:
            print(f"  {len(refs):>3}  {anchor}")
    if dispositions_required:
        checked, commitments, undeclared, demoted, unplanned = formalized_census(
            dispositions, Path(args.dispositions), repository
        )
        print(
            f"formalized: {checked} checked against lean/**, "
            f"{commitments} forward commitment(s) exempt by the record"
        )
        if demoted:
            print(
                f"formalized: {demoted} value(s) whose module the tree holds: the exemption "
                "no longer reaches them, and they are resolved above"
            )
        if unplanned:
            print(
                f"formalized: {unplanned} value(s) name a module no record names: resolved, "
                "not exempt"
            )
        for name, count in sorted(undeclared.items()):
            print(
                f"formalized: {name}: {count} value(s) in a file documenting no "
                "formalized: convention"
            )
        tests = sum(len(disposition_values(entry, TEST_PREFIX)) for entry in dispositions.values())
        print(f"test: {tests} vector id(s) checked against vectors/**/*.ndjson")
        named = corpus_named_strings(Path(args.out))
        tokens = sum(
            len([
                token
                for token in BACKTICKED_TOKEN_PATTERN.findall(text)
                if not CORPUS_REFERENCE_PATTERN.fullmatch(token)
            ])
            for _, text in named
        )
        print(
            f"notes: {len(named)} ledger string(s) name a corpus, {tokens} backticked "
            f"token(s) besides the paths resolved in them"
        )

    if problems:
        print("")
        for problem in problems:
            print(f"problem: {problem}")
        print(f"check FAILED: {len(problems)} problem(s)")
        return 1
    print("check passed")
    return 0


def main(argv: list[str]) -> int:
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", choices=("generate", "check"))
    parser.add_argument("--artifacts", default=str(root / "spec" / "oasis"))
    parser.add_argument("--out", default=str(root / "ledger"))
    parser.add_argument("--dispositions", default=str(root / "ledger" / "dispositions"))
    args = parser.parse_args(argv)
    return command_generate(args) if args.command == "generate" else command_check(args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
