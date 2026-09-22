#!/usr/bin/env python3
"""Extract the normative statements of the pinned OASIS AMQP 1.0 artifacts.

    scripts/clause-ledger.py generate [--artifacts DIR] [--out DIR]
    scripts/clause-ledger.py check    [--artifacts DIR] [--out DIR] [--dispositions DIR]

`generate` walks the pinned XML in document order and emits one record per
normative statement, plus a coverage report. `check` validates the disposition
files against the generated ledger and reports undispositioned MUST-class
clauses; it exits non-zero on any problem.

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
    "environment:",
    "out-of-scope:",
    "test:",
    "superseded:",
)

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
    """
    tokens: list[str] = []

    def add(text: str | None) -> None:
        if text:
            tokens.extend(text.split())

    if element.tag == "xref" and element.attrib.get("name"):
        name = element.attrib["name"]
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
            emit_statements(tokens, stack, artifact, counters, clauses, lowercase_only, refs)

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

    if not find_keywords(tokens) and re.search(r"\b(must|should|may)\b", text):
        lowercase_only.append(
            {
                "artifact": artifact,
                "anchor": path,
                "text": text if len(text) <= 240 else text[:237] + "...",
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

    out_dir.mkdir(parents=True, exist_ok=True)
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
    return {"per_artifact": per_artifact, "clauses": clauses, "lowercase_only": lowercase_only}


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
                    "formalized:/environment:/out-of-scope:/test:/superseded:/informative"
                )
            if not entry.get("text_sha256"):
                problems.append(f"{path.name}: {ref}: missing text_sha256")
            merged[ref] = {**entry, "file": path.name}
    return merged, problems


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

    return {
        "schema_version": 1,
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


def check_dispositions(report: dict, dispositions: dict[str, dict]) -> list[str]:
    problems: list[str] = []
    known = {clause["ref"]: clause for clause in report["clauses"]}
    stale = 0
    for ref, entry in sorted(dispositions.items()):
        clause = known.get(ref)
        if clause is None:
            problems.append(f"{entry['file']}: {ref}: no such clause in the ledger")
            continue
        if entry["text_sha256"] != clause["text_sha256"]:
            stale += 1
            problems.append(
                f"{entry['file']}: {ref}: STALE disposition — the clause text changed\n"
                f"    disposition recorded for: {entry['text_sha256']}\n"
                f"    ledger now has:            {clause['text_sha256']}\n"
                f"    ledger text: {clause['text']}"
            )
    if stale:
        problems.insert(
            0, f"{stale} stale disposition(s): the pinned text and the decisions disagree"
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
    repository_artifacts = (Path(__file__).resolve().parent.parent / "spec" / "oasis").resolve()
    problems.extend(
        check_reconciliation(
            report,
            Path(args.out) / "reconciliation.json",
            required=Path(args.artifacts).resolve() == repository_artifacts,
        )
    )

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
