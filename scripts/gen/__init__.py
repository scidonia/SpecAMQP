"""The corpus generators, one module per family.

`scripts/gen/` holds the corpus families, and the two corpus entry points are thin
command lines that dispatch to them: they own the flags, the output paths and the
report, while the family — what vectors exist and where each expectation comes from —
lives here, one file per family.

| Module | Family | Written by |
| --- | --- | --- |
| `gen/values.py` | the value corpus: the Part 1 encoder, its self-check against the artifact's worked examples, and the golden, reject, property and element families | `scripts/gen-value-vectors.py --out` |
| `gen/frames.py` | the frame corpus: every performative in both directions, the size and DOFF boundaries, and the layout's malformed arithmetic | `scripts/gen-value-vectors.py --frames` |
| `gen/slices.py` | the per-slice exchange corpora: the connection and session families, and the mutation controls that are meant to fail | `scripts/gen-exchange-vectors.py` |

The split exists so that two slices can add corpus families in the same wave without
editing one file: a new family is a module here plus one dispatch line in whichever
entry point writes its output, rather than a merge conflict inside a thousand-line
script. A family's expectations are authored from the clauses or from recordings, never
produced by running the executable specification, and the module that holds them is
where that provenance is written down — so a family's module is also the place to read
before adding to it.

`write_ndjson` is the one thing the families share: the corpus file format. It lives
here rather than in one family so that the format is stated once for all of them.
"""

from __future__ import annotations

import hashlib
import json
import pathlib


def write_ndjson(path: pathlib.Path, vectors: list[dict]) -> str:
    """Write the corpus: one JSON object per line, keys sorted, a trailing newline.

    Returns the SHA-256 of the octets written, which is what an entry point reports and
    what a contract compares against the committed corpus.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    text = "\n".join(json.dumps(v, sort_keys=True) for v in vectors) + "\n"
    path.write_text(text, encoding="utf-8")
    return hashlib.sha256(text.encode("utf-8")).hexdigest()
