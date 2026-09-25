#!/usr/bin/env python3
"""The exchange corpus: the connection lifecycle as ordered steps.

    scripts/gen-exchange-vectors.py [--out vectors/generated-exchanges.ndjson]
                                    [--mutations PATH]

This script is the corpus's command line and nothing else: it owns the flags, the output
paths and the report, and dispatches the families — the connection and session families,
the widening family the corpus carries, and the mutation controls that are meant to fail —
to `scripts/gen/slices.py`. The split exists so that two slices can add corpus families in
the same wave without editing one file: a family is a module there plus one dispatch line
here.

`--out` is the corpus a gate runs: the connection and session families pass in both
artefacts, and the widening family is the failure-first evidence for PLAN.md §24's
`deferred:S4` obligations — red in both until the widened model lands, and deliberately not
weakened to keep a gate green.

`--mutations` writes the control family to a path the caller names rather than into the
corpus: a control asserts what the artifact forbids and is meant to fail, so it cannot live
in a corpus a gate requires to pass.

What the exchange expectations are authored from, and which artifact tables they read,
is stated in the module that holds the family.
"""

from __future__ import annotations

import argparse
import pathlib
import sys

# The families are a package beside this script. Running a script puts its own
# directory on `sys.path` already; saying so keeps the import working when that
# convention is switched off (python3 -P, or PYTHONSAFEPATH=1).
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from gen import slices, write_ndjson

ROOT = pathlib.Path(__file__).resolve().parent.parent


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", default=str(ROOT / "vectors" / "generated-exchanges.ndjson"),
                        help="where the exchange corpus is written")
    parser.add_argument("--mutations", default=None, metavar="PATH",
                        help="also write the mutation controls — vectors that assert "
                             "what the artifact does not permit and are therefore meant "
                             "to fail — to PATH")
    args = parser.parse_args(argv)

    tables = slices.Corpus()
    vectors = slices.corpus(tables) + slices.session_corpus(tables) + slices.widening_corpus(tables)
    digest = write_ndjson(pathlib.Path(args.out), vectors)
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
        controls = slices.mutation_corpus(tables)
        control_digest = write_ndjson(pathlib.Path(args.mutations), controls)
        print(f"generated {len(controls)} mutation controls into {args.mutations}")
        print(f"  sha256: {control_digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
