#!/usr/bin/env python3
"""Generate a large value corpus for the reference implementation and the specification.

    scripts/gen-value-vectors.py [--out vectors/generated.ndjson] [--frames PATH]
                                 [--messages PATH]

This script is the corpus's command line and nothing else: it owns the flags, the output
paths and the report, and dispatches the families to `scripts/gen/` — the value corpus to
`gen/values.py`, the frame corpus to `gen/frames.py` when `--frames` names a path, the
message corpus to `gen/messages.py` when `--messages` does, and the fragmentation adequacy
control to `gen/flows.py` when `--flow` or `--flow-negative` does.
The split exists so that two slices can add corpus families in the same wave without
editing one file: a family is a module there plus one dispatch line here.

What each family's expectations are authored from, and why none of them is produced by
running either Lean artefact, is stated in the module that holds the family.
"""

from __future__ import annotations

import argparse
import hashlib
import pathlib
import sys

# The families are a package beside this script. Running a script puts its own
# directory on `sys.path` already; saying so keeps the import working when that
# convention is switched off (python3 -P, or PYTHONSAFEPATH=1).
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from gen import flows, frames, messages, slices, values, write_ndjson

ROOT = pathlib.Path(__file__).resolve().parent.parent


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", default=str(ROOT / "vectors" / "generated.ndjson"))
    parser.add_argument("--limit-properties", type=int, default=None,
                        help="emit only the first N property vectors, for a quick pass")
    parser.add_argument("--frames", default=None, metavar="PATH",
                        help="also emit the frame corpus (every performative in both "
                             "directions, the size and DOFF boundaries, the layout's "
                             "malformed arithmetic and the mutation controls) to PATH")
    parser.add_argument("--messages", default=None, metavar="PATH",
                        help="also emit the message corpus (every descriptor code, the "
                             "payload and item-count boundaries, the annotation key rules "
                             "and the delivery states) to PATH")
    parser.add_argument("--flow", default=None, metavar="PATH",
                        help="also emit the fragmentation adequacy control (one message at "
                             "every interior split point the artifact permits, plus the "
                             "three-transfer compositions) to PATH")
    parser.add_argument("--flow-negative", default=None, metavar="PATH",
                        help="also emit the fragmentation negatives (the split points the "
                             "artifact does not permit) to PATH")
    args = parser.parse_args(argv)

    values.self_check()
    corpus = values.corpus(args.limit_properties)
    out = pathlib.Path(args.out)
    digest = write_ndjson(out, corpus)
    counts: dict[str, int] = {}
    for vector in corpus:
        counts[vector["kind"]] = counts.get(vector["kind"], 0) + 1
    print(f"generated {len(corpus)} vectors into {out}")
    print("  kinds: " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    print(f"  artifact: {hashlib.sha256(values.ARTIFACT.read_bytes()).hexdigest()[:16]}… "
          f"(the table the encoder was read from)")
    print(f"  sha256: {digest}")

    if args.messages is not None:
        messages.self_check()
        message_vectors = messages.corpus()
        message_out = pathlib.Path(args.messages)
        message_digest = write_ndjson(message_out, message_vectors)
        message_counts: dict[str, int] = {}
        for vector in message_vectors:
            message_counts[vector["kind"]] = message_counts.get(vector["kind"], 0) + 1
        print(f"generated {len(message_vectors)} message vectors into {message_out}")
        print("  kinds: " + ", ".join(f"{k}={v}" for k, v in sorted(message_counts.items())))
        print(f"  sha256: {message_digest}")

    if args.flow is not None or args.flow_negative is not None:
        # The family's own controls run before either file is written: the message the
        # sweep fragments is the declared sections' octets, and every vector's chunks
        # rebuild it. Both are checks on the *family*, so they run once, whether the
        # operator asked for the positives, the negatives or both.
        flows.self_check()
        flow_tables = slices.Corpus()
        flow_vectors = flows.flow_corpus(flow_tables)
        negative_vectors = flows.flow_negative_corpus(flow_tables)
        if args.flow is not None:
            flow_digest = write_ndjson(pathlib.Path(args.flow), flow_vectors)
            print(f"generated {len(flow_vectors)} flow vectors into {args.flow}")
            print(f"  sha256: {flow_digest}")
        if args.flow_negative is not None:
            negative_digest = write_ndjson(pathlib.Path(args.flow_negative), negative_vectors)
            print(f"generated {len(negative_vectors)} flow negatives into {args.flow_negative}")
            print(f"  sha256: {negative_digest}")
        flows.report(flow_vectors, negative_vectors)

    if args.frames is not None:
        frame_vectors = frames.frame_corpus()
        frame_out = pathlib.Path(args.frames)
        frame_digest = write_ndjson(frame_out, frame_vectors)
        frame_counts: dict[str, int] = {}
        for vector in frame_vectors:
            frame_counts[vector["kind"]] = frame_counts.get(vector["kind"], 0) + 1
        print(f"generated {len(frame_vectors)} frame vectors into {frame_out}")
        print("  kinds: " + ", ".join(f"{k}={v}" for k, v in sorted(frame_counts.items())))
        print(f"  sha256: {frame_digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
