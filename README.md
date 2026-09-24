![SpecAMQP — AMQP 1.0, specified in Lean: an AMQP frame pipeline from a sender to a receiver through OPEN, BEGIN, ATTACH, FLOW and TRANSFER, the connection's state diagram over Open, Active, End and Closed, and a machine-checked Lean proof](assets/banner.png)

# SpecAMQP

An **executable formal specification of AMQP 1.0 core** (OASIS Standard, Parts 0–5), written in Lean 4,
with a second independently written reference implementation of it, and a clause-level ledger that makes
completeness and fidelity *measurable*.

- **579 clauses** of the standard, each with a recorded disposition: 238 formalized, 105 covered by test
  vectors, 180 deferred to a named milestone, and the rest informative, out of scope or superseded.
- **24 test corpora**, replayed step by step against both implementations, comparing each step's verdict
  *and the condition behind every refusal*.
- **20 gates** in `tests/contracts/`, each a script that fails loudly, offline, with no network, clock or
  randomness.
- **76 Lean modules**, and an endpoint in `lean/Impl/` compiled by Lean's own C backend whose protocol core
  is proved to conform to the specification.

The specification is meant to be a target, not a description: conformance is defined as a state machine over
an interface alphabet frozen before any implementation existed, and implementations prove their own
instances of it. `PLAN.md` is the programme of record.

## What is here

| layer | what it holds |
|---|---|
| `spec/oasis/` | the vendored OASIS artifacts, byte-identity pinned in `toolchain/sources.toml`; every clause id, disposition and citation refers to these bytes |
| `lean/Generated/` | the standard's declared surface — descriptors, encodings, types, fields, choices — as generated Lean data |
| `lean/Spec/` | the handwritten semantics: executable, total, and independent of every consumer |
| `lean/Ref/` | a second, independently written reading of the same artifacts, sharing no definition with `lean/Spec/` |
| `lean/Impl/` | the shipped endpoint: its protocol core, proved to conform, and `Transport.lean`, its socket boundary — the one module there that is not proved |
| `lean/Shell/` | the shipped process: the recv/feed/write loop and the socket lifecycle |
| `lean/Harness/`, `lean/Contracts/`, `lean/Proofs/` | the runner and its reason-class vocabulary; the acceptance declarations; their proofs |
| `ledger/` | the clause ledger, its coverage and reconciliation, and the **ambiguity register** — every place the standard is silent and a reading was taken |
| `vectors/` | the test vectors: authored from clauses or recordings, **never produced by the executable specification** |
| `tests/contracts/` | the gates |
| `bench/` | off-gate timing evidence for the corpus instruments |
| `PLAN.md` | the programme of record, including its own rules of evidence |

## Status

**Every clause is accounted for, and every reading is recorded.** All 579 clauses of Parts 0–5 have a disposition, and where the standard is silent the register carries the reading taken *and* the alternatives it was chosen over, so a disagreement with a decision here is a disagreement about a written argument rather than about a default; trust is accounted
for gate-wise: the proof-integrity gate scans the handwritten modules for `sorry`, `native_decide`, `axiom`,
`opaque`, `unsafe` and `extern`, the one permitted `extern` boundary is `lean/Impl/Transport.lean` — pinned by
path and printed with its count, so the exemption cannot silently widen — and each accepted theorem's transitive
axiom inventory is printed, so the trust base of a claim is visible per theorem.

**The endpoint's protocol core is proved.** `Proofs/EndpointConformance.lean` proves the statement
`Contracts/EndpointConformance.lean` froze — the core is a forward simulation of the specification's
connection endpoint over the alphabet the interface fixes — and `Contracts/EndpointAcceptance.lean` binds
it. Its framing laws are proved under the same gates as everything else. The proof is plumbing and says so:
three of the four equalities relating the two independently written constructions are `rfl`-level, so a
defect inside `Spec.Connection.step` is inherited by both sides rather than caught here.

**What is not proved is named rather than left to be found**: Lean's compiler and runtime (which makes the
shipped binary *trusted* rather than verified), the socket boundary, the process loop above it, the stream
corollary that waits on `ValuePrefixDetermined`, and the delivery contract a second connection would rest
on. `PLAN.md` §23.1 records the measurement, the decision and the rejected alternative behind the socket
boundary — a choice, not a necessity.

**What is deliberately absent is a status snapshot.** The numbers above come from the ledger and the gates; which vectors pass, which remain staged and what has just moved are printed by running them, and `PLAN.md` carries the state and the history. A sentence here that described them would be wrong within a day, which is how most of the earlier drafts of this file were wrong. The endpoint is also exercised over a real socket as a
third runner beside `amqp-spec` and `amqp-ref`, with `tests/contracts/r4_wire_differential.sh` as the
record of what agrees and what does not.

## Running it

Everything runs in the pinned shell; the first `nix develop` realizes the closure and later runs are offline.

```sh
alias shell='nix --extra-experimental-features "nix-command flakes" develop --offline --no-update-lock-file .#spec --command'

shell bash tests/contracts/s0_sources_ledger.sh      # vendored identity, ledger, dispositions
shell bash tests/contracts/s0_tables_fidelity.sh     # generated tables current and load-bearing
shell bash tests/contracts/s0_spec_manifest.sh       # planner-owned files as the manifest records them
shell bash tests/contracts/s0_vector_citations.sh    # every citation in the corpus resolves
shell bash tests/contracts/s0_generator_fidelity.sh  # each corpus is what its generator produces

shell bash tests/contracts/s1_proof_integrity.sh     # no sorry, no native_decide; axiom inventories
shell bash tests/contracts/s1_differential.sh        # specification and reference agree on the wire
shell bash tests/contracts/s2_frame_vectors.sh       # the frame layer's corpus
shell bash tests/contracts/s3_exchanges.sh           # the exchange corpora, both artefacts
shell bash tests/contracts/s5_messages.sh            # the message layer's differential
shell bash tests/contracts/s6_transactions.sh        # the transaction layer's differential
shell bash tests/contracts/s7_sasl.sh                # the security layer
shell bash tests/contracts/r4_wire_differential.sh   # the endpoint over a socket, per vector

shell python3 scripts/clause-ledger.py check         # ledger, dispositions and reconciliation
shell python3 scripts/gen-oasis-lean.py --check      # generated tables current
```

## How it is checked

- **Proofs.** No `sorry`, `native_decide`, `axiom`, `opaque`, `unsafe` or `extern` in the handwritten
  modules, with each accepted theorem's transitive axiom inventory printed.
- **The corpus.** Both implementations replay the same vectors, and the differential compares verdicts
  *and the condition each refusal names* — agreeing that a step is refused is half of agreeing why.
- **Third-party evidence.** Recordings from implementations not generated from this model.
- **Mutation controls.** For each semantic layer, structural, boundary, omission and polarity mutants are
  planted, because the question is what *class* of wrong specification the evidence would fail to notice.

## License

The work of this repository — the specification, the reference, the ledger, the corpus, the gates and the
scripts — is licensed under the **Apache License 2.0**; see `LICENSE`.

The vendored OASIS artifacts under `spec/oasis/` are **not** covered by that license. They are the OASIS
Standard's own text, redistributed unmodified under their own terms, which `spec/oasis/` carries alongside
them. Nothing in this repository re-licenses them.
