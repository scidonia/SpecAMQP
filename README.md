# SpecAMQP

An **executable formal specification of AMQP 1.0 core** (OASIS Standard, Parts 0–5) written in Lean 4,
with a clause-level ledger that makes completeness and fidelity *measurable*.

**This repository holds a specification, and a reference implementation of it.** It defines what a
conforming AMQP 1.0 endpoint must do, states that as mathematics a machine can run, records for every clause
of the standard how — and to what extent — the specification accounts for it, and ships an endpoint written
in Lean whose protocol core carries the specification's conformance statement — frozen in `Contracts/EndpointConformance.lean`,
with R3 as the proof still owed — and whose framing laws are proved. What it does not ship is a
*verified binary*: Lean's compiler is trusted, the socket boundary and the Lean shell that drives it are the unproved parts, and
`PLAN.md` §23.1 names both rather than leaving them to be inferred.

## What is here

| layer | what it holds |
|---|---|
| `spec/oasis/` | the vendored OASIS artifacts, byte-identity pinned in `toolchain/sources.toml`. **Immutable**: every clause id, disposition and vector citation refers to these bytes |
| `lean/Generated/Oasis/` | the declared surface as Lean data — descriptors, encodings, types, fields, choices — generated from the artifacts |
| `lean/Spec/` | the handwritten semantics: executable, total, and independent of every consumer |
| `lean/Ref/` | an independently written reference implementation, authored from the artifacts and sharing no definition with `lean/Spec/` |
| `lean/Impl/` | the shipped endpoint's Lean side: the pure protocol core, whose `Conforms` instance is R3 and **undischarged**, and `Transport.lean` — the one module in this directory that is not proved (the socket boundary, `PLAN.md` §23.1) |
| `lean/Shell/` | the shipped process: the recv/feed/write loop and the socket lifecycle over the protocol core — whose conformance is stated and owed (R3), not proved. It imports the boundary because it owns the `IO`, which is why it sits outside `lean/Impl/` — that directory's claim is about its own files |
| `lean/Harness/` | the runner: corpus replay, per-step verdicts, and the reason-class vocabulary the corpus schemas mirror |
| `lean/Contracts/` | acceptance declarations: the exact propositions the specification claims |
| `lean/Proofs/` | proofs of those declarations |
| `ledger/` | the clause ledger, its coverage and reconciliation, the dispositions, and the **ambiguity register** — every place the standard is silent and a reading was taken |
| `vectors/` | the specification test vectors: positive, negative and recorded third-party, each authored from clauses or recordings and **never produced by the executable specification** |
| `tests/contracts/` | the gates: what makes the claims above checkable |
| `bench/` | timing evidence for the corpus instruments — off-gate, never a gate, with the environment, the input digests and the per-run figures in `bench/results/`; the ratio it reports is what detects a complexity regression |
| `PLAN.md` | the programme of record, including its own rules of evidence |

## Where an implementation fits

**The specification's purpose is to be a target.** `PLAN.md` defines what it means for an endpoint to
conform — a state machine over a frozen interface alphabet — and that interface was frozen *before any
implementation existed* for exactly this reason: proving an instance of it for a concrete programme is
downstream work. This repository now supplies **two** things to that work: an **executable oracle and a
definite contract to prove against**, and — since the implementation track of `PLAN.md` §23.1 — **a
reference endpoint of its own**, written in Lean and compiled natively, whose protocol core carries a *stated* instance of that same conformance relation, with its proof owed. TemperMint's Rust programme, its extraction through Charon and
Aeneas, and the proofs about it remain TemperMint's work and are not replaced by it: the endpoint here is a
second instance of the relation, and the corpus is what the two are compared over.

**How far the endpoint's evidence reaches.** Its protocol core's conformance is *stated* rather than proved — the claim is frozen in
`Contracts/EndpointConformance.lean` and R3 is the proof — so what is proved about its parts today is the framing laws, under the same gates as
every other proof in this repository. Its compiled form is a *trusted* step rather than a proved one — Lean's
compiler and runtime are not verified — and its socket layer is a small, separately named unproved
dependency: **a choice rather than a necessity**, because the pinned stdlib does have TCP (`Std.Async/TCP`,
over libuv compiled into `libleanshared.so`) and a POSIX wrapper — a couple of hundred lines, measured in
`PLAN.md` §23.1 — was taken instead, so that the endpoint's frame loop stays synchronous and the unnamed part of the trust base
stays small. `PLAN.md` §23.1 records the measurement, the decision and the rejected alternative, which was
built and passed before it was rejected. **The corpus does run against the
endpoint over a socket as a third runner beside `amqp-spec` and `amqp-ref`** — that runner is R4, its first rung
is in the tree (`scripts/run-endpoint-wire-differential.sh` with `scripts/endpoint/WireApp/` and the wire peer),
and it compares the shipped binary's per-step socket verdict against `amqp-spec`'s in-process verdict. **Two of
`slice.ndjson`'s six playable vectors agree end to end — one of them exercising the SASL layer through the core
including its refused step — and four diverge, each named with its step**: two because the shell prompts the
application only after a read, so two consecutive sends with nothing arriving between them cannot be played; one
because that vector's pre-state is `START` and the shell has already announced its own header; and one endpoint
state after a refusal, not yet attributed to the core or to the vector. So the rung discriminates, three of its
four divergences are attributed to the application seam rather than the core, and **R4 is not accepted**: an
unattributed divergence is what acceptance is waiting for, not a passing count. The protocol
core's `Conforms` instance is likewise R3 and undischarged: what is proved *about the endpoint* at this point
is nothing, and what is proved *about its parts* is the framing laws in `lean/Proofs/CoreLaws.lean`.

**`lean/Ref/` is not that proof, and it is not an implementation-acceptance mechanism.** It is a second
*independent reading* of the same standard, because the dominant residual risk here is prose ambiguity: two
readings by the same reader share their errors, so the way to test a reading is to build a second one from
the artifacts without looking at the first and see whether the two agree on the wire. Where they disagree,
one of them has misread the standard, and the disagreement is the evidence. That is a check on **the
specification**, not on an implementation.

And because the vectors, the verdict schema and the comparison are deliberately implementation-agnostic — a
Rust binary, a Gallina development through extraction, or a third party's stack can be added as a runner
rather than requiring a rewrite — the same corpus that tests the two readings also becomes the first
acceptance test any implementation runs. A second formalisation in a second prover was considered and not
adopted; `PLAN.md` records the reasons rather than the conclusion alone.

## How it is checked

Evidence is tiered, and each tier's blind spots are stated rather than assumed:

- **V1 — proofs.** The proof-integrity gate scans every handwritten module for `sorry`, `native_decide`,
  `axiom`, `opaque`, `unsafe` and `extern`, and prints the transitive axiom inventory of each accepted
  theorem so the trust base of a claim is visible per theorem.
- **V2 — the corpus.** The specification and the reference run the same vectors; the differential compares
  verdicts *and the condition each refusal names*, because agreeing that a step is refused is only half of
  agreeing about why.
- **V3 — third-party evidence.** Recordings and observations from implementations not generated from this
  model. A specification-built runner is a consumer, not third-party evidence.
- **V4 — mutation controls.** For each new semantic layer, a structural, a semantic-boundary, an omission
  and an acceptance/rejection-polarity mutant are planted and run, because the question is what *class* of
  wrong specification the evidence would fail to notice.

The gates are also the memory, because the repository's rules have each been bought by something that went
wrong. They sit in `tests/contracts/`, and `PLAN.md` records the rules themselves — quoting rather than
paraphrasing in a dispatch, deriving a label from its evidence cell rather than from a word in it, treating
a generated corpus's generator as its target rather than a previous copy of its output, and the rest.

## Running it

Everything runs in the pinned shell; the first `nix develop` realizes the closure and later runs are offline.

```sh
alias shell='nix --extra-experimental-features "nix-command flakes" develop --offline --no-update-lock-file .#spec --command'

# data and provenance
shell bash tests/contracts/s0_sources_ledger.sh      # vendored identity, ledger, dispositions
shell bash tests/contracts/s0_tables_fidelity.sh     # generated tables current and load-bearing
shell bash tests/contracts/s0_lean_environment.sh    # pinned toolchain, mathlib, offline resolution
shell bash tests/contracts/s0_spec_manifest.sh       # planner-owned files as the manifest records them
shell bash tests/contracts/s0_vector_citations.sh    # every citation in the corpus resolves
shell bash tests/contracts/s0_generator_fidelity.sh  # each corpus is what its generator produces

# proofs and the two artefacts
shell bash tests/contracts/s1_proof_integrity.sh     # no sorry, no native_decide, axiom inventories printed
shell bash tests/contracts/s1_differential.sh        # specification and reference agree on the wire
shell bash tests/contracts/s2_frame_vectors.sh       # the frame layer's corpus
shell bash tests/contracts/s5_messages.sh            # the message layer's differential
shell bash tests/contracts/s6_transactions.sh        # the transaction layer's differential

# the ledger and the generated tables
shell python3 scripts/clause-ledger.py check         # ledger, dispositions and reconciliation
shell python3 scripts/gen-oasis-lean.py --check      # generated tables current
```

`nix develop` provisions a writable copy of the pinned mathlib closure from a prewarmed store path, so
Lean and mathlib are exactly the revisions the downstream proof work pins. `scripts/fetch-oasis.sh
--verify` checks the vendored artifacts offline; it is the only step that ever fetches, and it refuses any
hash mismatch.

## License

The work of this repository — the specification, the reference, the ledger, the corpus, the gates and the
scripts — is licensed under the **Apache License 2.0**; see `LICENSE`.

The vendored OASIS artifacts under `spec/oasis/` are **not** covered by that license. They are the OASIS
Standard's own text, redistributed unmodified under their own terms, which `spec/oasis/` carries alongside
them. Nothing in this repository re-licenses them.
