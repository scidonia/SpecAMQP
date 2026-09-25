# SpecAMQP — development programme: a correct, executable AMQP 1.0 specification

This plan is forward-only: what to do, and what constrains doing it. The engineering
log it used to carry — rung narratives, design rationale, the collected traps and the
historical numbers — is preserved verbatim in `RECORD/`, indexed by `RECORD/README.md`;
section texts this file keeps in edited form are preserved as written in
`RECORD/Framing.md`. Two rules keep this file honest:

- **No current-state numbers.** Counts, gate results and rung status live in
  `ledger/coverage.json` and the gates' own output; this file links rather than
  quotes, because prose drifts and the ledger computes. Historical numbers in
  `RECORD/` are dated records of what was true then.
- **Decisions stay, with a one-line reason each.** The *argument* lives in `RECORD/`.

## Goal

Produce, in this repository, **a complete, correct, executable formal specification of AMQP 1.0 core** (OASIS Standard, Parts 0–5) in Lean 4, faithful to the OASIS Standard, with a clause-level ledger that makes *completeness* and *fidelity* measured properties rather than claims, and with a defined conformance interface so that downstream work — a Rust implementation, its extraction, and its proofs, which belong to TemperMint, not here — has a definite target.

This repository holds the specification, the evidence that it is correct, and a **reference implementation written in Lean**. The two are deliberately separate artefacts: the specification is declarative, generated-table-driven and shaped for proof, while the reference implementation is operational, independently written from the same clauses, and compiled to a native executable by Lean itself — so its behaviour rests on no translation step. Differential testing runs the implementation against the specification and against recorded third-party exchanges; the corpus, not either artefact, is what both are measured by. Nothing here is Rust: extraction through Charon and Aeneas, proofs about a Rust programme, and performance work remain downstream (§23); what this repository measures of its own is its instruments, the corpus executables' cost, off-gate, committed under `bench/` (measurement here, optimisation there).

## 1. What "a correct specification" means here

Correctness of a specification is not a vibe, and it is not "it type-checks". Five properties, each with a mechanism and an observable gate:

| Property | Statement | Mechanism |
| --- | --- | --- |
| **Completeness** | every normative statement in the pinned OASIS artifacts is dispositioned; every MUST-class statement is either formalized or recorded as an environment/out-of-scope assumption with a reason | clause ledger (§6) with coverage report |
| **Consistency** | the specification does not contradict itself: encodings round-trip, invariants are preserved, no illegal transition is silently permitted, no obligation leads to a state where it cannot be met | theorems in `lean/Spec`, `lean/Contracts` (§9), executability gate |
| **Fidelity** | the formalisation says what the OASIS text says, and admits what conforming implementations actually do | clause citations in the ledger, ambiguity register (§8), third-party vector admission (§12 V3) |
| **Discrimination** | the specification is neither vacuous nor over-permissive: it admits the legal and rejects the illegal, with named error conditions | witness/counter-witness vector pairs (§11), specification-mutation controls (§12 V4) |
| **Usability** | the specification is executable, and conformance is defined precisely enough that a third party can be checked against it | executable driver (§9), conformance interface (§10) |

Completeness is measured against the pinned artifacts, never asserted: **`ledger/coverage.json` is the census, and this plan deliberately does not quote it.** The S0-era census table and its drift record are `RECORD/Ledger.md`; the crude scan the programme was sized with is reconciled in `ledger/reconciliation.json`. Scan numbers size the work; the ledger is the work. **Done** means: every clause dispositioned; every MUST-class clause formalized or explicitly assumed, with reviewer sign-off; the declared surface covered by generated tables rather than transcription; the vector corpus passing with the executable specification and with third-party admissions; the mutation controls firing; and no `sorry`, no `noncomputable` definition, and no unaudited axiom.

## 2. Deliverables

| # | Deliverable | Location |
| --- | --- | --- |
| D-a | Vendored, hash-pinned OASIS artifacts plus copyright notice | `spec/oasis/`, `spec/oasis/NOTICE` |
| D-b | Clause ledger, dispositions, coverage report | `ledger/` |
| D-c | Ambiguity register with adopted readings and evidence | `ledger/ambiguities/` |
| D-d | Generated definition tables (descriptors, fields, choices, encodings, error conditions) | `lean/Generated/Oasis/` |
| D-e | Executable Lean specification of Parts 0–5 | `lean/Spec/` |
| D-f | Acceptance declarations for every specification claim | `lean/Contracts/` |
| D-g | Conformance interface: the definition of what it means to implement this specification | `lean/Contracts/Conformance.lean` |
| D-h | Specification test vectors: positive, negative, and recorded third-party | `vectors/` |
| D-i | Executable driver over the vectors (`lake exe amqp-spec`) | `lean/Spec/Main.lean` |
| D-j | Handoff notes for downstream implementation work | `HANDOFF.md` |
| D-l | Reference implementation of the type system in Lean, independent of `Spec.*`, compiled to a native executable | `lean/Ref/`, `lake exe amqp-ref` |
| D-m | The type-system vector corpus and its schema, authored from the artifacts' worked examples | `vectors/primitives.ndjson`, `tests/contracts/value-vector.schema.json` |
| D-n | The engineering record: rung narratives, design rationale, findings | `RECORD/` |

## 3. Non-goals

- **No Rust, no extraction, no performance work.** The reference implementation is in Lean, and it is the only implementation here. A Rust programme, its extraction through Charon and Aeneas, proofs about it, optimised candidates and performance *targets* belong to TemperMint and are scheduled there (§23). The corpus executables' cost is measured off-gate and committed under `bench/` — measurement here, optimisation there — and the numbers are not a claim about any downstream artefact's speed.
- **No claims about the reference implementation's conformance beyond its corpus.** It is an implementation, not a proof: what it satisfies is stated by the vectors it passes, and a clause it does not yet exercise is a clause it does not yet demonstrate. The specification's theorems are about the specification. **No protocol extensions**: AMQP management (`amqp-man`), filter expressions (`filtex`), claims-based security (`amqp-cbs`), addressing, JMS mapping, HTTP-over-AMQP, event streams, and connection-info are out of scope, existing as working drafts rather than as part of the OASIS Standard; core must nonetheless model how unknown described types and pass-through annotations are handled.
- **No broker or queue semantics.** AMQP core defines links and termini, not what a destination does with a message. `source`/`target` are formalized as protocol-visible field sets and obligations, not as a routing model.
- **No TLS, no TCP/IP, no crypto.** Security-layer negotiation is specified; TLS, the byte stream, and mechanism-specific cryptography are environment assumptions, recorded as such in the ledger.
- **No verified native execution claims, no claims about any programme, no calendar promises.** The specification states what a conforming endpoint does; it does not certify anything. Progress is reported in coverage units: clauses dispositioned, declarations, vectors, theorems.

## 4. Normative source and pinning

Vendor the six Part 0–5 XML artifacts byte-identically at `spec/oasis/`, with SHA-256 recorded in `toolchain/sources.toml` and the OASIS copyright/citation notice retained alongside (the OASIS notice permits redistribution of the whole with the notice intact; the files MUST NOT be modified). `scripts/fetch-oasis.sh` populates `spec/oasis/` and refuses to proceed unless every hash matches `sources.toml`; the vendored copies are committed, so all later work is offline.

Two structural facts about these artifacts, verified against the pinned bytes, drive the design:

1. **The definition language is present and machine-readable**: `type` (with `class` ∈ {primitive, restricted, composite}), `field` (with `type`, `mandatory`, `default`, `label`), `choice` (with `value`), `descriptor` (with `code` as `domain:descriptor`, e.g. `amqp:open:list` = `0x00000000:0x00000010`), `encoding` (with `code`, `category`, `width`). Sections carry stable `name` attributes which anchor every clause identifier.
2. **Behaviour is prose.** The artifacts contain no state-machine element type: only prose `<doc>` text with normative keywords, plus `<picture>` diagrams. Framing, connection/session/link lifecycles, window arithmetic, settlement, and transaction rules exist only as normative English.

Consequence, and the core methodological decision of this programme: the specification is built from **generated tables for the declared surface** (codes, field order, mandatory flags, defaults, choices, encodings) and **handwritten semantics for behaviour**, bound by contracts that make a mistyped descriptor code impossible to introduce silently.

## 5. The specification's own independence rules

Three independence rules keep the evidence meaningful; each has a gate (§17):

1. **Generated tables are data, not semantics.** `lean/Spec` may import the generated tables through a binding layer; semantics are handwritten. A generated table is never the authority on behaviour.
2. **Vectors are authored from the clauses and from recordings, never from the executable specification.** A vector produced by running the specification would only prove the specification equals itself.
3. **No clause's meaning may live outside the ledger.** Every normative statement's disposition points at the declaration, assumption, or vector that carries its meaning; an undocumented convention is a defect.

## 6. The clause ledger

`scripts/clause-ledger.py` reads only the pinned artifacts and emits `ledger/clauses.json`: one record per normative statement, deterministically ordered. Its rules (the full original text, with counts and worked examples, is `RECORD/Framing.md`):

- **Identifier**: `<artifact>#<anchor path>.<n>`. The anchor path is the chain of enclosing named elements, because a bare `name` is not unique, and `<n>` is the 1-based statement index within the anchor; anchor paths make ids stable under unrelated edits.
- **Fields**: artifact, anchor, index, kind, class (`MUST` for both MUST forms, else the kind), normalised text, text and statement SHA-256, and cited `<xref>` names. `index` counts statements within the anchor: a sentence carrying two keyed phrases is two statements quoting the same sentence, told apart by the invariant that `class` is the kind's class.
- **Cross-references are resolved for the reader**: a `<definition>` constant renders its value; a named element renders `«open»`; a reference that **selects a choice** renders the choice's own name and records `<element>/choice:<choice>` in `references` — two clauses differing only by a `choice` attribute otherwise present identical antecedents with opposite obligations (the defect `RECORD/ConformanceInterface.md` records).
- **Normalisation** handles the real markup: emphasis around the keyword, keywords split across source lines, entity-encoded text; `<picture>`, `revhistory` and `acknowledgements` content is not normative. A token-aware scan, not a regex grep, verified by planted negative controls (§17).
- **Dispositions** (`ledger/dispositions/*.json`, planner-authored) key on `(id, text_sha256)`, so edited clause text makes its disposition stale and fails the contract. **A disposition is a decision about text, not about a reference**: a re-split paragraph gets its decision moved onto the text it decides about, not a hash re-recorded in place. Values: `formalized:<Lean declaration>`, `deferred:<milestone>`, `environment:<id>`, `out-of-scope:<reason>`, `underspecified:<id>`, `informative`, `test:<vector id>`, `superseded:<decision id>` (§8).
- **Statements without keywords are captured too**: a paragraph can state a requirement with no RFC 2119 keyword, and a keyword-driven ledger loses it. Captured sentences become kind `UNKEYED`, and `check_unkeyed` fails until each carries a disposition, so an omission is a decision. **Pictures are reviewed, not merely skipped**: any carrying formal grammar or normative keywords are listed in `ledger/pictures.json` with a content digest; `check` fails until each carries a disposition keyed to it, and again if the picture's text changes.
- **Coverage report** (`ledger/coverage.json`) aggregates per artifact and per anchor, regenerated per milestone; acceptance diffs it so a coverage regression is visible.
- **No clause can escape the ledger**: a token census of every text node is compared against what the ledger accounted for; a keyword token producing no clause fails `check` and names the element. **The baseline reconciliation cannot drift**: `ledger/reconciliation.json` records the crude-scan numbers and the named mechanism for every difference; `check` fails if they stop matching.

## 7. Generated definition tables

`scripts/gen-oasis-lean.py` reads the pinned bytes and emits `lean/Generated/Oasis/`, one module per declaration kind (`Constants`, `Types`, `Fields`, `Encodings`, `Choices`), with `provenance.json` recording the artifact digests and record counts — read the counts there, not here. Contracts, all enforced by `tests/contracts/s0_tables_fidelity.sh`:

- **currency**: a fresh generation is byte-identical to the committed modules, so the tables are derived rather than transcribed;
- **load-bearing**: replacing `amqp:transfer:list`'s code with `disposition`'s in a scratch copy of Part 2 changes the generated tables and makes the currency check fail — the gate is not vacuous;
- **counts**: an independent count of the pinned artifacts equals the generated record counts;
- **no smuggling**: no file under `lean/Spec`, `lean/Contracts` or `lean/Proofs` may contain a literal descriptor code or an `amqp:`-shaped symbol — they come from these modules;
- **compilation**: the generated modules build against the pinned closure.

Two normalisations are deliberate and documented in the generator: labels have whitespace runs collapsed so diffs stay stable (no data field is touched), and each declaration carries its anchor path, linking a generated record to the ledger's identifier for the same element. Each generated module is self-contained; `Choices.lean` imports `Types.lean` because the error-condition lookup needs the type table, and nothing else.

## 8. Ambiguity register

AMQP 1.0's prose is not uniformly exact; several areas admit two readings, and real implementations disagree in practice. `ledger/ambiguities/*.json` records, per issue: the clause ids involved, the candidate readings, the reading adopted, the evidence, and the consequences for the conformance relation. Adopting a reading is a decision *with evidence*, recorded as a `superseded` disposition; where a mainstream implementation disagrees, the disagreement is a recorded finding, not a licence to weaken the specification. The register's opening entries are listed in `RECORD/Framing.md`.

## 9. Specification architecture (Lean)

```
lean/Spec/
  Value.lean         AMQP type system: the value domain and all 39 encodings
  Codec.lean         the value codec: readers, writers, refusals, and the class vocabulary
  Frame.lean         frame header, extended header, frame types 0x00/0x01, channel, and the framing
  FrameCodec.lean    the fourteen frame-level performatives, bound to the generated descriptors
  Message.lean       Part 3: sections, annotations, fragmentation, outcomes
  Connection.lean    the connection and session state machines, error taxonomy, SASL framing, and the layers
  ConnectionCodec.lean  the connection's own codec: header negotiation and the performatives' bodies
  Session.lean       links, flow, credit, delivery numbers, drain and echo, handles
  SessionCodec.lean  the session layer's codec
  Transactions.lean  Part 4: coordinator, declare, discharge, transactional state
  WidenedState.lean  the widened session model: link registry, unsettled map, sender bookkeeping (§24)
  ReadLaws.lean      the laws the readers obey: progress, consumption, prefix behaviour
  Main.lean          executable driver: vectors in, verdicts out
```

Earlier versions of this list named modules the implementation folded elsewhere (`Wire`, `Performative`, `Endpoint`, `Flow`, `Sasl`, `Exec`, `Spec/Conformance`); they are recorded as folded, not deleted, because the ledger gate's forward-promise exemption read this list — a stale name here protects values nothing checks (`RECORD/Framing.md` keeps the note as written). Requirements:

- **Executable, total where the protocol is total, independent of consumers.** Every definition in `Spec/` is computable (`noncomputable` and `partial` rejected by contract); decoding returns an explicit error result rather than a default; no `Spec/` declaration refers to anything outside `lean/` and `spec/oasis/`.
- **Nondeterminism is explicit, canonical encodings are specified.** Where the OASIS text says MAY, the choice is a first-class input (a policy stream), not a hidden decision inside a Lean definition; specificity preservation holds round-trip theorems on a stated equality class rather than on "some bytes came back". **The starting state is stated for a *layer*** — `Endpoint.initialFor (layer : Layer)` — so an implementation's starting state can be *proved* against a specification state rather than assumed equal to one: a constructor parameterised by the choice the standard leaves open, not a constant encoding our reading of it.

## 10. The conformance interface

Frozen at S0/S1 and defined in `lean/Contracts/Conformance.lean`: an endpoint is a state machine over an interface alphabet (`Input` = `frame` | `api` | `tick`; `Output` = `frame` | `api`), and conformance is simulation preserving **identical output sequences**. The alphabet does not change: the widening (§24) adds state, not events. `Contracts/EndpointConformance.lean` states the shipped core's claim and imports neither its proof nor its acceptance, so an unproved statement could not be quietly weakened to meet one. The six defining rules — the arguments and the instances' history are `RECORD/ConformanceInterface.md`:

1. **Output agreement, not trace inclusion** — the wire is the observable, so "implements AMQP 1.0" is a definite statement rather than a family of interpretations.
2. **Specification nondeterminism is a set** — a third-party behaviour the specification rejects is a bug in the specification, and adequacy must be able to say so (§12 V3).
3. **MUST versus SHOULD** — MUSTs are obligations; SHOULDs are fairness-qualified progress obligations or recorded freedoms, never silently promoted.
4. **Progress is part of conformance** — mandated actions are deadlock-freedom obligations under a stated fairness assumption, enumerated from the ledger.
5. **Bounded resources are explicit** — exhaustion is specified behaviour with the mandated error code, so running out of room is incorrect in a checked way.
6. **Anchored in an environment model** — the peer, the ordered byte stream, ticks, TLS/crypto-as-opaque are named assumptions with ledger dispositions.

## 11. Specification test vectors

One shared format for everything the specification is tested against: NDJSON, schema-validated (`tests/contracts/vector.schema.json`), **logical time only** — timestamps are ordering tags, never wall-clock, so replay is deterministic on any machine (worked example: `RECORD/Framing.md`). The rules:

- `kind` is `positive` (must be admitted, with the named outputs), `negative` (must be rejected with a named error condition and the mandated close/detach behaviour), or `recorded` (captured from a third-party implementation, provenance mandatory: peer implementation and version, capture date, and the transcript hash kept out-of-tree).
- `dir:"in"` is peer→endpoint, `dir:"out"` is endpoint→peer; `expect` distinguishes byte-identical output from a typed action where the specification permits latitude (for example fragmentation split points). `refs` cite the clauses a vector is testing, and the coverage report cross-checks them against the ledger, so vectors cannot accumulate free of the clauses they claim to exercise — and clauses cannot be claimed as tested by vectors that do not cite them.
- **Authoring rule (§5 rule 2)**: vectors come from the clauses or from recordings. A vector generated by running the specification is not evidence. Negative vectors carry the error-condition expectation explicitly, because "it fails" is not a specification — "it fails with `amqp:decode-error` on channel 3, after which the connection is closed" is.

## 12. Correctness evidence

Four tiers, all offline, none requiring an implementation to be written here:

| Tier | Question | Mechanism | Failure it detects |
| --- | --- | --- | --- |
| **V1** | is the specification internally consistent? | theorems: round trips, canonicality, invariants (window and credit conservation, handle uniqueness, delivery-number monotonicity), reachability of every state with a mandated exit | contradictions, dead ends, silent acceptance of an illegal transition |
| **V2** | does it discriminate? | the positive/negative vector corpus, run by `lake exe amqp-spec` | over-permissiveness, missing error paths, vacuous definitions |
| **V3** | is it faithful to reality? | recorded third-party vectors must be **admitted** by the specification, and reproduced where the specification fixes bytes | **over-narrow specification** — the defect class that makes formalisations useless in practice |
| **V4** | would the corpus catch a wrong specification? | specification-mutation controls: planted mutations (a dropped MUST check, an off-by-one in window arithmetic, a wrong descriptor code in a vendor copy, acceptance of a non-canonical encoding, an out-of-range channel admitted) must each be detected by V1–V3 with the expected diagnostic | a corpus that proves nothing because it cannot fail |

V4 is what makes V2 and V3 load-bearing: a mutation that no tier detects is reported as a suite defect, not quietly tolerated. **Considered and not adopted: a second formalisation in a second prover** — two readings by the same reader share their errors, per-clause review is the scarce resource, and it does not discharge the Rust trust line. Kept cheap rather than closed (the vectors, schema and comparison are implementation-agnostic), with named revisit triggers: implementation proofs moving to Rocq, V3 unable to adjudicate, or a second kernel wanted for the specification's own claims. Full deliberation: `RECORD/SecondProver.md`. The risk register that was §19 is `RECORD/Framing.md`. Recording third-party vectors is a manual, credentialed, off-gate activity: run an existing peer implementation (Qpid Proton, Apache Qpid J/Artemis, RabbitMQ 1.0, Dispatch router — two or more), capture the bytes with harness glue, commit the capture with provenance; replay is offline and deterministic, and no test contacts a network service, a model, a clock, or a random source.

## 13. Milestones — state at HEAD, and where the record lives

Each milestone's scope, contracts, expected pre-implementation failure and acceptance, **and the narrative of how it was earned**, are preserved per rung in `RECORD/`: `S0.md` … `S7.md`, `S1.5.md` (the codec proof ladder), `H1.md`; the implementation track in `EndpointTrack.md` and `R1.md` … `R5.md`. State at HEAD, by link rather than by number: **coverage and dispositions** —

- `ledger/coverage.json`, regenerated by `python3 scripts/clause-ledger.py check`. The live list of clause obligations is the ledger's `deferred:` dispositions. **Gates**: the contracts in `tests/contracts/` (§20 lists them; `AGENTS.md` explains each) — run them for status; do not read status off prose, this file included. **What happened**: `RECORD/README.md`'s mapping table resolves every old section of this plan, including the citations ("§13's D4 record", "§23.1") that appear in the ledger and in `AGENTS.md`.

## 14. Repository layout

```
PLAN.md  AGENTS.md  HANDOFF.md  RECORD/
flake.nix  flake.lock
toolchain/{sources.toml,downstream-pins.toml}
spec/oasis/{amqp-core-*-v1.0-os.xml,NOTICE}
ledger/{clauses.json,coverage.json,dispositions/,ambiguities/}
lean/{Spec/,Ref/,Harness/,Impl/,Shell/,Generated/Oasis/,Contracts/,Proofs/,lakefile.lean,lean-toolchain,lake-manifest.json}
vectors/{*,recorded/}
tests/contracts/
scripts/
bench/{run.py,workloads.json,results/}
```

Directories appear with their first real file: no empty scaffolding, no build caches, no generated file without its generator.

## 15. Repository and toolchain decisions

- **The specification's toolchain is Lean only.** `lean-toolchain` pins `leanprover/lean4:v4.31.0` and mathlib `v4.31.0`, with nixpkgs `b3d51a0365f6695e7dd5cdf3e180604530ed33b4` for the prewarmed closure — the same Lean and mathlib revisions TemperMint pins, so the specification's modules compose with downstream proof work without version surgery. This repository requires no Rust, Charon, or Aeneas.
- **Downstream pins are recorded, not required.** `toolchain/downstream-pins.toml` records TemperMint's Charon `a5591f6b94c8575a6ba2ae71090614a722f2b011` (LLBC `0.1.263`), Aeneas `227f4e7ac70d687a6b1a4871b3304f5a1c6994bf`, and rustc `nightly-2026-09-17` as the identities the downstream consumer uses, so the handoff names exact revisions. A read-only contract checks that our Lean/mathlib revisions still match TemperMint's, so the two repositories cannot drift apart silently.
- **Integration contract.** The Lean project is a normal Lake package with path-based module names (`Spec.*`, `Contracts.*`, `Proofs.*`, `Generated.*` under namespace `SpecAMQP.*`), importable as a dependency by downstream tooling; no symlink or re-export layer. **No new dependencies** beyond Lean, mathlib, and the pinned closure without a recorded decision; the scripts use the Python standard library. `.feature` contracts are executed by `scripts/run-contracts.py`, adopting TemperMint's runner idiom, added with the first feature contract rather than in advance.

## 16. Contracts, ownership, and test forms

Planner-owned (coder and reviewer MUST NOT modify; a changed file requires an explicit planner update plus a regenerated SHA-1 manifest, which `tests/contracts/s0_spec_manifest.sh` recomputes and compares):

- `toolchain/sources.toml`, `toolchain/downstream-pins.toml`; everything under `ledger/`, including dispositions and ambiguities
- `tests/contracts/**` including schemas, fixtures and feature files
- `lean/Spec/**`, `lean/Contracts/**`, `lean/Harness/**` (the reason-class vocabulary is contract, mirrored in `tests/contracts/exchange-vector.schema.json`)
- `vectors/**` once a vector is committed as contract

Coder-owned: `flake.nix`, `flake.lock`, `scripts/**` (including `scripts/loopback/**`), `lean/Proofs/**`, `lean/Ref/**`, `lean/Impl/**`, `lean/Shell/**`, `lean/Generated/**` (regenerated only), `AGENTS.md` and `HANDOFF.md` under planner review. `lean/Impl/Transport.lean` is the one coder-owned file whose *content* is a declared trust claim: the trust gate pins `@[extern]` to that path and prints the count, so a change shows up in a gate's output rather than only in a diff.

Test forms:

- **Specification properties and invariants** are theorem/interface-conformance contracts, not Given/When/Then: they are mathematics over a defined domain.
- **Vector replay and mutation tiers** are BDD scenarios at the harness boundary, where the actor is the operator running the driver over a corpus and the observable outcome is the verdict report and exit status; the driver's refusal diagnostics are contract, not incidental log wording.
- **Ledger, schema, and provenance checks** are data/workflow contracts; **generators are contracts too**: a generator must reproduce its committed output byte-for-byte, and a mutation of its input must change that output.
- **No test may call a network service, a model, a real clock, or randomness.** Third-party capture is manual, off-gate, and its *outputs* are committed; replay is offline. Any generated input uses a committed seed. **Failure-first**: every new contract is run and observed failing before its implementation, with the exact command and diagnostic recorded. A test never observed to fail protects nothing.

The history behind these rules — what each one cost, in the order it was bought — is `RECORD/WorkingAgreements.md`.

## 17. Verification gates and their negative controls

Every gate pairs a mechanism with a negative control that proves the gate can fail for the reason it exists: the full table — source identity, vendored immutability, ledger completeness, table fidelity, no hand-typed codes, executability, proof integrity, vector provenance, picture review, discriminating power, adequacy, determinism — is preserved in `RECORD/Framing.md`; the gates are the commands of §20.

## 18. Constraints and invariants

- The specification is executable, total where the protocol is total, and independent of every consumer.
- `MAY`-clauses become explicit nondeterminism and never a silent deterministic choice; `SHOULD` is never silently promoted to `MUST`.
- Semantics are handwritten; generated tables are data; no clause's meaning lives outside the ledger; vectors are authored from clauses or recordings, never produced by the specification.
- No `sorry`, no reachable `sorryAx`, no unapproved axiom, no undisclosed `native_decide`.
- The specification makes **no claim about any implementation**. Its own assumptions — the peer, the ordered byte stream with arbitrary fragmentation, ticks, resource limits, TLS and mechanism cryptography — are named individually with ledger dispositions, and each of its claims states which of them it rests on.
- Third-party recordings are evidence about the OASIS text, not authority over it: a disagreement becomes a register entry with a decision, never a silent conformance weakening.

## 19. Risks and mitigations

The risk register — over-narrowing, over-permissiveness, prose ambiguity, transcription error, ledger drift, scale, executability cost, corpus acquisition, correlated misreadings, scope creep — with each risk's failure mode and mitigation, is preserved in `RECORD/Framing.md`; the mitigations are the mechanisms §1, §12 and §17 name.

## 20. Acceptance commands

Run in milestone order. `shell` abbreviates the offline pinned-shell invocation; the first `develop` realises the pinned closure, everything afterwards is offline and writes only into temporary directories. Every gate builds with `LAKE_NO_CACHE=1`; an ad-hoc verification build must too.

```sh
alias shell='nix --extra-experimental-features "nix-command flakes" develop --offline --no-update-lock-file .#spec --command'

shell bash tests/contracts/s0_sources_ledger.sh      # vendored identity, ledger, dispositions
shell bash tests/contracts/s0_tables_fidelity.sh     # generated tables current and load-bearing
shell bash tests/contracts/s0_lean_environment.sh    # pinned toolchain, mathlib, offline resolution
shell bash tests/contracts/s0_spec_manifest.sh       # planner-owned files as the manifest records them
shell bash tests/contracts/s0_vector_citations.sh    # every citation resolves
shell bash tests/contracts/s0_generator_fidelity.sh  # each corpus is what its generator produces
shell bash tests/contracts/s1_proof_integrity.sh     # no hidden trust; axiom inventories per theorem
shell bash tests/contracts/s1_ref_vectors.sh         # the reference builds native; both its corpora pass
shell bash tests/contracts/s1_differential.sh        # specification and reference agree on the wire
shell bash tests/contracts/value_boundaries.sh       # the value layer's rule-boundary sweep
shell bash tests/contracts/value_class_agreement.sh  # the value layer's reason-class agreement
shell bash tests/contracts/s2_frame_vectors.sh       # the frame layer's corpus
shell bash tests/contracts/s3_exchanges.sh           # the exchange corpora, both artefacts
shell bash tests/contracts/s4_flow.sh                # the flow layer's corpus
shell bash tests/contracts/s5_messages.sh            # the message layer's differential
shell bash tests/contracts/s6_transactions.sh        # the transaction layer's differential
shell bash tests/contracts/s7_sasl.sh                # the security layer
shell bash scripts/run-transport-loopback.sh         # two Lean processes over loopback; shim evidence
shell bash scripts/run-transport-loopback.sh --mutant NAME   # truncating-recv | reordering-recv | short-send
shell bash tests/contracts/r1_transport_shell.sh     # R1's evidence, and each control's pinned reach
shell bash tests/contracts/r2_endpoint_shell.sh      # the shipped shell's forced obligations
shell bash tests/contracts/r4_wire_differential.sh   # the endpoint over a socket, per vector
shell python3 scripts/clause-ledger.py check         # ledger + audit + reconciliation
shell python3 scripts/gen-oasis-lean.py --check      # generated tables current
```

## 21. Work order

The milestone sequence S0 → S1 → S2 → S3 → V1–V4 → S4 → S5 → S6 → S7 ran to completion of its slices; the record is `RECORD/S0.md` … `RECORD/H1.md`. The order from here, adopted as §23.4 item 5:

1. **The widening** (§24) — its clause obligations move from `deferred:` to carried in the ledger as each carrier exists.
2. **S5's remainder** — the message layer's acceptance contract and round-trip proof (§25); then the other layers' deferred clauses, each dispatch asking for the *costing* as well as the site — which modules a change reaches, and whether that reach includes a conformance proof whose guard structure it would follow (`RECORD/FINDINGS.md`, the tail-trial rule).
3. **The narrator demonstration** (§23.4 item 3) — the specification narrating live traffic, with one mutation client whose violation is refused and quoted; then **H1**, the handoff document, last. Recorded third-party vectors (V3) are added as captures become available, without blocking anything (§25).

## 22. Parallel work order

Slices run at the same time without sharing a file, because the cost of a parallel batch is the interface that has to be fixed before it starts and the conflict that follows if it is not. Three rules hold for every batch (as written, with the episode that sharpened them, in `RECORD/Framing.md`; the waves as dispatched, in `RECORD/WorkingAgreements.md`):

* **interfaces are fixed by the planner before the batch starts** — a state type, a dispatch hook, a corpus schema. A slice that discovers it needs a different interface reports that; it does not negotiate one with its sibling, because two coders agreeing on an interface is not the same as the interface being right.
* **file ownership is disjoint, and the shared boundaries are named rather than discovered.** There are two: the generator, split before a wave needs two slices to touch it; and **the harness, which is shared with everything** — a slice that must edit it advances it in compiling steps, and if two slices need it in one wave the planner sequences them. The practical forms: write shared files whole where the tool allows it; say so when mid-edit; believe the owning slice over a build log. **One integration owner**: the planner runs the acceptance commands, not the slices, since a slice that validates its own work is validating against its own reading of the contract.

## 23. Handoff: what downstream implementation work needs from here

This repository holds the specification **and** a reference implementation of it: an AMQP 1.0 endpoint written in Lean, compiled natively, whose protocol core's conformance is stated at the frozen interface's type, with **two** named unproved parts: its socket boundary, and the Lean shell that drives it. The *core* is what is proved; a reader who takes that for a claim about the process has been misled by an omission rather than by an overstatement, which is why the shell is named here. The remaining work — a Rust implementation, its extraction through Charon and Aeneas, proofs that it conforms, performance evidence — belongs to TemperMint; this repository's endpoint is a *second instance* of the same conformance relation, not a replacement. What downstream needs from here, and what `HANDOFF.md` records:

1. **The frozen interface alphabet and conformance relation** (§10) — so an implementation's proof is a `Conforms` instance rather than a re-framing exercise.
2. **The ledger and coverage report** — so implementation milestones can claim clause-level coverage in the same units as the specification, and gaps are visible on both sides.
3. **The vector corpus** — positive, negative, and recorded — as the differential and regression suite for any implementation, with the schema already frozen.
4. **The executable specification** (`lake exe amqp-spec`) — the oracle for spec-vs-implementation differential testing, and the reason vectors can be checked without writing a checker.
5. **The Lean/mathlib pin agreement** — so the specification's modules can be required directly by downstream proofs.
6. **Requirements that need tooling changes**, for scheduling in TemperMint rather than implementing here: multi-target extraction sharing one source-closure identity; a certificate binding the specification, model, corpus, and a `Conforms`-style theorem; a certificate kind whose claim is "refines a specification" rather than "computes a specified value"; per-module proof-cost accounting; and a corpus dimension in replay that regenerates and compares every claim-bearing input byte-identically.

### 23.1 The implementation track

**The goal is a reference implementation of this specification**: an AMQP 1.0 endpoint, written in Lean, running as a native process, whose protocol core is the *stated* instance of the conformance relation §10 froze. It exists so that the corpus has a runner that speaks the protocol on a real transport rather than replaying vectors in process. The rungs and their records: `RECORD/R1.md` (transport shell), `RECORD/R2.md` (endpoint core), `RECORD/R3.md` (conformance theorem), `RECORD/R4.md` (wire differential), `RECORD/R5.md` (demonstration), with the goal and boundary rationale in `RECORD/EndpointTrack.md`.

The trust chain is three links, and only the middle one is trusted:

1. **The protocol core conforms to the specification** — stated at the frozen type in `Contracts/EndpointConformance.lean`, proved in `Proofs/EndpointConformance.lean`, bound by `Contracts/EndpointAcceptance.lean`. Its content is the plumbing between two independently written constructions; a defect inside `Spec.Connection.step` is inherited rather than caught, and finding one is the corpus's and the differential's work.
2. **The compiled binary refines the source — trusted, and disclosed.** Lean's compiler and runtime are not verified; the claim is disclosed the way `native_decide` is, in `HANDOFF.md` and in the trust gate's inventory.
3. **The binary behaves as the corpus says** — the wire differential (`tests/contracts/r4_wire_differential.sh`) replays the corpus against the shipped binary over a socket and compares per vector against `amqp-spec`; the shell's forced obligations are driven by `tests/contracts/r2_endpoint_shell.sh`.

Two boundary decisions, with their reasons: **our own socket shim, not the stdlib's TCP** — what gets trusted decides it: a small POSIX wrapper plus the kernel's ABI, rather than libuv's asynchronous machinery inside the unnamed part of the trust base (measured working and not chosen; `RECORD/EndpointTrack.md`). The `@[extern]` surface is pinned to `lean/Impl/Transport.lean` by the trust gate, which prints the count, and nothing else in `lean/Impl` may import it or be `unsafe` — so "only the boundary module here is not proved" is a property of the directory, checked rather than read. **And the shell lives in `lean/Shell/`, outside `lean/Impl/`** — the driver owns `IO` and must import the boundary, and keeping it out of `Impl` is what makes the directory's claim a fact about its files rather than a reading of the imports; the trust gate checks that half.

**What this track does not claim.** Not that the binary is verified — the compiler link is trusted and disclosed. Not that the shell is proved; it is the named hole, kept small enough to read. Not performance: the endpoint is a reference to compare against, and measurement belongs to TemperMint. And not that the endpoint replaces the second reading in `lean/Ref/`: the differential between two independent readings of the standard is a check on *the specification*, and a third runner over the same corpus does not make it redundant.

### 23.2 The demonstration server

Superseded by §23.4: the node-server scope, its two reviews, and the seam analysis are `RECORD/R5.md`. What stands: a demo shows no live fan-out (the shipped shell serves one connection at a time, deliberately), the demonstration worth building is the specification narrating live traffic (§23.4 item 3), and a demo is not worth widening the trust base for.

### 23.3 The server's remaining obligations: what is a gap and what is the standard's boundary

What a server must *do* that the specification does not yet state or enforce, in five categories — each pointing at the record that carries the details, because those records move (`RECORD/R5.md` keeps the full text):

1. **Terminus behaviour is the standard's own boundary, not a gap** — routing, queues, filters, `dynamic`, node properties are `out-of-scope:` in the dispositions; a server implementer brings them from elsewhere.
2. **The model's restrictions are recorded where they live** — the D4 model-restriction record and the widening its fourth trigger scheduled are `RECORD/S1.5.md` and `RECORD/Widening.md`; the register entries (e.g. `interleaved-deliveries-absorbed`, `link-uniqueness-vacuous`) remain the record of what the model does not represent.
3. **Obligations the standard places on any peer that the model does not yet enforce** — the ledger's `deferred:` dispositions are the live, named list; `vectors/generated-exchanges.ndjson` and `vectors/isolation.md` carry the widening's failure-first boundary scenarios.
4. **Time** — `open.idle-time-out` is `environment: implementation-idle-policy`; the interface carries an opaque `tick` and nothing in the semantics consumes it: the boundary of what a step relation over frames can state.
5. **Host-level assumptions** (`server-hostname-default`, TLS/SNI, `tcp-ordered-stream`, `tcp-close-order`) sit in the ledger beside the clauses they qualify.

### 23.4 The route to a real server: what stays, what leaves, and what the demo should be

**Partly adopted.** Item 5's order is the programme of record for this repository (§21). Items 1–4 remain the recommendation that explains that order (full text: `RECORD/Framing.md`), and §23.5's second repository remains unadopted.

1. **The boundary is measured, and it decides the split** — a broker built in this tree would be the first artefact here not checkable against the standard, the one property the tree exists to keep.
2. **What stays here** — the protocol, the corpus, the differential, the proved core, and the server narrowed to what this repository can state.
3. **The demonstration worth building is the specification narrating live traffic** — a real third-party client at one end, the verdict, condition and rule in words per frame, one mutation client whose violation is refused and quoted; it needs no node model and no seam migration.
4. **The real server belongs in another repository, and its first artefact is its own specification** — the *method* is the transferable part; its protocol half is checked by this repository's corpus and `r4_wire_differential.sh` whatever language it is written in.
5. **Order, adopted** — the widening first, then S5's message layer, then the narrator demonstration; the node server leaves this tree entirely.

### 23.5 The second repository — a name, a first artefact, and an interface

**Recommended rather than adopted** — adopting §23.4 item 5's order does not adopt this second repository, its name or its interface (full text: `RECORD/Framing.md`). The name on the table is **`SpecMQ`**, the node layer above AMQP 1.0 core: its first artefact is a clause-level ledger of the node model, authored the way this repository authors its own, because the method is the transferable thing; its interface to here already exists — the corpus and `r4_wire_differential.sh` check any shipped binary in any language by running it. Smallest first: a queue with settlement at the node, and nothing else, until that much has a specification, a proof and a gate; and it should read AMQP Management and use the core's capability fields before inventing a publication format.

## 24. The widening — decisions

The widening adds link identity, the unsettled map and the sender's delivery bookkeeping to the session model, discharging the resumption-family obligations the one-link model could not represent. Its full contracts — the four parts, the clause set in vector order with the failing-before observations, the readings the vectors rest on, and the state shape's obligation table — are `RECORD/Widening.md`. The decisions, each with its one-line reason: **the alphabet does not change** — the widening adds state, not events; the frames the widened rules decide on are the frames the interface already carries — and:

- **The interface extends by addition, not edit** — `Contracts/EndpointConformance.lean` is not touched, because a contract edited after its proof is a contract nobody can audit; the widened statement is frozen beside it and the projection (on the fragment the old model reaches, the relations agree) is stated as a theorem, so "extends" is a claim about terms rather than intent.
- **One shipped core** — the rung makes `Impl.Core.State` exactly `WidenedImplementationState` and R3 remains proved at its own frozen type; there is no adapter, second implementation, or second shipped-state shape, because a second shape is one more thing to keep agreeing.
- **The registry is keyed by name plus local role** — handles cannot identify a link: both endpoints may use handle zero and either handle may move while the logical link survives, and the standard gives link names no grammar, so `LinkId` is the uninterpreted name plus the local role.
- **The unsettled history is single** — two link records would let the two independent readings agree while the two handle spaces silently accumulated different unsettled maps; one tag-keyed table holding both endpoint states per entry makes that divergence unrepresentable and makes the standard's comparison clause statable.
- **Handle-less and tag-less operations traverse finite, exact key indexes** — `linkKeys` and `unsettledKeys` carry keys only, so a disposition ranges over every matching link and entry without any index becoming a second source of protocol state.
- **What the harness cannot pin stays a proof obligation** — the corpus observes per-step verdicts, so spontaneous emissions and held comparisons have no observable there; those clauses remain named obligations in `Proofs`, and a theorem about a desired condition is not counted as a theorem that the endpoint emitted the frame.

## 25. Open questions and remaining obligations

- **V3 third-party captures** — outstanding by design: recording requires an independent implementation to talk to, capture is a manual off-gate activity, and no capture is committed yet. The requirement stands: a capture of the same exchange from an independent implementation, committed under `vectors/recorded/` with provenance. **The UTF-8 lemma** — octets that decode to a text re-encode to those octets: stated nowhere in core or batteries (a measured absence); it stays an explicit conditional premise (D3), blocking the narrowest-form law's two text families, whose remaining steps are the dispatch case analysis and the composition, recorded with their entry points in `RECORD/S1.5.md`.
- **The writer law (`ValueWriterAgree`)** — undecided: refuted unrestricted, restated over the reader-reachable domain, its classing done; the endpoint-level refutation the classing made expressible is landable and not yet landed (`RECORD/ConformanceInterface.md`).
- **The transport-role correspondence** (`version-negotiation.5`, `sasl.8`) — corpus-unreachable by construction, so its carrier is the theorem; deferred with its cost now known rather than guessed (`RECORD/FINDINGS.md`).
- **The widening's unpinnable clauses** — the clauses whose obligations are emissions or held comparisons remain named proof obligations, not corpus steps (§24).
- **S5's acceptance remainder** — the message layer's contract and round-trip proof, planner-authored like every acceptance declaration; S6's caveat is the same shape (`RECORD/S1.5.md`'s amendment record).
- **The remaining deferred clauses** — the ledger's `deferred:` set; dispatches ask for the costing as well as the site (§21 item 2). **A derived-instance trust check** — whether any accepted theorem's dependencies include a derived instance (`deriving` is opaque to the kernel and invisible to the source scan) is named and not yet a gate (`RECORD/FINDINGS.md`). **H1** — the handoff document itself.
