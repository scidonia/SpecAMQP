# SpecAMQP — development programme: a correct, executable AMQP 1.0 specification

## Goal

Produce, in this repository, **a complete, correct, executable formal specification of AMQP 1.0 core** (OASIS Standard, Parts 0–5) in Lean 4, faithful to the OASIS Standard, with a clause-level ledger that makes *completeness* and *fidelity* measured properties rather than claims, and with a defined conformance interface so that downstream work — a Rust implementation, its extraction, and its proofs, which belong to TemperMint, not here — has a definite target.

This repository holds the specification, the evidence that it is correct, and a **reference implementation written in Lean**. The two are deliberately separate artefacts: the specification is declarative, generated-table-driven and shaped for proof, while the reference implementation is operational, independently written from the same clauses, and compiled to a native executable by Lean itself — so its behaviour rests on no translation step. Differential testing runs the implementation against the specification and against recorded third-party exchanges; the corpus, not either artefact, is what both are measured by.

Nothing here is Rust: extraction through Charon and Aeneas, proofs about a Rust programme, and performance work remain downstream (§23). What this repository now provides to that work is an executable oracle.

## 1. What "a correct specification" means here

Correctness of a specification is not a vibe, and it is not "it type-checks". Five properties, each with a mechanism and an observable gate:

| Property | Statement | Mechanism |
| --- | --- | --- |
| **Completeness** | every normative statement in the pinned OASIS artifacts is dispositioned; every MUST-class statement is either formalized or recorded as an environment/out-of-scope assumption with a reason | clause ledger (§6) with coverage report |
| **Consistency** | the specification does not contradict itself: encodings round-trip, invariants are preserved, no illegal transition is silently permitted, no obligation leads to a state where it cannot be met | theorems in `lean/Spec`, `lean/Contracts` (§9), executability gate |
| **Fidelity** | the formalisation says what the OASIS text says, and admits what conforming implementations actually do | clause citations in the ledger, ambiguity register (§8), third-party vector admission (§12 V3) |
| **Discrimination** | the specification is neither vacuous nor over-permissive: it admits the legal and rejects the illegal, with named error conditions | witness/counter-witness vector pairs (§11), specification-mutation controls (§12 V4) |
| **Usability** | the specification is executable, and conformance is defined precisely enough that a third party can be checked against it | executable driver (§9), conformance interface (§10) |

Completeness is measured against the pinned artifacts, never asserted. The ledger (§6) is generated from the vendored bytes; these are its numbers:

| Measure | types | transport | messaging | transactions | security | overview | total |
| --- | --- | --- | --- | --- | --- | --- | --- |
| clauses | 6 | 226 | 90 | 36 | 22 | 21 | **401** |
| MUST-class | 4 | 117 | 57 | 29 | 12 | 11 | **230** |
| — MUST / MUST NOT | 4 / 0 | 94 / 23 | 38 / 19 | 24 / 5 | 12 / 0 | 9 / 2 | 181 / 49 |
| SHOULD / SHOULD NOT | 0 / 0 | 32 / 4 | 13 / 7 | 5 / 1 | 6 / 0 | 4 / 0 | 60 / 12 |
| MAY | 1 | 69 | 12 | 0 | 4 | 2 | **88** |
| RECOMMENDED / REQUIRED | 0 / 0 | 3 / 1 | 0 / 0 | 1 / 1 | 0 / 0 | 3 / 2 | 7 / 4 |

The declared surface, from the same parse of the pinned bytes (not a text scan): **96 types** (24 primitive, 39 restricted, 33 composite), **125 fields** (25 `mandatory="true"`, 27 with a declared `default`, 13 `multiple`, 19 `requires`), **54 choices**, **40 descriptors**, **39 encodings**, **13 named constants** (`<definition>`), 31 sections, and 5 types providing error conditions holding 25 error-condition symbols.

A crude keyword scan of the raw files — the numbers this programme was originally sized with: 222 MUST-class, 70 SHOULD, 85 MAY over Parts 1–5 — is reconciled against the ledger in `ledger/reconciliation.json`, with every difference attributed to a named mechanism: Part 0 was outside that scan; keywords inside `<picture>` diagrams and the `revhistory`/`acknowledgements` sections are not normative statements; and a `MUST NOT` broken across source lines was counted as a plain MUST. Two further crude-scan artifacts are recorded in this section rather than in that file, because they concern the declared surface rather than clause counts: the scan's field count included an *escaped documentation example* (`&lt;field … mandatory="true" …&gt;`, Part 1's illustration of a book type) that the parse correctly ignores, which is why this plan lists 25 mandatory fields where the scan said 26; and the scan's `REQUIRED` count included an adjective use ("the idle timeout REQUIRED by the sender"), now dispositioned `informative`.

Scan numbers size the work; the ledger is the work.

**Done** means: every clause dispositioned; every MUST-class clause formalized or explicitly assumed, with reviewer sign-off; the declared surface covered by generated tables rather than transcription; the vector corpus passing with the executable specification and with third-party admissions; the mutation controls firing; and no `sorry`, no `noncomputable` definition, and no unaudited axiom.

## 2. Deliverables

| # | Deliverable | Location |
| --- | --- | --- |
| D-a | Vendored, hash-pinned OASIS artifacts plus copyright notice | `spec/oasis/`, `spec/oasis/NOTICE` |
| D-b | Clause ledger, dispositions, coverage report | `ledger/` |
| D-c | Ambiguity register with adopted readings and evidence | `ledger/ambiguities/` |
| D-d | Generated definition tables (descriptors, fields, choices, encodings, error conditions) | `lean/Generated/Oasis/` |
| D-e | Executable Lean specification of Parts 0–5 | `lean/Spec/` |
| D-f | Acceptance declarations for every specification claim | `lean/Contracts/` |
| D-g | Conformance interface: the definition of what it means to implement this specification | `lean/Spec/Conformance.lean` |
| D-h | Specification test vectors: positive, negative, and recorded third-party | `vectors/` |
| D-i | Executable driver over the vectors (`lake exe amqp-spec`) | `lean/Spec/Exec.lean` |
| D-j | Handoff notes for downstream implementation work | `HANDOFF.md` |
| D-l | Reference implementation of the type system in Lean, independent of `Spec.*`, compiled to a native executable | `lean/Ref/`, `lake exe amqp-ref` |
| D-m | The type-system vector corpus and its schema, authored from the artifacts' worked examples | `vectors/primitives.ndjson`, `tests/contracts/value-vector.schema.json` |

## 3. Non-goals

- **No Rust, no extraction, no performance work.** The reference implementation is in Lean, and it is the only implementation here. A Rust programme, its extraction through Charon and Aeneas, proofs about it, optimised candidates and measurements belong to TemperMint and are scheduled there (§23).
- **No claims about the reference implementation's conformance beyond its corpus.** It is an implementation, not a proof: what it satisfies is stated by the vectors it passes, and a clause it does not yet exercise is a clause it does not yet demonstrate. The specification's theorems are about the specification.
- **No protocol extensions.** AMQP management (`amqp-man`), filter expressions (`filtex`), claims-based security (`amqp-cbs`), addressing, JMS mapping, HTTP-over-AMQP, event streams, and connection-info are out of scope; they exist as working drafts in `oasis-tcs/amqp-specs`, not as part of the OASIS Standard for core AMQP 1.0. Core must nonetheless model how unknown described types and pass-through annotations are handled.
- **No broker or queue semantics.** AMQP core defines links and termini, not what a destination does with a message. `source`/`target` are formalized as protocol-visible field sets and obligations, not as a routing model.
- **No TLS, no TCP/IP, no crypto.** Security-layer negotiation is specified; TLS, the byte stream, and mechanism-specific cryptography are environment assumptions, recorded as such in the ledger.
- **No verified native execution claims, and no claims about any programme.** The specification states what a conforming endpoint does; it does not certify anything.
- Calendar promises. Progress is reported in coverage units: clauses dispositioned, declarations, vectors, theorems.

## 4. Normative source and pinning

Vendor the six Part 0–5 XML artifacts byte-identically at `spec/oasis/`, with SHA-256 recorded in `toolchain/sources.toml` and the OASIS copyright/citation notice retained alongside (the OASIS notice permits redistribution of the whole with the notice intact; the files MUST NOT be modified). `scripts/fetch-oasis.sh` populates `spec/oasis/` and refuses to proceed unless every hash matches `sources.toml`; the vendored copies are committed, so all later work is offline.

Two structural facts about these artifacts, verified against the pinned bytes, drive the design:

1. **The definition language is present and machine-readable**: `type` (with `class` ∈ {primitive, restricted, composite}), `field` (with `type`, `mandatory`, `default`, `label`), `choice` (with `value`), `descriptor` (with `code` as `domain:descriptor`, e.g. `amqp:open:list` = `0x00000000:0x00000010`), `encoding` (with `code`, `category`, `width`). Sections carry stable `name` attributes (`framing`, `sessions`, `links`, `performatives`, `txn-declare`, `primitive-type-definitions`, …) which anchor every clause identifier.
2. **Behaviour is prose.** The artifacts contain no state-machine element type: only prose `<doc>` text with normative keywords, plus `<picture>` diagrams. Framing, connection/session/link lifecycles, window arithmetic, settlement, and transaction rules exist only as normative English.

Consequence, and the core methodological decision of this programme: the specification is built from **generated tables for the declared surface** (codes, field order, mandatory flags, defaults, choices, encodings) and **handwritten semantics for behaviour**, bound by contracts that make a mistyped descriptor code impossible to introduce silently.

## 5. The specification's own independence rules

Three independence rules keep the evidence meaningful, and each has a gate (§17):

1. **Generated tables are data, not semantics.** `lean/Spec` may import the generated tables through a binding layer; semantics are handwritten. A generated table is never the authority on behaviour.
2. **Vectors are authored from the clauses and from recordings, never from the executable specification.** A vector produced by running the specification would only prove the specification equals itself. The author of a vector reads the OASIS text (or a recorded third-party exchange) and writes down what must happen.
3. **No clause's meaning may live outside the ledger.** Every normative statement's disposition points at the declaration, assumption, or vector that carries its meaning; an undocumented convention is a defect.

## 6. The clause ledger

`scripts/clause-ledger.py` reads only the pinned artifacts and emits `ledger/clauses.json`: one record per normative statement, deterministically ordered.

- **Identifier**: `<artifact>#<anchor path>.<n>`, e.g. `amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions.42`. The anchor path is the chain of enclosing named elements (`section:framing`, `type:open`, `field:max-frame-size`, `doc:doc-idle-time-out`), because a bare `name` is not unique — `field name="value"` occurs inside many types — and `<n>` is the 1-based index of the statement within that anchor in document order. Anchor paths are what make ids stable under unrelated edits elsewhere in the artifact.
- **Fields**: artifact, anchor, index, kind (`MUST` | `MUST NOT` | `SHOULD` | `SHOULD NOT` | `MAY` | `REQUIRED` | `OPTIONAL` | `RECOMMENDED` | `NOT RECOMMENDED`), class (`MUST` for both MUST forms, else the kind), normalised text, text SHA-256, statement SHA-256, and the names of any `<xref>` elements the statement cites.
- **Cross-references are resolved for the reader**: `<xref name="MIN-MAX-FRAME-SIZE"/>` renders as `512` through the generated `<definition>` constant table (13 constants, resolved across artifacts because Part 5 cites a Part 2 constant), while a reference to a named element renders as `«open»`. A constant's value changing changes the clause text, so its disposition goes stale — which is the intended behaviour, since that is a semantic change. Cross-artifact references are recorded per clause so the link survives resolution.
- **Normalisation** must handle the real markup: inline emphasis around the keyword (`<b>MUST</b>`), keywords split across source lines (`MUST\nNOT`), entity-encoded text, and must not treat `<picture>` diagram text, `revhistory`, or `acknowledgements` content as normative. This is a token-aware scan, not a regular-expression grep, and it is verified by planted negative controls (§17).
- **Dispositions** (`ledger/dispositions/*.json`, planner-authored) key on `(id, text_sha256)`, so a source change that alters a clause's text makes its disposition stale and fails the contract — the mechanism that prevents silent drift between the OASIS source and the formalisation.
- **Disposition values**: `formalized:<Lean declaration>`, `deferred:<milestone>` (a real obligation this plan carries later; the suffix names the milestone, so deferred work is visible rather than conflated with work we decided is not ours), `environment:<id>` (an assumption discharged by the environment model, e.g. "TCP delivers an ordered byte stream"), `out-of-scope:<reason>`, `underspecified:<id>` (the artifact deliberately leaves behaviour open: nothing is enforced, and tests must not assert either reading), `informative` (explanatory, with justification), `test:<vector id>` (a statement whose only observable form is a vector expectation), `superseded:<decision id>` (decided by an entry in the ambiguity register, §8). The last two additions were forced by real statements that fit none of the first six: S3's messaging obligations are ours and not yet carried, and the two hostname sentences are explicit silence rather than a scope decision.
- **Statements without keywords are captured too.** A paragraph can state a requirement without an RFC 2119 keyword — Part 1's map type says "A map in which there exist two identical key values is invalid", one sentence among two MUST clauses — and a keyword-driven ledger reports completeness while losing it entirely. Ten keyword-free sentences matching a normative phrasing were captured; one was the specification's own definition of the keyword vocabulary rather than a requirement, and is excluded, leaving nine. Each becomes a statement of kind `UNKEYED` and `check_unkeyed` fails until it carries a disposition, so an omission is a decision. One of them turned out to be an instance of a rule already formalised (`Spec.Value.MultipleMandatory`, applied to `sasl-server-mechanisms`, which the artifact declares `multiple="true" mandatory="true"`), three are explicit silence about repeated hostnames and TLS mismatch, three are rationale or a reserved name, and two are deferred to S3. The gap this closes is a *class* of omission, not one sentence: the check is run per sentence, because a unit-level check loses the keyword-free sentence of a paragraph whose other sentences have keywords.
- **Pictures are reviewed, not merely skipped.** 104 pictures are excluded from clause extraction because most are sequence diagrams — but five carry formal grammar or normative keywords, including Part 1's formal constructor BNF, which is the specification's own statement of which octets are format codes, and two Part 3 diagrams that state the receiver's `resume=true` obligations. Those are listed in `ledger/pictures.json` with a content digest and flagged `looks_normative`; `check` fails until each carries a disposition keyed to that digest, and fails again if the picture's text changes. Excluding a subtree is a decision, and the ledger makes it one.
- **Coverage report** (`ledger/coverage.json`) aggregates per artifact and per anchor, and is regenerated per milestone; acceptance commands diff it against the previous milestone's report so a coverage regression is visible rather than merely regrettable. It also reports picture coverage: total, reviewable, dispositioned.
- **No clause can escape the ledger.** A crude token census (every text node, split by whether it sits in an excluded subtree) is compared against what the ledger accounted for, per artifact and per keyword; a keyword token in non-excluded prose that produced no clause fails `check` and names the offending element and text. This gate is what makes the ledger's completeness a measurement of the walk rather than a property of its author.
- **The baseline reconciliation cannot drift.** `ledger/reconciliation.json` records the crude-scan numbers per artifact, this ledger's numbers, and the named mechanism explaining every difference; `check` fails if the recorded numbers stop matching the generated ledger, so revising the ledger means revising the record deliberately.

## 7. Generated definition tables

`scripts/gen-oasis-lean.py` reads the pinned bytes and emits `lean/Generated/Oasis/`, one module per declaration kind:

| Module | Contents | Records |
| --- | --- | --- |
| `Constants.lean` | the `<definition>` constants, with `constantValue?` lookup | 13 |
| `Types.lean` | declared types, their class, source, semantic `provides` roles, descriptor, and artifact anchor path | 96 |
| `Fields.lean` | fields in wire order with owner, index, type, mandatory flag, declared default, `multiple`/`requires`, plus `fieldsOf`/`mandatoryFields` | 125 |
| `Encodings.lean` | the 39 encodings with constructor octet, category, size width, and `encodingOf` | 39 |
| `Choices.lean` | declared choices, the error-condition families, and `errorConditionsOf` | 54 |
| `provenance.json` | the artifact digests and record counts the modules were derived from | — |

Contracts, all enforced by `tests/contracts/s0_tables_fidelity.sh`:

- **currency**: a fresh generation is byte-identical to the committed modules, so the tables are derived rather than transcribed;
- **load-bearing**: replacing `amqp:transfer:list`'s code with `disposition`'s in a scratch copy of Part 2 changes the generated tables and makes the currency check fail — the gate is not vacuous;
- **counts**: an independent count of the pinned artifacts equals the generated record counts;
- **no smuggling**: no file under `lean/Spec`, `lean/Contracts` or `lean/Proofs` may contain a literal descriptor code or an `amqp:`-shaped symbol — they come from these modules;
- **compilation**: the generated modules build against the pinned closure.

Two normalisations are deliberate and documented in the generator. Labels — the human-readable attribute text — have whitespace runs collapsed so generated diffs stay stable; no data field (value, code, flag, default) is touched. And each declaration carries the anchor path it came from, which is what links a generated record to the clause ledger's identifier for the same element.

Module naming is path-derived (`lean/Generated/Oasis/Types.lean` → `Generated.Oasis.Types`), and each generated module is self-contained: `Choices.lean` imports `Types.lean` because the error-condition lookup needs the type table, and nothing else.

## 8. Ambiguity register

AMQP 1.0's prose is not uniformly exact; several areas admit two readings, and real implementations disagree in practice. `ledger/ambiguities/*.json` records, per issue: the clause ids involved, the candidate readings, the reading adopted, the evidence (clause citation, third-party behaviour), and the consequences for the conformance relation.

Entries opened at S0, from the clauses inspected while writing this programme:

- session window recomputation (`next-incoming-id` / `incoming-window` derivation of `remote-incoming-window`, Part 2 `#sessions`) and which window updates are "MAY (depending on policy)";
- `open.idle-time-out` — the local threshold rule, the halving recommendation, and which peer closes;
- `attach.initial-delivery-count` versus the first `flow.delivery-count`, and what a receiver must infer;
- `flow.available` for senders that cannot determine availability;
- link resumption: which fields change identity versus state;
- message fragmentation: the `more` flag, session-window interaction, and abort semantics;
- `received` (`section-number` / `section-offset`) obligations for partially transferred messages.

Adopting a reading is a decision *with evidence*, recorded in the ledger as a `superseded` disposition pointing at the decision. Where a mainstream implementation disagrees with our reading, the disagreement is a recorded finding, not a licence to weaken the specification — the specification states what the OASIS text requires, and the register states where practice diverges.

## 9. Specification architecture (Lean)

```
lean/Spec/
  Value.lean        AMQP type system: the value domain and all 39 encodings
  Wire.lean         frame header, extended header, frame types 0x00/0x01, channel,
                    protocol header and version negotiation, frame-size limits
  Performative.lean the 14 frame-level performatives as one inductive, bound to the generated descriptors (forty descriptors exist across the declared types; fourteen are dispatchable performatives)
  Message.lean      Part 3: sections, annotations, fragmentation, outcomes
  Endpoint.lean     connection/session/link state machines, error taxonomy
  Flow.lean         windows, credit, delivery numbers, drain/echo, handles
  Transaction.lean  Part 4: coordinator, declare, discharge, transactional state
  Sasl.lean         Part 5: SASL framing, mechanism negotiation, layers
  Conformance.lean  the interface alphabet and the definition of conformance (§10)
  Exec.lean         executable driver: vectors in, verdicts out
```

Requirements:

- **Executable.** Every definition in `Spec/` is computable; `Exec.lean` runs the vector corpus and reports per-vector verdicts. `noncomputable` and `partial` are rejected by contract.
- **Total where the protocol is total.** Decoding functions return an explicit error result rather than a default; there is no silent truncation and no "best effort" parse.
- **Independent of consumers.** No `Spec/` declaration refers to any implementation, module path, or artifact outside `lean/` and `spec/oasis/`.
- **Nondeterminism is explicit.** Where the OASIS text says MAY, the choice is a first-class input to the specification (a policy stream), not a hidden decision inside a Lean definition. This is what makes the specification testable and what keeps it from being accidentally narrower than the standard.
- **Canonical encodings are specified.** The type system is formalized with specificity preservation, so round-trip theorems hold on a stated equality class rather than on "some bytes came back".

## 10. The conformance interface

The specification must define what it means for an endpoint to conform, or downstream work has no target. Fixed at S0/S1 and frozen thereafter. An endpoint is a state machine over an interface alphabet:

```lean
inductive Input  where | frame : Bytes → Input | api : ApiCall → Input | tick : Tick → Input
inductive Output where | frame : Bytes → Output | api : ApiResponse → Output

structure Endpoint (σ : Type) where
  init   : σ
  step   : σ → Input → Option (σ × List Output)      -- implementation: partial function
  choose : σ → Input → Set (σ × List Output)         -- specification: relation
```

with conformance defined as simulation preserving **identical output sequences**:

```lean
def Conforms (spec : Endpoint σs) (impl : Endpoint σi) : Prop :=
  ∃ R : σs → σi → Prop, …   -- init related; every impl step matched by a permitted spec step
```

Defining rules, decided here so the specification is not retrofitted later:

1. **Output agreement, not trace inclusion.** An endpoint's observable output *is* the wire, so an implementation must emit exactly a sequence the specification admits. This is what makes "implements AMQP 1.0" a definite statement rather than a family of interpretations.
2. **Specification nondeterminism is a set.** `MAY`-clauses and policy-dependent window updates produce sets, and the *adequacy* obligation runs the other way from the safety obligation: the relation must admit every behaviour a conforming third-party implementation exhibits. A third-party vector the specification rejects is a bug in the specification (§12 V3) — the class of defect this repository exists to prevent.
3. **MUST versus SHOULD.** MUST-class clauses become obligations inside `choose`. SHOULD-class clauses become either fairness-qualified progress obligations or recorded freedoms, each with a ledger disposition; a SHOULD is never silently promoted to a MUST.
4. **Progress is part of conformance.** Where the specification requires an endpoint to act — send a mandated error, respond to `drain`, complete a close handshake — the obligation is a deadlock-freedom property under a stated fairness assumption, enumerated from the ledger rather than invented.
5. **Bounded resources are explicit.** Capacity exhaustion is specified behaviour with a mandated error code (`amqp:resource-limit-exceeded`, `amqp:frame-size-too-small`, `amqp:connection:framing-error` as the clauses direct), so an implementation that runs out of room is incorrect in a checked way rather than silently lossy.
6. **Anchored in an environment model.** The peer, the ordered byte stream with arbitrary fragmentation, timers as explicit ticks, and TLS/crypto as opaque are named assumptions, each with a ledger disposition. A claim that rests on one says so.

Proving an instance of `Conforms` for a concrete programme is downstream work (§23) and requires the extraction toolchain; defining it correctly is this repository's job, and it is the reason the interface is frozen before any implementation exists.

## 11. Specification test vectors

One shared format for everything the specification is tested against: NDJSON, schema-validated (`tests/contracts/vector.schema.json`), **logical time only** — timestamps are ordering tags, never wall-clock, so replay is deterministic on any machine.

```json
{"vector":"span-004","kind":"positive","provenance":{"role":"server","source":"clause",
   "refs":["amqp-core-transport-v1.0-os.xml#sessions.42","…#flow.7"]},
 "steps":[{"dir":"in","bytes":"414d515000010000"},
          {"dir":"out","expect":"bytes","bytes":"…"},
          {"dir":"out","expect":"action","action":{"kind":"credit","link":0,"value":100}},
          {"env":{"tick_ms":500}}]}
```

- `kind` is `positive` (must be admitted, with the named outputs), `negative` (must be rejected with a named error condition and the mandated close/detach behaviour), or `recorded` (captured from a third-party implementation, provenance mandatory: peer implementation and version, capture date, and the transcript hash kept out-of-tree).
- `dir:"in"` is peer→endpoint, `dir:"out"` is endpoint→peer; `expect` distinguishes byte-identical output from a typed action where the specification permits latitude (for example fragmentation split points).
- `refs` cite the clauses a vector is testing, and the coverage report cross-checks them against the ledger, so vectors cannot accumulate free of the clauses they claim to exercise — and clauses cannot be claimed as tested by vectors that do not cite them.
- **Authoring rule (§5 rule 2)**: vectors come from the clauses or from recordings. A vector generated by running the specification is not evidence.

Negative vectors carry the error-condition expectation explicitly, because "it fails" is not a specification — "it fails with `amqp:decode-error` on channel 3, after which the connection is closed" is.

## 12. Correctness evidence

Four tiers, all offline, none requiring an implementation to be written here:

| Tier | Question | Mechanism | Failure it detects |
| --- | --- | --- | --- |
| **V1** | is the specification internally consistent? | theorems: round trips, canonicality, invariants (window and credit conservation, handle uniqueness, delivery-number monotonicity), reachability of every state with a mandated exit | contradictions, dead ends, silent acceptance of an illegal transition |
| **V2** | does it discriminate? | the positive/negative vector corpus, run by `lake exe amqp-spec` | over-permissiveness, missing error paths, vacuous definitions |
| **V3** | is it faithful to reality? | recorded third-party vectors must be **admitted** by the specification, and reproduced where the specification fixes bytes | **over-narrow specification** — the defect class that makes formalisations useless in practice |
| **V4** | would the corpus catch a wrong specification? | specification-mutation controls: planted mutations (a dropped MUST check, an off-by-one in window arithmetic, a wrong descriptor code in a vendor copy, acceptance of a non-canonical encoding, an out-of-range channel admitted) must each be detected by V1–V3 with the expected diagnostic | a corpus that proves nothing because it cannot fail |

V4 is what makes V2 and V3 load-bearing. A mutation that no tier detects is reported as a suite defect, not quietly tolerated.

**Considered and not adopted: a second formalisation in a second prover.** A parallel Rocq development — specification plus a Gallina implementation, executed through extraction and compared at the wire — would add an independent kernel and an implementation claim with no translation in its trust base; as cross-execution it would also test whether two independent readings agree on bytes. It is not adopted now, for three reasons. The dominant residual risk is prose ambiguity, and two readings by the same reader share their errors, so the cross-check would report agreement exactly where we are most likely to be wrong. Per-clause review is the scarce resource: 230 MUST-class statements each needing a decision with evidence, and a second development makes every one of them land twice, with a second disposition trail, a second gate family (`Admitted`/`Axiom` beside `sorry`/`native_decide`) and a second pinned toolchain. And it does not discharge the Rust trust line, which is the line that matters for a shipped implementation; it converts that trust into a behavioural cross-check, the role V3 already plays with stronger independence.

The option is kept cheap rather than closed: vectors, the verdict schema and the comparison are implementation-agnostic, so any implementation — Gallina, Rust, or a third party's — can be added as a runner rather than a rewrite. Revisit when implementation proofs move to Rocq (the `mechanized-llbc` / RefinedRust lineage, which is where foundational Rust reasoning lives), at which point the specification should live there and Lean becomes the second implementation; or when V3 admission cannot adjudicate a dispute; or when a second kernel is wanted specifically for the specification's own claims. If taken up, the version worth doing first is scoped to Part 1: a Gallina codec executed through extraction, cross-decoded against `lake exe amqp-spec` over an exhaustive short-input byte domain (every input of two octets, and generated longer ones), comparing **wire bytes only** — a mapping between the two developments' internal representations would be a third artefact to trust.

**Rocq support in the pinned toolchain (verified at the pinned revisions).** Aeneas ships four backends — `backends/{coq,fstar,hol4,lean}` — and the CLI selects one with `-backend {coq,lean,fstar,hol4}`. Charon is prover-agnostic: it emits LLBC (with JSON serialisers for ULLBC and LLBC), and the prover choice belongs to Aeneas. The upstream documentation calls Lean "the most mature and actively maintained backend" and says the F*, Coq and HOL4 backends "receive less attention", but the Coq backend is not vestigial: it carries its own test suite (`tests/coq/{arrays,demo,misc}`, with `_CoqProject` templates) at the pinned revision. Our pinned nixpkgs carries `rocq-core` 9.1.1 (with `coq` now an alias for it), which satisfies the Rocq ≥ 9.0 that `mechanized-llbc` needs, so trying it costs no new flake input.

Three different things "Rocq support" could mean for this programme, with different prices:

1. **A second backend for the same Rust** — run the same LLBC through `-backend coq` and you have a Rocq model of the identical source, obtained by translation rather than by a second reading. Cheap: one more emitter run, a second audit family (`Admitted`, `Axiom` beside `sorry`, `native_decide`) and a second executable via extraction to OCaml. It catches emitter defects and mistakes in the *statements* of our theorems, because a statement false of the model is unlikely to hold in a second model of it. It does **not** catch translation defects — the engine is shared — and it does nothing about prose ambiguity. This is therefore a second-kernel cross-check, not the independent formalisation discussed above.
2. **The foundational line** — `mechanized-llbc` mechanises the LLBC model and the soundness of the symbolic execution Aeneas performs, and RefinedRust/RustBelt/Iris live in Rocq. This is the only place a claim not resting on a trusted translation could be built (unsafe code, concurrency, machine-code-level). Choosing it means implementation proofs move to Rocq while the specification stays here, bridged *behaviourally* by the corpus; no logical bridge is planned or claimed.
3. **A hand-written Gallina specification** — the only route to an independent *reading* of the prose, and the expensive one described above. The existence of a Coq backend does not change its cost, because extraction reproduces our reading rather than testing it.

One concrete consequence for contract shapes: the Coq backend's support library models failure as `Failure | OutOfFuel`, so divergence there is fuel-bounded, whereas the Lean backend supports partial functions and extrinsic termination proofs — which is what makes `⦃ result => … ⦄` (`WP.spec`) mean *total* correctness for us. A dual-backend effort would need a fuel formulation on the Rocq side, and the acceptance declarations would stop being copyable between the two.

Recording third-party vectors is a manual, credentialed, off-gate activity: run an existing peer implementation (Qpid Proton, Apache Qpid J/Artemis, RabbitMQ 1.0, Dispatch router — two or more), capture the bytes with harness glue, commit the capture with provenance. No test in this repository contacts a network service, a model, a clock, or a random source; recorded captures replay deterministically offline.

## 13. Milestones

Each milestone: scope, planner contracts, the failure expected before implementation, and observable acceptance. Coverage is stated in ledger terms and superseded by `ledger/coverage.json`.

### S0 — basis, ledger, tables, and the frozen interfaces

Work: vendor the artifacts and notice; write `AGENTS.md` recording repository instructions, contract ownership, and the test-form decisions of §16; write `toolchain/sources.toml` and `toolchain/downstream-pins.toml`; implement the ledger generator and the first disposition pass; generate the tables; land the vector schema; freeze the interface alphabet, the environment assumptions, and the error-code mapping; stand up the executable driver's skeleton.

Contracts: `tests/contracts/s0_sources_ledger.sh` (hashes, ledger generation, reconciliation with the §1 baseline, planted-negative controls), `tests/contracts/vector.schema.json`, `tests/contracts/s0_tables_fidelity.sh` (regeneration determinism and the mutated-vendor-copy control).

Expected failure: `scripts/fetch-oasis.sh` fails on a missing pin; `clause-ledger.py` fails on an unresolved import; the tables contract fails because no generator exists.

**Progress.** S0 is essentially landed. Verified so far: the six artifacts are vendored with hashes and notice, and `scripts/fetch-oasis.sh` refuses a one-bit mutation; `scripts/clause-ledger.py` generates 401 clauses over 230 MUST-class statements across 116 anchor paths with the token census clean and the baseline reconciliation recorded; 39 connection-establishment clauses carry their first dispositions; `scripts/gen-oasis-lean.py` emits the declared surface (13 constants, 96 types, 40 descriptors, 125 fields, 39 encodings, 54 choices) and all five modules compile; the `spec` shell realizes the pinned Lean 4.31.0 + mathlib closure (741 MB store path, 3m35s once, offline afterwards) and provisions a writable copy into the gitignored `lean/.lake`; the vector schema and `toolchain/downstream-pins.toml` are written. Three contracts pass: `s0_sources_ledger.sh`, `s0_tables_fidelity.sh`, `s0_lean_environment.sh`.

Each contract first failed on a real defect, which is why they are worth having: `revhistory` is a section *name* rather than an element tag, so exclusion by tag alone silently kept revision-history prose in the ledger; the tables contract's own independent recount assumed every encoding carries a `name` when 11 do not; and the generated Lean did not compile until `class` (a Lean keyword) became `typeClass` and list elements were separated. The environment contract also caught that the mathlib probe needed `Mathlib.Algebra.Order.BigOperators.Group.List`, the module carrying the `List.Sublist.sum_le_sum` bound that the specification's later aggregation arguments rely on.

Still open in S0: the executable driver's skeleton, which is genuinely the first S1 artifact — `Spec/Value.lean` plus the driver that turns a vector file into a verdict — so the milestone boundary is deliberate rather than a gap.

Acceptance: ledger generated offline from the vendored bytes; every §1 count reconciled with recorded reasons; regeneration byte-identical; sources and ledger gates green with their negative controls observed failing first.

### S1 — type system (Part 1)

Scope: 26 primitive types, 39 encodings, described types, composite encodings, arrays; specificity preservation; the decode-error taxonomy; the Part 1 ABNF cross-checked against the encoding table.

Contracts: `lean/Contracts/TypeSystem.lean` (round-trip and canonicality theorems at exact types), `vectors/primitives.ndjson` (authored from the Part 1 examples and clause text).

**Progress.** The constructor grammar is formalised and its claims accepted. `lean/Spec/Value.lean` classifies a leading octet by the grammar's ranges (`descriptor`, the four categories with their size widths, and `reserved`), and proves by kernel-checked computation that the reserved octets are exactly `%x01-3F`, that the twelve escape octets the grammar reserves for future formats are unassigned in the generated table while still lying in their category's range, that the ranges cover `%x40-FF` with `%x00` as the descriptor prefix and no gap, and that all 39 declared encodings follow the category and width their range gives them. `lean/Contracts/TypeSystem.lean` is the acceptance declaration: the exact proposition, with the acceptance theorem applying the proof at that type. Part 1's six clauses are dispositioned (six `formalized:`, one of which also records a misclassified keyword), and the map-ordering clause opened an ambiguity-register entry, because "maps are ordered unless known to be otherwise" fixes map equality as sequence equality — a decision the value domain must inherit. The picture-review gate that surfaced this work is described in §6.

Two corrections came out of writing the proofs rather than reading them: `decide` refuted my first statement of the reserved set (`List.range 0x40` includes `%x00`, which is the descriptor prefix, not reserved), and the grammar's agreement check had to be a computation rather than a proposition, because instance search cannot unfold a matcher over a computed classification.

Remaining in S1: the value domain (null, booleans, integers, floats, decimals, char, timestamp, uuid, binary, string, symbol, and the compound forms), the reader and writer for all 39 encodings with the decode-error taxonomy, round-trip and canonicality theorems at `Contracts.TypeSystem`'s types, the vector corpus authored from Part 1's examples, and the driver that turns a vector file into per-vector verdicts.

**Progress.** The reference implementation's first slice is landed and passing: `lean/Ref/` reads and writes the type system's primitives, compound lists and arrays with described types, independently of `Spec.*`, with no `partial` (the reader is total, bounded by fuel that decreases at every recursive step), and `lake exe amqp-ref` compiles it to a native binary that consumes the corpus and reports one JSON verdict per vector. `vectors/primitives.ndjson` holds 14 vectors authored from the artifacts' worked examples — the str8 example, the described-URL example, the composite `book` value octet for octet, the narrowest-encoding choices for `uint`, and four rejections (reserved octet, escape octet, truncated string, raised size). `tests/contracts/s1_ref_vectors.sh` passes with a mutation control that corrupts one expected octet and requires the run to fail naming that vector.

The corpus earned its place immediately, finding three things rather than confirming what was written:

* the big-endian writers emitted the least-significant octet first, so `uint 256` encoded to a different number than it decoded from;
* the size check for compound values and arrays measured from the wrong offset, omitting the count field (and, for arrays, the element constructor) that the size counts;
* my own reading of the published composite example was wrong — I had claimed its size octet was a documentation defect, having under-counted the authors array by one octet. The encoder agreed with the artifact octet for octet; the vector was corrected, not the artifact, and `ledger/ambiguities/compound-size-field.json` now records the withdrawal with the corrected arithmetic and closes the question.

**The generated corpus.** `scripts/gen-value-vectors.py` emits 66,517 further vectors and is checked two ways: its encoder must reproduce the artifact's published examples octet for octet, and the committed corpus must reproduce byte-for-byte from the generator. Its families are golden vectors (integer and length boundaries, compound counts either side of the one-octet count boundary, which for maps is 127 pairs (254 items) against 128 pairs (256 items) rather than a round number of pairs, nesting, both descriptor forms), reject vectors (every reserved octet, every escape octet, every proper prefix of every short golden encoding, and size fields moved by one), and a **property sweep over every one- and two-octet input** — 65,792 vectors asserting that whatever decodes must re-decode to the same value. The sweep needs no oracle, which is what lets the domain be closed rather than sampled.

The corpus paid for itself within the hour, finding four defects rather than confirming the implementation:

* the wide-form size field omitted the four-octet count field, so `list32`/`array32` declared a size three octets short of their content;
* array elements were written in whatever form each element would choose alone, instead of the array's declared element constructor — the array said `uint32` while the elements were one-octet small-uints;
* a refactor dropped the wide-constructor selection, so a 256-octet string announced `str8` with a four-octet length;
* two performance defects that made the corpus unusable before they were found: an accumulator that appended to the end of a list (quadratic in the corpus size) and a hex renderer that appended two characters at a time (quadratic in the payload). Both are now linear, and 66,517 vectors run in 0.4 s.

The first two are the interesting ones methodologically: the **generator and the implementation shared them**, which is exactly the correlated-error risk §19 names, and what caught them was not agreement between two encoders but the *reader's* independent measurement of its own size window. An implementation that trusted the declared size would have accepted both.

**Trust accounting is now a gate.** `tests/contracts/s1_proof_integrity.sh` scans the handwritten modules for `sorry`, `admit`, `native_decide`, `partial def`, `axiom`, `constant`, `opaque`, `unsafe`, `extern` and `implemented_by`, with a planted control that hides each construct behind comments and docstrings (so the scanner is shown to read code rather than text), and it prints the accepted theorem's transitive axiom inventory. As of S1 that inventory is `[propext]` — the extensionality axiom the `decide` proofs use, and the expected baseline — with no `sorryAx` and no `native_decide` trust. The scan covers the executable modules too (`lean/Ref`, `lean/Harness`), not only the specification: a `partial` reader in the reference would be a silent totality hole in the oracle the differential contract trusts, and the reference's fuel-bounded reader is now known to be kernel-accepted rather than assumed total.

**The reference codec now covers the whole type system.** Reader and writer handle all 39 encodings, verified by the corpus: 14/14 worked-example vectors and 67,124/67,124 generated vectors, including the new families and their 127/128-pair map count boundary. Two decisions from the review of that slice are worth recording as design:

* **`smallint`/`smalllong` are read but never written.** The artifact lists 0x54/0x55 as format codes, so the reader accepts them with sign extension into the `int`/`long` domain, but the writer emits the four- and eight-octet forms. The choice of encoding for a given value is the implementation's, not the clauses', so this asymmetry is not a conformance question — and the disposition records it as such rather than leaving a reader that admits bytes the writer cannot produce.
* **`unsupported` is a distinct decode error from `unassigned`.** Some element constructors are legal but not read by the reference (arrays of compound elements, and the small/zero/wide forms it does not implement as element data); reporting those as `unassigned` would claim the grammar does not assign them, which is false. A probe pins the taxonomy: an array of maps reports `unsupported` for 0xC1, an array of arrays `unsupported` for 0xE0, while the escape 0x4F and the genuinely unassigned 0x46 report `unassigned`. The same distinction is required of the specification's codec.

**The specification's codec landed and the differential contract is green.** `lean/Spec/Codec.lean` reads and writes the whole corpus vocabulary, built table-driven: it classifies octets through `Spec.Value.classify` and asks `Generated.Oasis.encodingOf` for the declared surface, and it contains **no hand-written octet dispatch at all** (zero occurrences, against 63 in the reference's `match`), importing no `Ref.*` module. That independence is what makes the comparison evidence rather than a tautology, and `tests/contracts/s1_differential.sh` passes with per-vector verdict comparison over both corpora — 14/14 and **67,124/67,124 identical verdicts**, with rejections present and the non-vacuity floor satisfied. Its first run failed on a defect in the contract itself: the loop named its logs after the corpus's *basename* (`ref-primitives.log`) while the non-vacuity check read `ref-worked.log`, and the rejection floor was a flat 8, which a 14-vector corpus cannot carry. Both are fixed, and the floor is now corpus-relative.

**One finding from the codec slice is a real specification defect, not a tooling detail.** The reader threads fuel, and the bound is the octet count. That is harmless for every element whose data has width, but an array of *zero-width* elements — `null`, or the boolean forms, which carry no octets — needs one unit of fuel per element while consuming none, so an array declaring more elements than the buffer has octets is refused although it is a perfectly legal encoding. Reported by the coder with a smoke vector (two elements accepted, ten in a four-octet array refused) rather than silently papered over with `List.replicate`, which would have re-opened an unbounded memory question. The ruling is that the specification must accept it: the element iterator should recurse **structurally on the count from the header**, with fuel reserved for descending into nesting, which is total for the same reason `Nat` recursion is. The reference has the same defect from the same cause. Follow-up: fix both artefacts, and add the corpus family that would have caught it — arrays of zero-width elements with counts from 0 to 257 in buffers smaller than the count, in both the 8-bit and 32-bit forms.

**The zero-width ruling is implemented, on both sides.** The element iterator recurses on the header's count in both readers (fuel stays for descending into nesting), a declared `arrayElementLimit := 65536` bounds materialisation in both, and exceeding it refuses with the class `limit`. The corpus grew by 218 vectors — zero-width element constructors 0x40/0x41/0x42 at counts 0, 1, 2, 255, 256 and 257 in both forms, with a size-mismatch control and an over-limit reject whose reason class is pinned — and both artefacts pass all 67,342. Refusals now carry their class as the leading token of the detail in both artefacts, which required the harness to stop discarding the codec's error.

Two consequences worth keeping, both about where a refusal can happen rather than about this defect:

* **A refusal can be in either direction, and the corpus could only say one of them.** `kind: reject` is a decode expectation: bytes that must be refused. An encoder can also be required to refuse *a value* — an array over the element limit is the first case — and no vector could express that, so `expectError` on `kind: encode` now means exactly that, with the reason class pinned the same way. This closes a hole in the vocabulary rather than working around it, and S2 needs it: a frame too large for the negotiated limit and a performative missing a mandatory field are refusals the *encoder* is best placed to reject.
* **The writer's domain sits inside what the reader accepts.** The element limit exists because reading is where hostile input forces materialisation, so the natural reading is that only the reader needs it. That reading is wrong: the writer must refuse the same values, or it emits octets its own reader rejects and the round-trip law is false for values it produced. Both artefacts therefore carry the limit on both sides with the same number and class, and the differential contract generates an over-limit encode request in its temporary directory to observe the agreement — a 65,537-item JSON line is not worth committing, and the control is worth more than the vector would be.

**S1 is accepted**, on the evidence the plan set out to require: both executables build; the corpora are replayed by each artefact through the same harness (20/20 worked examples and 67,342/67,342 generated vectors, both directions); the differential contract is green with per-vector verdict comparison, its reason-class check, its pinned-reason check, its non-vacuity floor and its generated over-limit encode control; vector ids conform to the schema's own pattern; the trust scan is clean across the handwritten *and* executable modules with the accepted theorem's axiom inventory disclosed as `[propext]`; the ledger check passes with every unkeyed statement dispositioned and the ambiguity register validated; the ABNF/table agreement is a proved theorem; and Part 1's normative clauses are covered.

What S1 deliberately does *not* claim, so nothing reads as stronger than it is: the round-trip and narrowest-form laws are stated in `Contracts/Codec.lean` and unproved (S1.5), and the reference does not read every element constructor the specification reads — the gap recorded immediately below, which is being closed now.

**The element-constructor gap, stated correctly.** Any legal constructor may appear as an array's element constructor, and the reference read only some of them. Part 1's grammar settles what "any" means — `constructor = format-code / %x00 descriptor` with `format-code = fixed / variable / compound / array`, so the element constructor is a `constructor` and the array category is one of them — and the encodings section adds no exclusion. The reference was missing `smalluint`/`smallulong`, `uint0`/`ulong0`, `list0`, boolean, short/int/long, the wide variable-width forms, `described`, **and the array category** (`0xE0`/`0xF0`), which the specification already reads and writes. An earlier version of this record said "arrays of compound elements", which undersold it: the grammar admits the array category too, and the record now cites the production rather than a reading. Note where that grammar lives — in a picture, already dispositioned as normative for this reason, the same pattern as the frame header's layout. Its evidence for the codec's laws is the corpus and the differential agreement between two independent derivations — which is strong, and is not a proof, and the plan says which is which.

**The package build is fixed, and the cause is worth keeping.** `lean/lakefile.lean` now gives each of the five libraries its globs. Lake's default for a `lean_lib Foo` is `roots := #[Foo]` and `globs := roots.map Glob.one`, i.e. a glob for a *root module* named `Foo`; no `Generated.lean`, `Spec.lean`, `Contracts.lean`, `Harness.lean` or `Ref.lean` exists, because the content lives one directory down. A `Glob.one` yields its name without checking that a source file is there, so each library's module set held that phantom module, resolving its imports failed, and the library's `modules` facet reported "some modules have bad imports" at job computation — which is why only a *bare* `lake build` failed while every acceptance command, all of them targeted, was green. Each library now declares `globs := #[.submodules \`Generated]` and its siblings, with `roots` left at its default so the modules stay local to their library. `Glob.andSubmodules` would have been the wrong glob — it selects the bare name unconditionally, which is the phantom module again — so the comment records that a root module added later must widen its glob in the same change, or the new module would sit silently outside its library. Verified: bare `lake build` 21 jobs, the five library targets 4–9 jobs each, targeted module and executable builds unchanged at 23 jobs, a clean cache-disabled build enumerating all fifteen modules, and `s0_lean_environment` / `s0_sources_ledger` / `s0_tables_fidelity` all passing.

### S1.5 — the codec's laws, proved in rungs

`Contracts/Codec.lean` states `RoundTripOnEncodedValues` and `NarrowestEncoding`. Proving them in one piece would be an all-or-nothing milestone whose progress is invisible until it lands, so the proof is specified as a ladder, each rung a theorem that stands on its own in `lean/Proofs/` and is accepted by the same gates as everything else (no `sorry`, no `native_decide`, `#print axioms` clean apart from the library axioms already disclosed):

* **R1 — fixed-width scalars.** null, boolean, ubyte/ushort/uint/ulong, byte/short/int/long including the small forms, float, double, decimal32/64/128, uuid, timestamp, char. No length fields are involved, so this rung reduces to byte-level lemmas: the big-endian writer and the reader's `takeBe` agree, two's-complement sign extension inverts, and the width is fixed by the line rather than by the payload.
* **R2 — variable-width families.** string, symbol, binary in both the 8-bit and 32-bit forms. Adds the length-prefix agreement and the narrow/wide choice, which is where `NarrowestEncoding` first bites.
* **R3 — compounds.** list8/list32/list0, map8/map32, array8/array32. Adds the size/count bookkeeping (the size field counting exactly what follows it) and the item loops, so the induction is over the value's structure at two levels: the compound and its items.
* **R4 — described values.** The descriptor-then-value pair, which composes R1–R3 and needs the reader's fuel generalised (`fuel ≥ octets remaining` rather than `fuel = the whole buffer`).
**R1 is where it stands, and the rung's shape is proved even though its claim is not.** Seven obligations are proved and named: `go_length` and `beOctets_length` (the writer's big-endian fold has the declared width), `mod_mul_base` (the base-256 decomposition `n % (256*b) = n % 256 + 256 * (n/256 % b)`, which was the obstruction the rung first reported and which falls to `Nat.div_add_mod`, the two truncation facts and `omega` — no induction), `go_foldr_value` with `bigEndianFieldValue` and `fieldValueRoundTrip` (the field-value law, stated in the reader's left-fold orientation because that is the direction the reader folds), and `Spec.ReadLaws.takeBe_eq_fold` in the specification itself: `takeBe` at a checked offset returns the fold of the buffer slice it consumed. `RoundTripFixedWidth` remains stated, and its three remaining obligations are named rather than hidden: the `drop`/`take` characterisation of that slice at the composition site, which the module documents as a library step nobody could name from the pinned core; the two's-complement pair for the signed widths; and the non-integer fixed-width cases, which need the same bridge once.

**R2 is landed to the same standard as R1: the shape proved, the claim stated.** Six obligations are proved and named. The narrow/wide rule is proved at both sides (`lengthWidthOf_narrow`, `lengthWidthOf_wide`) and is *stated as code* — `def lengthWidthOf payloadLength := if payloadLength ≤ 255 then 1 else 4` — so the rule is part of the rung rather than something a proof re-derives from whichever branch it unfolded. `two_pow_eight_mul` bridges the bound as the writer writes it to the bound as the field law reads it. Then the two halves of the length agreement: `lengthPrefixed_eq` (the writer emits the narrowest big-endian field carrying the payload's length, then the payload unchanged) and `lengthPrefixed_ok` (the emitted octets are the field plus the payload, so the field is the whole overhead), the second with **no hypothesis at all** because the size of the list does not depend on the check that admitted it — a condition the rung first carried and then removed, which is the same discipline as proving an identity unconditionally instead of assuming what it needs. `takeBe_beOctets` is the reader's half and the theorem that makes a length field *readable*: a cursor positioned after a header reads back exactly the value the header encodes, composing the consumed-slice identity with the field's value law.

`RoundTripVariableWidth` and its shape predicate remain stated, with three obligations named and none blocked: the writer's row choice agreeing with `lengthWidthOf` on the payload it actually has, the reader's length field feeding back into how many octets it takes, and the recovered payload being the writer's payload under `utf8Of` for the text families. One obstruction is recorded rather than papered over: the *success* form of the size half needs `Functor.map` on `Except.error` reduced, and this closure has no simp lemma for it — the same family as R1's Array/List bridge.

**R5 is the first rung that is not about agreement, and it reported the difference precisely.** R1 to R4 each proved an equality between a write and a read-back; R5 proves an inequality between two encodings of the same value, which is a statement about the choice rule. Three obligations landed: `widthChoice_le_of_fits` (any width the table offers that carries every quantity is at least the width the rule chooses — the whole order-theoretic content of "narrowest", which the agreement rungs never needed because agreements do not consult the choice), `widthChoice_narrow_iff` (the narrow width is chosen *exactly* when one octet carries everything, so the wide choice is **forced** rather than a preference the writer could reverse — which is what turns "narrowest" from a house style into a property), and `lengthPrefixed_canonical_size`.

What `NarrowestEncoding` still needs, and the ruling on it: **the contract keeps its global statement; the gap is reader-side lemmas, not a weaker claim.** The law compares the writer's canonical octets against an *arbitrary accepted* encoding, and the four rungs all reason about writer-produced octets. But the reader's dispatch is a function of the accepted buffer's first octet — the same table decision the writer consults — so a global proof can case on that octet and know which width the accepted encoding used, without any API change. What is missing is a set of lemmas about *what the reader consumed*, per family, derived from `takeBe`/`takeBytes` rather than from the writer's behaviour. Those are proof-internal and they compose into the global law, so the statement does not shrink and no hypothesis is added to it. The distinction the rung was asked to preserve is the one that matters: "this is per family" and "this family's reader lemma is missing" are the difference between a contract that shrank and a proof with one more rung to climb.

**The reader-consumption rung, and the induction that had to be generalised.** `foldl_be_bound` proves `bytes.foldl (fun acc byte => acc * 256 + byte.toNat) init < (init + 1) * 256 ^ bytes.length`, and the generalisation to an *arbitrary accumulator* turned out to be necessary rather than tidy: the loop carries one, so the nil case at `init` is the only base that closes the cons case — stating it at `init = 0` leaves the step unprovable. That is the same reason `takeBe`'s own value law needed the loop rather than its reversal, so the pattern is worth knowing twice. On top of it, `takeBe_lt`: a field's value is bounded by its own width, so a length read from a one-octet field is at most 255 and one from a four-octet field is below `2 ^ 32`. **The caveat, disclosed rather than buried:** `takeBe_lt` carries the cursor's own check as a hypothesis, because extracting it from `takeBe`'s success means inverting its refusal branch and that goes through `Functor.map` on `Except.ok`/`error` — the obstruction R2 and R3 recorded. Every composition site already has that check, so the hypothesis costs nothing at the point of use; it is a hypothesis all the same, and the module says so.

What `NarrowestEncoding` still needs is now short and family-by-family: for the variable-width families, an accepted encoding's field has width one or four and carries the same length, so `takeBe_lt` bounds that length by the width, `widthChoice_le_of_fits` gives `lengthWidthOf length ≤ w`, and the sizes add. The compounds and described values are the same argument with their own quantities and their own constructor octets. The law itself is untouched: no hypothesis, no weakening, the contract's statement.

The module also gained a section stating why these lemmas live there rather than beside the codec's other laws: they are about the *choice*, not about the codec's behaviour — which is the distinction the rung was asked to make visible, in the file a reader will open first.

**The traps, collected in one place because every rung has paid for at least one.** The closure has no Mathlib, so a Mathlib spelling of a lemma is a name to avoid rather than a thing to import (`Nat.pow_succ`, not `pow_succ`; `by_cases`, not `by_contra`), and `norm_num` is unavailable. `prefix` is a Lean keyword and cannot be a binder name. `Array.foldl_toList` is oriented list-ward, so the Array-to-List bridge is `← Array.foldl_toList`, and `Functor.map` on `Except.ok` does not reduce under `simp`, so the proof crosses it with an explicit `show`. And the one that has now recurred across R2, R3 and R4 and is therefore a property of this codebase rather than of any rung: **every arithmetic goal over the writer's output wants `simp [List.length_append, beOctets_length] <;> omega`** — associativity and commutativity of `+` are never in `simp`'s normal form for the goal shapes the writer's length expressions produce, so `simp` alone leaves `head.length + tail.length + 1 = 1 + head.length + tail.length` open. R5 added two more of the same shape, and the shared lesson is worth stating once: **the arithmetic is fine and the *spelling* of the goal is what stops the tactic.** A membership obligation under `List.all_eq_true.mpr` is a `decide`-form equality rather than a `Prop`, so the bound must be proved as a proposition and handed over with `simpa`; and `omega` does not evaluate powers, so `q < 2 ^ (8 * 1)` has to be `decide`d into `q < 256` first. Three more from the reader-consumption rung: `Except.ok.inj` gives a *pair* equality, so taking a component needs `congrArg Prod.fst` rather than `.1`; `Nat.pow_le_pow_right`'s first argument leaves a metavariable at elaboration unless its type is annotated; and `(0 + 1) * 256 ^ m` needs normalising by `simpa` before it can be compared with `256 ^ m`.

Two traps, both the no-Mathlib shape: `by_contra` is Mathlib-only (core's spelling is `by_cases h : p`), and `prefix` is a Lean *keyword*, so it cannot be a binder name — it produced a parse error that read exactly like a missing import. And one lesson about the shared boundary: with a broken shared file, a dependent's *own* errors stay hidden behind it, so a retry loop reported six failures that were all in the dependent itself and surfaced only when the shared file returned. A red build naming someone else's file is not evidence that the file is the problem.

**R4 is the framing around two values, and it handled the shared fact as instructed.** Three obligations are proved: the descriptor prefix is one octet of overhead, the framed octets are that octet plus the two encodings unchanged, and the writer's described case in closed form — given the descriptor's encoding and the value's, the described value's octets are the prefix followed by those two in that order. That is the framing half of the composition; the values inside are the lower rungs' business, and nothing in R4 re-derives their reasoning. Two things it stated rather than left implied: **a described value consults no choice rule**, because the framing carries no quantity and the descriptor and value bring their own encodings — otherwise a statement of the form "the writer takes the narrowest form" would read as if it applied here — and the fact that the frame layer's descriptor contract and a described value's descriptor round trip are *the same fact*, so R4 supplies it and the frame layer consumes it rather than two layers proving it twice.

The fuel gap is R3's, one level further in: `readValue` at a described value spends one octet on the prefix, then reads the descriptor and the value at the same remaining fuel, so an entry-fuel statement says nothing usable about either inner value. Recorded as the obligation it is. `RoundTripDescribed` and `DescribedScalar` remain stated, with three obligations named and none blocked: the prefix octet classifying as `.descriptor` (a fact of the generated range, not arithmetic), the cursor landing where the descriptor's encoding begins, and the composition itself with the two inner round trips as hypotheses at the fuel the descent supplies.

**R3's generalisation is right and the shape I proposed for it was wrong.** I suggested generalising R2's narrow/wide rule to a single quantity so that the compound case would be an instance; it is not, and the rung proved that rather than following the brief: a length field carries *one* quantity (the payload's length) while a compound's size field carries *two* (the size and the count, with a predicate over the pair), so a single-`Nat` generalisation would have had to say "everything except compounds", which is not a general rule at all. The general form is `widthChoice (quantities : List Nat)`, and both instances are then *proved* to be instances (`lengthWidthOf n = widthChoice [n]`, `sizeWidthOf size count = widthChoice [size, count]`), so there is no third spelling sitting beside the rule. Eight obligations landed and are inventoried: the choice rule stated once with both sides proved, the two instances, the writer's octets for a list/map and for an array in closed form under exactly the check the writer performs, and the size-field-is-the-whole-overhead pair, which is `lengthPrefixed_ok`'s statement at the compound's width plus the array's one constructor octet.

**R3 also reported a real gap rather than assuming it away, and it is the first one that is structural rather than arithmetic.** `decodeValue` enters at the octet count, but `readItems`/`readElements` descend into a compound's items with the *same* fuel the compound itself was read at — while the compound has already spent one octet on its size field. So a statement at entry fuel says nothing directly usable about the items inside, and R1 and R2 never had to care because their values do not recurse. The claim is stated at entry fuel and the descent's fuel accounting is recorded as the obligation it is.

`RoundTripCompound` is also the first claim whose proof must *use* the claim itself: a list of strings needs R2's, a list of integers R1's, and a list of lists this one — which is why it is a predicate on values rather than a lemma about a single encoding. Remaining obligations, none blocked: the writer's chosen row satisfying its own check (turning `≤ 255` into `compoundOctets`'s `< 2 ^ (8 * width)`, with R2's `two_pow_eight_mul` as the bridge), the reader's measured span equalling the declared size for a body the writer produced, and the induction with the fuel accounted for. Two traps recorded: an over-specified simp set is reported as unused once the hypotheses close the goal, and the array's size arithmetic needs `omega` after the length rewrites because associativity is not in simp's normal form for that goal shape.

**The composition's two facts are now proved, and the first attempt at one of them was the wrong obstacle.** `Spec.ReadLaws.extract_toList_eq_drop_take` proves `(buffer.extract pos (pos + width)).toList = (buffer.toList.drop pos).take width` **unconditionally**, because `List.extract` is an abbreviation for `(l.drop start).take (stop - start)` rather than a function, so the identity is `Array.toList_extract` and a definitional step. The rung had expected to need the cursor's check as a hypothesis and did not. `Spec.ReadLaws.takeBe_eq_fold` is upgraded to the composition's vocabulary — `takeBe` at a checked offset returns `beValue` of that slice with the cursor advanced by exactly `width`, the hypothesis being the cursor's own check — and the weaker octet form was *removed* rather than kept beside it, so a reader sees one statement and nobody quotes a superseded one.

Two orientation facts, each of which cost attempts and will cost the next rung the same: `Array.foldl_toList` is oriented list-ward (`List.foldl f init xs.toList = Array.foldl f init xs`), so the Array-to-List bridge is `← Array.foldl_toList`; and `Functor.map` on `Except.ok` does not reduce under `simp` in this closure, so the proof crosses the map with an explicit `show` at the reduced form.

Two notes from the rung worth keeping beyond it. The closure has **no Mathlib**, so a Mathlib spelling of a lemma is a name to avoid rather than a thing to import — `Nat.pow_succ`, not `pow_succ`. And the inventory now discloses `Classical.choice` on the theorems whose proofs lean on `omega`: acceptable because they are propositions about a codec and proofs are erased, and disclosed because an axiom that nobody prints is an axiom nobody reviewed.

* **R5 — narrowest form.** After R1–R4, for any buffer that decodes in full, the writer's encoding is no longer.

The rungs share one generalisation that has to be stated once: the reader's fuel is the whole buffer at the entry, so every rung is proved for `fuel ≥ read-so-far + remaining` rather than for the entry value, or the induction has no usable hypothesis. `sizeOf` may appear freely in these proofs — it is a measure, and erasure means it never has to compile, which is precisely why the *writer* could use it as a termination measure while the executable reader could not use it as a value.

### S2 — framing and performatives (Part 2 structural)

Scope: 8-byte frame header (`SIZE`/`DOFF`/`TYPE`/`CHANNEL`), extended header (`DOFF*4 - 8` bytes, ignored), frame types 0x00/0x01, performative-plus-payload body, all 40 descriptors, field order/mandatory/default rules, `max-frame-size` bounds, `channel-max` bounds.

Contracts: `lean/Contracts/FrameCodec.lean`, `lean/Contracts/PerformativeTables.lean`, `vectors/frames.ndjson`, `vectors/frames-negative.ndjson` (malformed header, oversize frame, out-of-range channel, missing mandatory field — each with its mandated error condition).

**What the tables carry, and what they do not — verified before writing the contract.** The generated tables hold the performative layer completely: 96 type declarations with 40 descriptors, of which **14 are the performatives** (nine whose `provides` contains `frame`, five `sasl-frame`), 125 field records each carrying `mandatory` and a `default`, 54 choices with `errorConditionsOf` (so `framing-error` resolves to `amqp:connection:framing-error` without hand-typing it), and the 39 encodings including `list8`/`list32`, which are the constructors a performative's list body uses. They hold **nothing for the frame header**: no frame-type octet, no protocol-header layout, no connection-level channel number, and the `max-frame-size` and `channel-max` defaults appear only as untyped strings in prose or in `defaultValue`. The header arithmetic — the eight-octet layout, what `DOFF` counts, where the type and channel bytes sit — **has no clause at all** under `amqp:transport/section:framing` (which holds four clauses: `SIZE` totals, the performative is a described type, empty frames, and the octet that must be zero before a size change). Its only normative statement is the layout pictures.

Three consequences, each a decision rather than an observation:

* **The frame constants are hand-transcribed, and their source is a picture.** The rule that no hand-written module may contain a literal descriptor code exists to stop a second source of truth for *table* data; where the artifact has no table, the hand transcription *is* the source, and it must cite what it transcribed. The frame-type octets, the protocol-header octets and channel 0 therefore live in the specification's frame module with the layout picture named in the documentation, and the pictures' ledger dispositions are updated to point at those declarations — which is what closes the loop between the picture review and the formalisation. If a later artifact revision ships frame-layer data, the transcription is replaced by generation and the dispositions move with it.
* **Defaults are typed by the field, not by the string.** `defaultValue` is the artifact's raw attribute text: numerals, booleans and choice names in one `Option String`. Reading a default as a value of the declared type is therefore a transcription rule of its own, with its own contract, and it is where a `channel-max` of 65535 and a `max-frame-size` of 4294967295 stop being strings.
* **Fourteen performatives, not forty.** The plan previously said "all 40 descriptors", conflating the types that carry descriptors with the performatives the frame layer dispatches on. Fourteen is the number the vectors must exercise, and the dispatch table that says which performative is legal in which state is a picture — S3's material, cited but not applied here.

**The contract surface S2 must fix before implementation.** The frames layer is where the corpus stops being values and starts being structure, so the statements are different in kind from S1's:

* **The header is arithmetic over the artifact's constants, not a layout somebody remembered.** `SIZE` counts the whole frame including the header; `DOFF` counts four-octet words from the start of the frame to the body, so the extended header is `DOFF*4 - 8` octets and MUST be ignored rather than rejected; `TYPE` selects the frame type and `CHANNEL` is 0 for connection-level frames. The generated constants (`MIN-MAX-FRAME-SIZE`, the frame-type octets, the descriptor codes) are what the statements refer to, so a constant changing moves the statement rather than leaving it true by accident.
* **Two rules that are easy to conflate and must not be**: the *frame* size limit is `max-frame-size` from the connection's `open`, while the *minimum* is the artifact's `MIN-MAX-FRAME-SIZE`; a frame outside the negotiated limit is a framing error, and an extended header of the wrong width is a different one. Both are rejects with distinct reason classes, following the rule S1 established — a refusal names its class.
* **Mandatory and default rules come from the generated field table, not from prose.** A performative missing a mandatory field, and one whose omitted optional field takes its default, are the two cases the corpus must separate: the first is a refusal, the second is a value. The field table carries `mandatory`/`default`, so the codec asks the table; a hand-written list of mandatory fields is a second source of truth and therefore a defect.
* **Composites: trailing nulls and field order.** A shorter list than the type declares means the missing trailing fields are null (S1 already dispositioned this), and field order is the declared order — not the order the fields appear on the wire. Both directions must be exercised, because an encoder that reorders fields still round-trips with its own reader and never with anything else.

**The vectors exist and the failure is observed.** Ten frame vectors are committed — `vectors/frames.ndjson` with four decodes and one encode, `vectors/frames-negative.ndjson` with five refusals — against `tests/contracts/frame-vector.schema.json`, every one citing clauses that exist in the ledger, with octets computed from the artifact's layout rather than typed by hand (a hand-typed `SIZE` of 21 against 20 octets was caught by recomputing all of them, which is the argument for computing). The pre-implementation failure is a harness that does not know the kind:

```
$ ./lean/.lake/build/bin/amqp-spec vectors/frames.ndjson
amqp-spec: line 1: unknown vector kind 'frame-decode'
exit 2
```

A loud failure rather than a silent pass, which is worth having checked: the same command through a pipe reported exit 0 until the status was measured directly, which is exactly the shape of a gate that protects nothing. The positives pin the smallest legal AMQP frame (a header and an `open` whose fields are all null by the trailing-null rule), a performative followed by opaque payload octets, a SASL frame whose channel octets carry no meaning, and a frame whose four octets of extended header must be *ignored* rather than validated. The negatives pin `SIZE` below what the body needs, `DOFF` below the header, `DOFF*4` beyond `SIZE`, a frame type this specification does not assign, and a seven-octet header — each with its reason class, so the arithmetic contradictions are `sizeMismatch`, the unknown type is `unsupported` rather than `unassigned` (the frame types come from prose, not a table, so nothing has "assigned" them to be unassigned), and a short frame is `truncated`.

**What is proved, and what is stated.** The frame layer's contract is `lean/Contracts/FrameCodec.lean`, and it separates the two kinds of claim rather than dressing one as the other. **Proved**: the header arithmetic — `bodyStart doff - headerOctets = (doff - minDoff) * doffWord` for any legal `DOFF`, and `bodyStart minDoff = headerOctets` — because that is arithmetic over the definitions and it is one of the two places a hand-written layout drifts; a codec that read `DOFF` as octets rather than words would satisfy every vector with no extended header and fail these. Both appear in the trust gate's axiom inventory with `[propext]` and `[propext, Quot.sound]`, so their trust is disclosed rather than assumed. **Stated and unproved**: `AcceptedFramesCarryPerformatives` (every accepted frame's body is a described value whose descriptor names a declared type carrying the frame type's role — the conformance gap the mutation control found, now a claim about every accepted frame rather than a branch somebody wrote), `ConsumedIsTheDeclaredSize`, and `FrameRoundTripOnEncodedFrames`, which is recorded as *depending on* the value layer's round trip because a frame body is a described value: a frame law proved without the value law would be a law about a smaller language than the codec speaks.

Acceptance, and one amendment on the record. The plan asked for the header arithmetic and the descriptor lookup to be *proved*, naming them as the two places a hand-written layout drifts. The arithmetic is proved. **The descriptor lookup is not: it is a stated proposition, gated by a mutation control that fails loudly the moment an accepted frame's body stops naming a performative.** Its proof belongs with S1.5's rungs — it is a case analysis over the decoder's branches, not arithmetic — and the amendment is recorded rather than left implicit, because a plan whose acceptance line is quietly satisfied by different work is worse than one that says which part is outstanding. What stands as S2's evidence is therefore: **the corpora (ten authored vectors and forty-three generated), differential agreement on every vector including each refusal's reason class, the descriptor mutation control, the performative-coverage check read from the artifacts, and the header arithmetic proved.** every descriptor exercised in both directions; every negative vector rejected with its named reason class; the descriptor-code mutation control fires; and the differential contract extended to frames, since the reference's frames layer is written independently of the specification's.

### S3 — connection lifecycle and the vertical slice

Scope: protocol header and version negotiation including mismatch and refusal rules, security-layer negotiation, `open`/`close`, `container-id`, `channel-max`, `max-frame-size`, `idle-time-out`, the connection state machine, connection errors, plus SASL ANONYMOUS, `begin`/`end`, `attach` with a settled receiver mode, `flow` with initial credit, `transfer` carrying one unfragmented `data` section, and `detach`. Narrow and closed completely, so the method is proved on this problem before breadth is added.

Contracts: `lean/Contracts/ConnectionLifecycle.lean`, `vectors/slice.ndjson`, `vectors/slice-negative.ndjson`, `vectors/recorded/slice-*.ndjson`.

Acceptance: the slice's clauses are dispositioned and formalized; every state in the connection and session machines has a reachable mandated exit; positive vectors admitted and negative vectors rejected with the named error; at least two recorded third-party vectors of the same exchange admitted (V3) with the mutation controls (V4) firing on the slice corpus.

### S4 — sessions, links, and flow control

Scope: `begin`/`end` with the window rules (`incoming-window`, `outgoing-window`, `next-outgoing-id`, `remote-incoming-window`, `remote-outgoing-window` and their recomputation), session errors and `unmapped` termination, `attach` with both roles and all settle modes, handle allocation, `flow` state (`link-credit`, `delivery-count`, `available`, `drain`, `echo`), transfer fragmentation and `more`, `disposition` and settlement, link resumption, link errors, forced detach.

Contracts: `lean/Contracts/FlowControl.lean`, `lean/Contracts/SessionWindow.lean`, `lean/Contracts/Settlement.lean`, `vectors/flow.ndjson`, `vectors/flow-negative.ndjson`.

Acceptance: window arithmetic formalized against the register's adopted reading with citations; credit conservation and handle-uniqueness invariants proved; drain and echo modelled; a vector family that fragments the same message at different permitted split points is admitted (the adequacy control).

### S5 — messaging (Part 3)

Scope: `header`, `delivery-annotations`, `message-annotations`, `properties`, `application-properties`, `data`, `amqp-sequence`, `amqp-value`, `footer`, `source`/`target` field sets, `message-format`, section framing across transfers, `received`/`accepted`/`rejected`/`released`/`modified` outcomes, `section-number`/`section-offset`.

Contracts: `lean/Contracts/MessageFormat.lean`, `vectors/messages.ndjson`, `vectors/messages-negative.ndjson`.

Acceptance: every section type round-trips; the outcome state machine is proved; the partial-transfer `received` path is modelled and vector-covered; a fragmented recorded message is admitted.

### S6 — transactions (Part 4)

Scope: `coordinator`, `declare`/`declared`, `discharge`, `txn-id`, transactional delivery state, transaction outcomes and errors, resumption rules, interaction with settlement.

Contracts: `lean/Contracts/Transaction.lean`, `vectors/txn.ndjson`, `vectors/txn-negative.ndjson`.

Acceptance: the declared/discharged state machine proved; mandatory transaction fields enforced; transactional dispositions covered; illegal ordering rejected with the named error.

### S7 — security layer (Part 5)

Scope: the SASL frame layer and its negotiation with the AMQP layer, `sasl-mechanisms`/`sasl-init`/`sasl-challenge`/`sasl-response`/`sasl-outcome`, `sasl-code` outcomes, ANONYMOUS/PLAIN/EXTERNAL, idle-timeout interaction, security errors, TLS as an opaque boundary with named assumptions.

Contracts: `lean/Contracts/Sasl.lean`, `vectors/sasl.ndjson`, `vectors/sasl-negative.ndjson`.

Acceptance: the SASL state machine proved; mechanism negotiation exercised; PLAIN and EXTERNAL vectors pass; the layer-transition rules (what may be sent when) enforced, with negative vectors for sending AMQP frames before SASL completion.

### H1 — handoff

Produce `HANDOFF.md`: the frozen interface, the ledger and coverage report, the vector corpus, the executable driver's invocation, and the requirements this specification places on implementation tooling (§23). No implementation work.

## 14. Repository layout

```
PLAN.md  AGENTS.md  HANDOFF.md
flake.nix  flake.lock
toolchain/{sources.toml,downstream-pins.toml}
spec/oasis/{amqp-core-*-v1.0-os.xml,NOTICE}
ledger/{clauses.json,coverage.json,dispositions/,ambiguities/}
lean/{Spec/,Generated/Oasis/,Contracts/,Proofs/,lakefile.lean,lean-toolchain,lake-manifest.json}
vectors/{*,recorded/}
tests/contracts/
scripts/
```

Directories appear with their first real file: no empty scaffolding, no build caches, no generated file without its generator.

## 15. Repository and toolchain decisions

- **The specification's toolchain is Lean only.** `lean-toolchain` pins `leanprover/lean4:v4.31.0` and mathlib `v4.31.0`, with nixpkgs `b3d51a0365f6695e7dd5cdf3e180604530ed33b4` for the prewarmed closure — the same Lean and mathlib revisions TemperMint pins, so the specification's modules compose with downstream proof work without version surgery. This repository requires no Rust, Charon, or Aeneas.
- **Downstream pins are recorded, not required.** `toolchain/downstream-pins.toml` records TemperMint's Charon `a5591f6b94c8575a6ba2ae71090614a722f2b011` (LLBC `0.1.263`), Aeneas `227f4e7ac70d687a6b1a4871b3304f5a1c6994bf`, and rustc `nightly-2026-09-17` as the identities the downstream consumer uses, so the handoff names exact revisions. A read-only contract checks that our Lean/mathlib revisions still match TemperMint's, so the two repositories cannot drift apart silently.
- **Integration contract.** The Lean project is a normal Lake package with path-based module names (`Spec.*`, `Contracts.*`, `Proofs.*`, `Generated.*` under namespace `SpecAMQP.*`), importable as a dependency by downstream tooling. No symlink or re-export layer is introduced.
- **No new dependencies** beyond Lean, mathlib, and the pinned closure without a recorded decision. The scripts use the Python standard library, XML parsing included.
- **Harness-contract runner**: `.feature` contracts are executed by `scripts/run-contracts.py` in this repository, adopting the runner idiom TemperMint established (one feature file names scenarios at the harness boundary; the runner is invoked per file). It is a new file here; TemperMint's copy is not modified.

## 16. Contracts, ownership, and test forms

Planner-owned (coder and reviewer MUST NOT modify; the conductor records SHA-1 for each before implementation, and a changed hash requires an explicit planner update and a regenerated manifest):

- `toolchain/sources.toml`, `toolchain/downstream-pins.toml`
- everything under `ledger/`, including dispositions and ambiguities
- `tests/contracts/**` including schemas and feature files
- `lean/Spec/**` (the frozen specification) and `lean/Contracts/**`
- `vectors/**` once a vector is committed as contract

Coder-owned: `flake.nix`, `flake.lock`, `scripts/**`, `lean/Proofs/**`, `lean/Generated/**` (regenerated only), `HANDOFF.md` under planner review.

Test forms:

- **Specification properties and invariants** are theorem/interface-conformance contracts, not Given/When/Then: they are mathematics over a defined domain.
- **Vector replay and mutation tiers** are BDD scenarios at the harness boundary, where the actor is the operator running the driver over a corpus and the observable outcome is the verdict report and exit status; the driver's refusal diagnostics are contract, not incidental log wording.
- **Ledger, schema, and provenance checks** are data/workflow contracts.
- **No test may call a network service, a model, a real clock, or randomness.** Third-party capture is manual, off-gate, and its *outputs* are committed; replay is offline. Any generated input uses a committed seed.
- **Failure-first**: every new contract is run and observed failing before its implementation, with the exact command and diagnostic recorded. A test never observed to fail protects nothing.

## 17. Verification gates and their negative controls

| Gate | Mechanism | Negative control |
| --- | --- | --- |
| Source identity | SHA-256 of vendored artifacts against `sources.toml` | mutate a byte in a copy; fetch/check must fail |
| Vendored immutability | notice present; files match hashes and are never edited | edit a copy; ledger regeneration must fail |
| Ledger completeness | every clause has a disposition; dispositions keyed by text hash | plant an undispositioned MUST; plant a `<b>MUST</b>`; plant a line-wrapped `MUST\nNOT`; each must be classified |
| Table fidelity | regeneration byte-identical; tables diffed against the OASIS text | mutate a descriptor code in a vendor copy; generation must change and the contract must fail |
| No hand-typed codes | scan of `lean/Spec`, `lean/Contracts`, `lean/Proofs` for literal descriptor codes and `amqp:` symbols | plant a literal `0x14` in a proof; the gate must fail |
| Executability | no `noncomputable`, no `partial`; `lake build Spec.Exec` succeeds | plant a `noncomputable def`; the gate must fail |
| Proof integrity | token-aware scan for `sorry`, `admit`, `native_decide`, `partial def`, `axiom`, `constant`, `opaque`, `unsafe`, `extern` and `implemented_by` across the handwritten modules, plus the accepted theorem's `#print axioms` inventory; no `sorryAx`, no `ofReduceBool` | plant a file containing each construct (behind comments and docstrings, to check the stripper) and require the scanner to name every one with file and line |
| Vector provenance | every vector cites clauses or records provenance; authoring rule (§5) enforced by review plus a scan for executor-generated vectors | add a vector with no `refs` and no provenance; the gate must fail |
| Picture review | every picture whose content contains formal grammar or a normative keyword carries a disposition keyed to its content digest | plant a `<picture>` containing `%x`; `check` must fail; record a wrong digest; the staleness check must fire |
| Discriminating power | V4 specification-mutation controls | a mutant no tier detects is reported as a suite defect |
| Specification adequacy | V3 recorded third-party vectors admitted | a recorded vector the specification rejects fails V3 |
| Determinism | replay produces byte-identical verdict reports across runs and machines | inject wall-clock or a random seed; the gate must fail |

## 18. Constraints and invariants

- The specification is executable, total where the protocol is total, and independent of every consumer.
- `MAY`-clauses become explicit nondeterminism and never a silent deterministic choice; `SHOULD` is never silently promoted to `MUST`.
- Semantics are handwritten; generated tables are data; no clause's meaning lives outside the ledger.
- Vectors are authored from clauses or recordings, never produced by the specification.
- No `sorry`, no reachable `sorryAx`, no unapproved axiom, no undisclosed `native_decide`.
- The specification makes **no claim about any implementation**. Its own assumptions — the peer, the ordered byte stream with arbitrary fragmentation, ticks, resource limits, TLS and mechanism cryptography — are named individually with ledger dispositions, and each of its claims states which of them it rests on.
- Third-party recordings are evidence about the OASIS text, not authority over it: a disagreement becomes a register entry with a decision, never a silent conformance weakening.

## 19. Risks and mitigations

| Risk | Concrete failure mode | Mitigation |
| --- | --- | --- |
| Over-narrowed specification | a conforming third-party behaviour is rejected | nondeterministic relation; V3 admission as a gate; over-narrowing treated as a defect class, not a test annoyance |
| Over-permissive specification | illegal behaviour is admitted, so the specification is useless downstream | negative vectors with named error conditions; V4 mutation controls; non-vacuity witnesses |
| Prose ambiguity | two readings diverge silently inside the specification | ambiguity register with evidence and a recorded decision per issue |
| Transcription error in tables | a wrong descriptor code or default propagates everywhere | generated tables, vendor-copy mutation control, no hand-typed codes |
| Ledger drift | clauses change meaning as text is edited and dispositions go stale | dispositions keyed by clause text hash; reconciliation contract against the §1 baseline |
| Formalisation scale | S4–S7 (flow control, messaging, transactions, SASL) are large and the ledger is unforgiving | milestone order closes the vertical slice first; coverage reported per anchor so partial progress is visible and measurable |
| Executability cost | the executable specification becomes too slow to run the corpus | the corpus is a specification test suite, not a benchmark: vector count in the hundreds, not millions; if a definition resists computation, that is a design smell in the definition, reported rather than worked around |
| Corpus acquisition | no access to a second implementation for V3 | capture is off-gate; clause-authored vectors land first, recorded vectors are added as they become available without blocking milestones |
| Correlated misreadings | a second transcription repeats the same error, so cross-checking two of our own developments reports agreement | third-party admission (§12 V3) is the independent evidence, because its independence is in authorship and experience rather than in language; a second prover is a cross-check, never an oracle (§12). Observed in practice at S1: the corpus generator and the implementation shared two encoding defects, and what caught them was the *reader's* independent arithmetic — a size window measured rather than trusted — not agreement between the two writers |
| Scope creep toward implementation | Rust creeps back in because it is the natural next step | §3 and §23: implementation work is scheduled in TemperMint; this repository stops at the handoff |

## 20. Acceptance commands

Run in milestone order. `shell` abbreviates the offline pinned-shell invocation; the first `develop` realises the pinned closure, everything afterwards is offline and writes only into temporary directories.

```sh
alias shell='nix --extra-experimental-features "nix-command flakes" develop --offline --no-update-lock-file .#spec --command'
nix --extra-experimental-features 'nix-command flakes' flake metadata --no-update-lock-file
nix --extra-experimental-features 'nix-command flakes' develop --no-update-lock-file .#spec --command true

# S0 — sources, ledger, tables, environment
shell bash tests/contracts/s0_sources_ledger.sh
shell bash tests/contracts/s0_tables_fidelity.sh
shell bash tests/contracts/s0_lean_environment.sh
git diff --exit-code -- lean/Generated    # regeneration determinism

# S1–S7 — specification claims and corpus, per milestone
shell bash -c 'cd lean && lake build Contracts.TypeSystem'
shell bash tests/contracts/s1_proof_integrity.sh  # no hidden trust in the specification
shell bash tests/contracts/s1_ref_vectors.sh      # reference implementation over the corpora
shell bash tests/contracts/s1_differential.sh     # specification vs reference, verdict by verdict
shell bash scripts/check-proof-assumptions.sh

# V2–V4 — corpus, adequacy, mutations
shell python3 scripts/run-contracts.py tests/contracts/v2_vector_corpus.feature
shell python3 scripts/run-contracts.py tests/contracts/v3_third_party_admission.feature
shell python3 scripts/run-contracts.py tests/contracts/v4_spec_mutations.feature
```

Each milestone's contract list adds its concrete `lake build Contracts.<Module>` and vector targets; the block above is the spine, not the full set.

## 21. Work order and first actions

Order: **S0 → S1 → S2 → S3 (vertical slice, closed completely) → V1–V4 on the slice → S4 → S5 → S6 → S7 → H1**, with recorded third-party vectors added to V3 as they become available. The slice is closed completely — clauses dispositioned, theorems, vectors, adequacy, mutations — before breadth is added, because the slice is what proves the method on this problem; widening afterwards is mechanical by comparison.

First three concrete actions:

1. Vendor the six OASIS artifacts with hashes and the notice; stand up the flake with Lean and mathlib pinned to TemperMint's revisions.
2. Implement `scripts/clause-ledger.py` and land the first disposition pass for Part 2 `#framing` and `#performatives`, with the planted-negative controls observed failing first.
3. Freeze the interface alphabet, the environment assumptions, and the vector schema — then write the Part 1 tables generator and its mutation control, so `Value.lean` starts on generated data rather than transcription.

## 22. Parallel work order, S3 to S7

The remaining milestones are decomposed into slices that can run at the same time without sharing a file, because the cost of a parallel batch is the interface that has to be fixed before it starts and the conflict that follows if it is not. Three rules hold for every batch:

* **interfaces are fixed by the planner before the batch starts** — a state type, a dispatch hook, a corpus schema. A slice that discovers it needs a different interface reports that; it does not negotiate one with its sibling, because two coders agreeing on an interface is not the same as the interface being right.
* **file ownership is disjoint, and the shared boundaries are named rather than discovered.** There are two, and the first version of this rule claimed there was one. The generator is shared between slices that add corpus families, so it is split before a wave needs two of them to touch it. **The harness is shared with everything** — every executable imports it, and so does every proof that touches a corpus — so a slice editing it can break four other slices' builds while being entirely within its brief. The rule for it is stricter because the blast radius is larger: a slice that must edit it advances it in compiling steps, and if two slices need it in the same wave the planner sequences them rather than handing it to one and hoping.

The mechanism turned out to be subtler than "keep it compiling between edits", and the slice that owned the file was in fact building after every edit. An edit *in progress* is an inconsistent file: the window between two compiling states is one a sibling's build can land in, and what the sibling then sees is an error naming a file it does not own. So the useful rules are weaker and more practical than "never break it": **write shared files whole rather than in a sequence of small edits where the tool allows it**, because a single write has no inconsistent window; **say so when you are mid-edit**, so the slices that depend on the file know a failure is expected rather than evidence of a defect; and **believe the owning slice over a build log** when the two disagree about whether the file compiles, because the log is a sample of a moving target. This was learned by paying: a mid-edit harness blocked two proof slices for the length of an edit, one of them retrying a build that could not succeed.
* **one integration owner** — the planner runs the acceptance commands, not the slices, since a slice that validates its own work is validating against its own reading of the contract.

**Wave 1 (running).** The reference's element-constructor gap (`lean/Ref/**`, `scripts/gen-value-vectors.py`); the value codec's round-trip rung R1 and the frame layer's three statements (both `lean/Proofs/**`, separate files so the two proof slices cannot collide); and S3's facts, read from the artifacts rather than remembered.

**Wave 2, after S3's facts land.** Three implementation slices and one enabling change:

* **S3-connection** — `lean/Spec/Connection.lean` and `lean/Ref/Connection.lean`: the protocol header and version negotiation, the SASL ANONYMOUS phase, `open`/`close`, the connection state machine and the connection error conditions; plus harness support for exchange vectors and the slice's generator family. The interfaces the planner fixes first: the state type takes the artifact's own state names, and the observable is the per-step verdict the exchange schema defines.
* **S3-session** — `lean/Spec/Session.lean` and `lean/Ref/Session.lean`: `begin`/`end`, `attach`/`detach`, `flow`, and `transfer` carrying one unfragmented `data` section. It depends on one thing from S3-connection and that thing is fixed before either starts: a frame whose channel is not zero is handed to the session layer, which decides whether the moment is legal.
* **S5-message** — `lean/Spec/Message.lean` and `lean/Ref/Message.lean`: the Part 3 section types and the outcome state machine. It depends on nothing in S3 at all — sections are values carried in a transfer's payload — which is why it can run beside the connection work rather than after it.
* **the generator split** — `scripts/gen/values.py`, `scripts/gen/frames.py`, `scripts/gen/slices.py`, with the existing script becoming the entry point that dispatches to them. This exists so that two slices can add families in the same wave without editing one file; until it lands, families are added by one slice at a time and the second waits.

**Wave 3.** S4's flow control (`lean/Spec/Session.lean`'s window arithmetic, credit conservation and settlement, with the fragmentation adequacy control) on top of S3-session; S6's transactions as its own performative family and state machine, which needs only the session dispatch; S7's full SASL mechanism negotiation and layer-transition rules on top of S3-connection's ANONYMOUS phase. R2–R5 of the proof ladder continue beside them.

**Wave 4.** The handoff, which is H1: what a downstream Rust implementation and its proof need from this repository, with the conformance interface and the frozen lexical surface named rather than described.

**One acceptance item is blocked on something no slice can produce.** S3's plan asks for at least two *recorded third-party* exchanges (V3) of the same slice, admitted, with the mutation controls (V4) firing. Recording requires an independent implementation to talk to, and this repository captures nothing over a network by design: the outputs of a capture are committed data, and there is no capture to commit. S3's acceptance therefore proceeds on V1, V2 and V4 — the authored and generated corpora and the mutation controls — and V3 stays outstanding with its requirement stated here rather than quietly dropped: a capture of the same exchange from an independent implementation, committed under `vectors/recorded/` with its provenance recorded the way the artifacts' identities are.

**Two gate defects found by the slice that hit them, both in contracts of mine.** The first: the differential's reason-class comparison keyed on a verdict status (`reject`) that the harness never emits, because it reports `pass`/`fail` for whether a *vector's* expectation was met. The comparison therefore skipped every vector and had never run — the pinned-reason check caught a wrong pin while two artefacts disagreeing about *why* they refused went unnoticed. It is now keyed on the corpus kind, with the class searched for in the detail because a verdict that met its expectation reads "rejected, as the vector expects: limit: …" rather than starting with the class. It is live and passing, and an honest gap remains: its *sister* check has been observed failing (a wrong pin, found by the slice), while this one has only been observed not-firing on inputs that are non-empty — a planted negative control would need a doctored artefact, and is owed. The second: the value corpus could not express an encode-direction refusal at all, because its shape check requires `bytes` on every vector, which is why the differential has to generate its limit control in a temporary directory instead of committing it. **Both are now closed**: the class comparison is keyed on the corpus kind and passes live over 68,111 vectors, and `bytes` is optional on an encode vector carrying `expectError`, which let the writer's refusal surface enter the corpus as **nine pinned vectors** — the declared form's capacity refusals (`limit`), covering a str8 element that cannot announce 300 octets, a list8 element that cannot announce 300 items, an array8 element that cannot announce 300 elements, a ubyte element constructor asked to carry a uint, `smalluint`/`smallint` out of range, `uint0` carrying a non-zero, `list0` carrying a non-empty, and a list8 element asked to carry a ubyte. The class is `limit` rather than `malformed` because `malformed` would say the octets are not a well-formed value when the value is legal and encodes fine in a wider form: what is unsatisfiable is the *declaration*, which is the same shape as the DOFF refusal and must not carry a different class.

The specification's six writer sites were changed by that slice under an explicit authorisation, on the condition that only the refusal *messages* move. Verified in the diff: every hunk wraps an existing message in the `refusal "limit"` helper, with no branch, condition or value touched.

**The workspace's git index is shared between agents**, and a slice learned it the expensive way: `git add <three paths> && git commit` committed nineteen files because a sibling's staged set was still in the index, and the commit message described three of them. The content was correct and every check had run on it; the *attribution* in the log was wrong. The lesson is in AGENTS.md: stage and commit in one command, never leave a staged set sitting, and amend the message rather than the record when it happens.

## 23. Handoff: what downstream implementation work needs from here

This repository stops at the specification. The remaining work — a Rust reference implementation, its extraction through Charon and Aeneas, proofs that it conforms, a fast implementation, performance evidence — belongs to TemperMint and is scheduled there. What it needs from here, and what `HANDOFF.md` records:

1. **The frozen interface alphabet and conformance relation** (§10) — so an implementation's proof is a `Conforms` instance rather than a re-framing exercise.
2. **The ledger and coverage report** — so implementation milestones can claim clause-level coverage in the same units as the specification, and gaps are visible on both sides.
3. **The vector corpus** — positive, negative, and recorded — as the differential and regression suite for any implementation, with the schema already frozen.
4. **The executable specification** (`lake exe amqp-spec`) — the oracle for spec-vs-implementation differential testing, and the reason vectors can be checked without writing a checker.
5. **The Lean/mathlib pin agreement** — so the specification's modules can be required directly by downstream proofs.
6. **Requirements that need tooling changes**, for scheduling in TemperMint rather than implementing here: multi-target extraction sharing one source-closure identity; a certificate binding the specification, model, corpus, and a `Conforms`-style theorem; a certificate kind whose claim is "refines a specification" rather than "computes a specified value"; per-module proof-cost accounting; and a corpus dimension in replay that regenerates and compares every claim-bearing input byte-identically.
