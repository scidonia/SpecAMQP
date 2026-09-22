# SpecAMQP — development programme: a correct, executable AMQP 1.0 specification

## Goal

Produce, in this repository, **a complete, correct, executable formal specification of AMQP 1.0 core** (OASIS Standard, Parts 0–5) in Lean 4, faithful to the OASIS Standard, with a clause-level ledger that makes *completeness* and *fidelity* measured properties rather than claims, and with a defined conformance interface so that downstream work — a Rust implementation, its extraction, and its proofs, which belong to TemperMint, not here — has a definite target.

This repository holds the specification and the evidence that it is correct. It contains **no implementation of the protocol**, in any language, and makes no claim about any implementation.

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

## 3. Non-goals

- **No implementation, in this repository.** No Rust, no reference implementation, no fast implementation, no extraction, no proofs about code, no performance measurement. Those require TemperMint's toolchain and are scheduled there (§22). The earlier draft of this programme specified them; they are removed, not forgotten.
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
- **Disposition values**: `formalized:<Lean declaration>`, `environment:<id>` (an assumption discharged by the environment model, e.g. "TCP delivers an ordered byte stream"), `out-of-scope:<reason>`, `informative` (explanatory, with justification), `test:<vector id>` (a statement whose only observable form is a vector expectation), `superseded:<decision id>` (decided by an entry in the ambiguity register, §8).
- **Coverage report** (`ledger/coverage.json`) aggregates per artifact and per anchor, and is regenerated per milestone; acceptance commands diff it against the previous milestone's report so a coverage regression is visible rather than merely regrettable.
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
  Performative.lean the 40 descriptors as one inductive, bound to generated tables
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

Proving an instance of `Conforms` for a concrete programme is downstream work (§22) and requires the extraction toolchain; defining it correctly is this repository's job, and it is the reason the interface is frozen before any implementation exists.

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

Acceptance: round trips proved on the canonical domain; every encoding row exercised by a vector; the ABNF/table agreement checked; ledger coverage complete for Part 1's normative clauses.

### S2 — framing and performatives (Part 2 structural)

Scope: 8-byte frame header (`SIZE`/`DOFF`/`TYPE`/`CHANNEL`), extended header (`DOFF*4 - 8` bytes, ignored), frame types 0x00/0x01, performative-plus-payload body, all 40 descriptors, field order/mandatory/default rules, `max-frame-size` bounds, `channel-max` bounds.

Contracts: `lean/Contracts/FrameCodec.lean`, `lean/Contracts/PerformativeTables.lean`, `vectors/frames.ndjson`, `vectors/frames-negative.ndjson` (malformed header, oversize frame, out-of-range channel, missing mandatory field — each with its mandated error condition).

Acceptance: frame and performative codecs proved against the generated tables; every descriptor exercised; every negative vector rejected with the named error; the descriptor-code mutation control fires.

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

Produce `HANDOFF.md`: the frozen interface, the ledger and coverage report, the vector corpus, the executable driver's invocation, and the requirements this specification places on implementation tooling (§22). No implementation work.

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
| Proof integrity | token-aware `sorry` scan; `#print axioms` inventory per public theorem; no reachable `sorryAx`; `native_decide` requires disclosure | plant a `sorry`; the gate must fail |
| Vector provenance | every vector cites clauses or records provenance; authoring rule (§5) enforced by review plus a scan for executor-generated vectors | add a vector with no `refs` and no provenance; the gate must fail |
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
| Scope creep toward implementation | Rust creeps back in because it is the natural next step | §3 and §22: implementation work is scheduled in TemperMint; this repository stops at the handoff |

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
shell bash -c 'cd lean && lake exe amqp-spec vectors/primitives.ndjson'
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

## 22. Handoff: what downstream implementation work needs from here

This repository stops at the specification. The remaining work — a Rust reference implementation, its extraction through Charon and Aeneas, proofs that it conforms, a fast implementation, performance evidence — belongs to TemperMint and is scheduled there. What it needs from here, and what `HANDOFF.md` records:

1. **The frozen interface alphabet and conformance relation** (§10) — so an implementation's proof is a `Conforms` instance rather than a re-framing exercise.
2. **The ledger and coverage report** — so implementation milestones can claim clause-level coverage in the same units as the specification, and gaps are visible on both sides.
3. **The vector corpus** — positive, negative, and recorded — as the differential and regression suite for any implementation, with the schema already frozen.
4. **The executable specification** (`lake exe amqp-spec`) — the oracle for spec-vs-implementation differential testing, and the reason vectors can be checked without writing a checker.
5. **The Lean/mathlib pin agreement** — so the specification's modules can be required directly by downstream proofs.
6. **Requirements that need tooling changes**, for scheduling in TemperMint rather than implementing here: multi-target extraction sharing one source-closure identity; a certificate binding the specification, model, corpus, and a `Conforms`-style theorem; a certificate kind whose claim is "refines a specification" rather than "computes a specified value"; per-module proof-cost accounting; and a corpus dimension in replay that regenerates and compares every claim-bearing input byte-identically.
