# SpecAMQP — development programme: AMQP 1.0 specification and reference implementation

## Goal

Produce, in this repository:

1. **A complete, executable formal specification of AMQP 1.0 core** (OASIS Standard, Parts 0–5) in Lean 4, faithful to the OASIS Standard, with a clause-level completeness ledger that makes "complete" a measured property rather than a claim.
2. **A reference implementation in Rust**, derived from that specification, of which the protocol-bearing core is extractable through the pinned Charon/Aeneas pair into a Lean model — so the specification and the implementation can be differentially tested against each other at machine speed.
3. **The conformance interface** that a later, separately written Rust programme must satisfy: a refinement relation over a fixed interface alphabet, with the specification's nondeterminism made explicit, so "prove this programme satisfies AMQP 1.0" becomes a statement of a definite shape rather than a research question to be framed later.

The endgame (downstream, not delivered here) is: a Rust programme, extracted to a Lean model, proved to refine this specification, with the specification itself checked against third-party implementations by differential trace testing.

The toolchain is TemperMint's (`../TemperMint`). **Nothing in TemperMint is modified by this programme.** Requirements the specification work places on TemperMint are recorded in §22 as a change request for a later, separately scheduled tooling-fit effort.

## 1. What "complete" means here

Completeness is measured against the pinned OASIS artifacts, never asserted. A milestone is complete when its coverage statement in §13 is discharged by the ledger, not when the feature "works".

The pinned OASIS Standard artifacts (`docs.oasis-open.org/amqp/core/v1.0/os/`, OASIS Standard 29 October 2012) are the normative source. A crude baseline scan of them, recorded here and **superseded by the S0 ledger**:

| Measure | types | transport | messaging | transactions | security | total |
| --- | --- | --- | --- | --- | --- | --- |
| bytes | 48 704 | 184 207 | 84 370 | 42 507 | 26 270 | 386 058 |
| MUST-class (incl. MUST NOT) | 4 | 117 | 60 | 29 | 12 | **222** |
| — of which MUST NOT | 0 | 23 | 19 | 4 | 0 | 46 |
| SHOULD | 0 | 36 | 20 | 6 | 8 | **70** |
| MAY | 1 | 69 | 12 | 0 | 4 | **85** |
| `<type class=…>` | 24 | 27 | 31 | 8 | 6 | 96 |
| `<field>` | 0 | 68 | 42 | 7 | 8 | 125 |
| `<choice>` | 0 | 32 | 9 | 8 | 5 | 54 |
| `<descriptor>` | 0 | 10 | 20 | 5 | 5 | 40 |

Additional scan results used as coverage units: 39 `<encoding>` specifications (all in Part 1, 39 distinct), 26 `mandatory="true"` fields, 28 declared `default=` values, and 31 distinct `<choice>` values declared in Part 2 — of which 25 are error conditions across the four providing types (`amqp-error` 13, `link-error` 5, `session-error` 4, `connection-error` 3) and 6 are enumerated type choices (`role`, both settle modes, terminus durability, distribution mode, lifetime policy).

The scan is crude: it counts keyword occurrences in prose without markup normalisation and therefore *includes* occurrences that are illustrative rather than normative (Part 1 has 4 MUST-class occurrences in a 48 KB document). The S0 ledger replaces these numbers, and the S0 contract pins the reconciliation between the ledger's count and this table with a recorded reason for every difference. These numbers exist to size the work, not to be quoted as the work.

**Definition.** The specification is complete when: (a) every normative statement in the pinned artifacts has a disposition in the ledger (§5); (b) every MUST-class statement is `formalized` or `environment`/`out-of-scope` with a recorded reason and a reviewer sign-off; (c) the declared type surface (96 types, 39 encodings, 26 mandatory fields, 28 defaults, 25 error conditions, 31 Part 2 choice values) is covered by generated tables rather than hand transcription (§6); (d) the executable specification admits the full committed trace corpus (§11); (e) the specification has no `sorry`, no `noncomputable` definition, and no unaudited axiom.

## 2. Deliverables

| # | Deliverable | Location |
| --- | --- | --- |
| D-a | Vendored, hash-pinned OASIS artifacts plus the OASIS copyright notice | `spec/oasis/`, `spec/oasis/NOTICE` |
| D-b | Clause ledger and dispositions | `ledger/clauses.json`, `ledger/dispositions/` |
| D-c | Generated definition tables (Lean and Rust) from the pinned XML | `lean/Generated/Oasis/`, `rust/amqp-codegen-generated/` |
| D-d | Executable Lean specification of Parts 0–5 | `lean/Spec/` |
| D-e | Acceptance declarations for every specification claim | `lean/Contracts/` |
| D-f | Reference implementation: allocation-free extractable core plus non-extracted environment layer | `rust/` |
| D-g | Extraction pipeline (Charon → LLBC → Aeneas → Lean) for the core | `scripts/extract-core.sh`, `lean/Generated/Core/` |
| D-h | Trace corpus and codec vectors with provenance | `fixtures/traces/`, `fixtures/vectors/` |
| D-i | Differential harness: spec-vs-model, spec-vs-ref, and third-party trace admission | `scripts/replay-traces.sh`, `rust/amqp-conformance/` |
| D-j | Conformance interface for downstream Rust programmes (§9) | `lean/Spec/Conformance.lean` |
| D-k | Tooling-fit change request for TemperMint (deferred, not implemented here) | `TOOLING-FIT.md` |

## 3. Non-goals

- **Protocol extensions.** AMQP management (`amqp-man`), filter expressions (`filtex`), claims-based security (`amqp-cbs`), addressing, JMS mapping, HTTP-over-AMQP, event streams, and connection-info are out of scope. The OASIS TC repository `oasis-tcs/amqp-specs` holds these as working drafts (`.docx`); they are not part of the OASIS Standard for core AMQP 1.0. Core must nonetheless *handle* them correctly as unknown described types and pass-through annotations, and §9 defines the extension point.
- **Broker and queue semantics.** AMQP core defines links and termini; it does not define what a destination does with a message. `source`/`target` are formalized as the protocol-visible field sets and obligations, not as a routing model.
- **TLS and the TCP/IP stack.** Security-layer negotiation is specified; TLS itself is an opaque, disclosed external model. The byte stream is an environment oracle: arbitrary fragmentation, no reordering.
- **Mechanism-specific SASL cryptography.** SASL *framing* is specified; ANONYMOUS/PLAIN/EXTERNAL content is simple enough to formalize; GSSAPI and similar are opaque external models whose content the protocol layer never inspects.
- **A production client or broker.** The reference implementation is a conformance oracle and differential-test subject. Reliability, throughput, backpressure tuning, and deployment concerns are not goals.
- **Verified I/O.** The async/socket/timer layer is explicitly outside every proof. No claim of verified native execution; the trust boundary is disclosed exactly as in TemperMint §3.
- **TemperMint changes.** No modification, fork, or vendoring of TemperMint in the spec milestones (§22 records the change request instead).
- Calendar promises. Progress is reported in coverage units (clauses, types, encodings, corpus size, proof obligations closed).

## 4. Normative source and pinning

Vendor the six Part 0–5 XML artifacts byte-identically at `spec/oasis/`, with SHA-256 recorded in `toolchain/sources.toml` and the OASIS copyright/citation notice retained alongside (the OASIS notice permits redistribution of the whole with the notice intact; the files MUST NOT be modified). `scripts/fetch-oasis.sh` populates `spec/oasis/` and refuses to proceed unless every hash matches `sources.toml`; the vendored copies are committed, so all later work is offline.

Two structural facts about these artifacts, verified against the pinned bytes, drive the whole design:

1. **The definition language is present and machine-readable**: `type` (with `class` ∈ {primitive, restricted, composite}), `field` (with `type`, `mandatory`, `default`, `label`), `choice` (with `value`), `descriptor` (with `code` as `domain:descriptor`, e.g. `amqp:open:list` = `0x00000000:0x00000010`), `encoding` (with `code`, `category`, `width`). Sections carry stable `name` attributes (`framing`, `sessions`, `links`, `performatives`, `txn-declare`, `primitive-type-definitions`, …) which are the anchor half of every clause identifier.
2. **Behaviour is prose.** The artifacts contain no state-machine element type: only prose `<doc>` text with normative keywords, plus `<picture>` diagrams. Framing, connection/session/link lifecycles, window arithmetic, settlement, and transaction rules exist only as normative English.

Consequence, and the core methodological decision of this programme: the specification is built from **generated tables for the declared surface** (codes, field order, mandatory, defaults, choices, encodings) and **handwritten semantics for behaviour**, and the two are bound by contracts that make a hand-typed descriptor code impossible to get wrong silently.

## 5. The clause ledger

`scripts/clause-ledger.py` reads only the pinned artifacts and emits `ledger/clauses.json`: one record per normative statement, deterministically ordered.

- **Identifier**: `<artifact>#<anchor>.<n>`, e.g. `amqp-core-transport-v1.0-os.xml#sessions.42`, where `<anchor>` is the `name` attribute of the nearest enclosing element carrying one (`section`, `type`, `field`, `choice`, `doc`) and `<n>` is the 1-based index of the statement within that anchor in document order.
- **Fields**: artifact, anchor, index, kind (`MUST` | `MUST NOT` | `SHOULD` | `SHOULD NOT` | `MAY` | `REQUIRED` | `OPTIONAL`), normalised text, text SHA-256, and the enclosing type/field/choice path where applicable.
- **Normalisation** must handle the real markup: inline emphasis wrapping the keyword (`<b>MUST</b>`), keywords split across source lines (`MUST\nNOT`), entity-encoded text, and must not treat `<picture>` diagram text, `revhistory`, or `acknowledgements` content as normative. This is a token-aware scan, not a regular-expression grep, and it is verified by planted negative controls (§17).
- **Dispositions** (`ledger/dispositions/*.json`, planner-authored) key on `(id, text_sha256)`. A source change that alters a clause's text makes its disposition stale and fails the contract — the mechanism that prevents silent drift between the OASIS source and the formalisation.
- **Disposition values**: `formalized:<Lean declaration>`, `environment:<id>` (an assumption discharged by the environment model, e.g. "TCP delivers an ordered byte stream"), `out-of-scope:<reason>`, `informative` (the statement is explanatory, with justification), `test:<fixture id>` (a statement whose only observable form is a trace expectation), `superseded:<decision id>` (a clause decided to have a specific reading recorded in the ambiguity register, §7).
- **Coverage report** `ledger/coverage.json` aggregates per-artifact and per-anchor counts, and is regenerated per milestone; the milestone acceptance commands diff it against the previous milestone's report so coverage regressions are visible.

## 6. Generated definition tables

Two generators consume the same pinned bytes, so table agreement between specification and implementation is by construction rather than by discipline:

- `scripts/gen-oasis-lean.py` → `lean/Generated/Oasis/*.lean`: descriptor codes as `Nat` literals, field order and codes, `Option`-typed nullable fields, declared defaults, mandatory flags, choice sets, the encoding table (39 entries with code/category/width), and the error-condition symbol sets. Types generated: 96 type declarations' metadata, 125 fields, 54 choices, 40 descriptors, 25 error conditions.
- `scripts/gen-oasis-rust.py` → `rust/amqp-codegen-generated/`: the same data in Rust form.

Contracts on both: regeneration is byte-identical (§17); no hand-written file in `lean/Spec`, `lean/Proofs`, `lean/Contracts`, or `rust/amqp-{wire,engine}` may contain a raw descriptor code or error symbol — the contract scans for hex-escape-shaped and `amqp:`-shaped literals and requires them to come from generated modules. The mutation control: edit a copy of one vendor file's `code="0x00000000:0x00000014"` to the wrong value, run the generator, and require the generated output to change and the affected contract to fail.

Neither generator is allowed to be a "specification of record": the Lean specification's *semantics* are handwritten (§8), and the generated tables are reviewed data.

## 7. Ambiguity register

AMQP 1.0's prose is not uniformly exact; several areas admit two readings, and real implementations disagree in practice. `ledger/ambiguities/*.json` records, per issue: the clause ids involved, the candidate readings, the reading adopted, the evidence (clause citation; third-party trace; primary implementations' documented behaviour), and the consequences for the conformance relation.

Known entries to open at S0, from the clauses inspected while writing this programme:

- session window recomputation (`next-incoming-id` / `incoming-window` derivation of `remote-incoming-window`, Part 2 `#sessions`) and which window updates are "MAY (depending on policy)";
- `open.idle-time-out` — the local threshold rule, the halving recommendation, and which peer closes;
- `attach.initial-delivery-count` versus the first `flow.delivery-count`, and what a receiver must infer;
- `flow.available` for senders that cannot determine availability;
- link resumption: which fields change identity versus state;
- message fragmentation: the `more` flag, session-window interaction, and abort semantics;
- `received` (`section-number` / `section-offset`) obligations for partially transferred messages.

Adopting a reading is a *decision with evidence*, and where a mainstream implementation disagrees with our reading, the disagreement is a recorded finding — not a reason to weaken the specification.

## 8. Specification architecture (Lean)

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
  Conformance.lean  the interface alphabet, the refinement relation (§9)
  Exec.lean         the executable driver: trace in, trace out
```

Requirements on the specification layer:

- **Executable.** Every definition in `Spec/` is computable; `Exec.lean` runs a trace and emits the resulting frames. `noncomputable` is rejected by contract. `lake exe amqp-spec` is the differential oracle.
- **Independent of generated code.** `Spec/` names no generated declaration. Generated tables are imported by `Performative.lean`'s binding layer only, under a contract that the binding is a *table*, not a semantics.
- **Independent of the implementation.** No `Spec/` declaration is derived from `rust/**`, and the extractor's output namespace (`Generated.Core.*`) is never referenced from `Spec/`.
- **Nondeterminism is explicit** (§9). Where the spec says MAY, the choice is a first-class input, not an implementation detail of our Lean definitions.
- Value-level fidelity: the type system is formalized with specificity preservation (canonical encodings), so `decode`/`encode` round trips are theorems with stated equality classes rather than loose "some bytes came back" claims.

## 9. The conformance interface (the deliverable the later proof needs)

Fixed at S0/S1 and frozen thereafter. An endpoint is a state machine over an interface alphabet:

```lean
inductive Input  where | frame : Bytes → Input | api : ApiCall → Input | tick : Tick → Input
inductive Output where | frame : Bytes → Output | api : ApiResponse → Output

structure Endpoint (σ : Type) where
  init : σ
  step : σ → Input → Option (σ × List Output)          -- implementation: partial function
  choose : σ → Input → Set (σ × List Output)           -- specification: relation
```

and refinement is simulation with **identical output sequences**:

```lean
def Refines (spec : Endpoint σs) (impl : Endpoint σi) : Prop :=
  ∃ R : σs → σi → Prop,
    (∀ si, spec.init ~ si → …) ∧
    ∀ ⦃ss si i o ss'⦄, R ss si → impl.step si i = some (si', o) →
      ∃ ss', (ss', o) ∈ spec.choose ss i ∧ R ss' si'
```

Design rules, decided here so the specification is not retrofitted later:

1. **Output agreement, not trace inclusion.** Because an endpoint's observable output *is* the wire, the implementation must emit exactly an output sequence the specification admits. This is stronger than trace inclusion and is what makes "satisfies the protocol" mean something for a programme we did not write.
2. **Specification nondeterminism is a set.** `MAY`-clauses and policy-dependent window updates produce sets. The *adequacy* obligation runs the other way from the safety obligation: the relation must be wide enough to admit every behaviour a conforming third-party implementation exhibits. That obligation is discharged by D3 (§12), and its failure mode — a third-party trace rejected by the specification — is a first-class bug class ("over-narrow specification"), not a test annoyance.
3. **MUST versus SHOULD.** MUST-class clauses become obligations inside `choose`. SHOULD-class clauses become either fairness-qualified progress obligations or recorded freedoms, each with a ledger disposition; a SHOULD is never silently promoted to a MUST.
4. **Progress.** Where the specification requires the endpoint to act (send a mandated error, respond to `drain`, complete a close handshake), the obligation is expressed as a deadlock-freedom property under a stated fairness assumption, enumerated from the ledger.
5. **Bounded resources are explicit.** `Input` includes resource events; refusal on capacity exhaustion is a specified behaviour with a mandated error code (§10), so an implementation that runs out of room is *incorrect in a checked way* rather than silently truncating.
6. **The extracted model is the implementation-side `step`.** Downstream proofs use the same `Endpoint` shape, so a user programme's proof is a `Refines` instance, and the specification work done here is reusable without re-framing.

## 10. Reference implementation architecture (Rust)

```
rust/
  amqp-codegen-generated/   generated tables (§6); not hand-edited
  amqp-wire/                type system codec, allocation-free, extractable
  amqp-engine/              endpoint state machines, allocation-free, extractable
  amqp-ref/                 environment layer: sockets, timers, buffering, SASL/TLS glue
  amqp-conformance/         trace replay/emit CLI (fixtures in, diff out)
  tests/                    caller-boundary behaviour contracts
```

- **Extractable core** (`amqp-wire`, `amqp-engine`): `#![forbid(unsafe_code)]`, no allocation, no I/O, no globals, no threads, no build scripts, no procedural macros, no feature-dependent bodies. Decoding is cursor-based over `&[u8]`; encoding writes into caller-owned `&mut [u8]` and returns the length; endpoint state lives in caller-owned tables (slab-style: capacity plus an explicit `len`) with `NoCapacity` as a typed error mapped to `amqp:resource-limit-exceeded`; frame-size violations map to `amqp:frame-size-too-small` / `amqp:connection:framing-error` as the clauses require. The endpoint surface is a step function, e.g. `step_endpoint(state: &mut State, input: Input<'_>, out: &mut [u8]) -> Result<usize, Error>`; the exact shape is fixed by the S0 spike (§13) after being checked against the pinned pair.
- **Environment layer** (`amqp-ref`): the async runtime, socket, timer, buffer pool, and the SASL/TLS mechanics that the protocol layer treats as opaque. Disclosed trust boundary. Its only obligations are the adapter obligations the specification names (bounded frame reads, ordered byte delivery, logical-time ticks as explicit inputs).
- **Capacities are negotiable, not fixed.** The core takes `channel-max`, handle counts, and window sizes from the caller; the endpoint's own advertised limits are therefore whatever the caller supplies, and the specification's rules about those limits are exercised directly.
- **Two independent transcriptions.** The Rust core is written from the specification text, not generated from Lean. Generating it would make the differential test vacuous. The shared artifacts between the two sides are only the *generated template tables* (§6), which come from the pinned XML and are themselves contract-checked.
- **Extraction** mirrors TemperMint's proven pipeline: `scripts/extract-core.sh` runs Charon (`--preset=aeneas`) inside the core crate and Aeneas (`-backend lean -loops-to-rec`) into `lean/Generated/Core/`, never hand-edited, regenerated before every proof build, with a second extraction required to be byte-identical.
- **Toolchain capability envelope** (verified against the pinned revisions rather than assumed, because these bounds are architectural, not cosmetic):
  - Aeneas "currently targets a safe, sequential Rust code" (`aeneasverif.github.io/projects`). The core is therefore synchronous by construction.
  - At the pinned Charon commit the unsupported-feature tracker lists **`async`** (`AeneasVerif/charon#609`, open), `CoerceUnsized` (#855), contract annotations (#646), default field values, and unsafe fields. **`async` cannot be extracted at all**, so the async layer is outside every proof by tooling limit, not merely by choice — which is why §10's split is the only shape available, and why the core must expose a synchronous step function.
  - Charon's `docs/limitations.md` at the pinned revision lists one known unsoundness (#583: indexing behind raw pointers). The issue is closed as completed on 2025-12-08, before the 2026-09-17 pin, and its subject is outside our fragment (no raw pointers in the core) either way; the file is stale rather than indicative. It also documents no trait solving on translated output and little syntactic information, both of which the generated-table design already avoids depending on.
  - Rust integer semantics arrive as Aeneas scalar types with checked arithmetic in the `Result` monad (`I64`, `Usize`, …), so overflow, out-of-bounds access, and panics become proof obligations rather than silent behaviours — exactly the obligations §13's L2/L3 levels discharge.

## 11. The trace, and why it is the shared currency

Everything is diffed through one format: NDJSON, schema-validated (`tests/contracts/trace.schema.json`), with **logical time only** — timestamps are ordering tags, never wall-clock, so replay is deterministic on any machine.

```json
{"trace":"spine-001","provenance":{"role":"client","peer":"apache-artemis 2.33.0",
  "method":"recorded","date":"2026-10-02","recorder":"ticket-142","transcript_sha256":"…"},
 "steps":[{"dir":"in","bytes":"414d515000010000"},
          {"dir":"out","expect":"bytes","bytes":"…"},
          {"dir":"out","expect":"action","action":{"kind":"credit","link":0,"value":100}},
          {"env":{"tick_ms":500}}]}
```

- `dir:"in"` is peer→endpoint, `dir:"out"` is endpoint→peer, and `expect` distinguishes byte-identical output from a typed action where bytes are not yet fixed by the specification (for example fragmentation split points the spec permits).
- Environment events (ticks, EOF, partial reads) are explicit steps. Nothing is read from a clock.
- Provenance is mandatory for non-synthetic traces, including the peer implementation and version, and the hash of the session transcript kept out-of-tree.

## 12. Differential testing (four tiers)

| Tier | Subjects | Mechanism | Failure it detects |
| --- | --- | --- | --- |
| D1 | specification vs extracted model | in-Lean: codec equality over the full byte domain where provable, plus deterministic generators over a committed seed; engine comparison over generated event sequences | transcription divergence between the two formalizations of the same prose |
| D2 | specification vs reference | trace replay through `lake exe amqp-spec` and through the Rust reference, byte-compared | implementation defects, and spec-versus-ref disagreement on the corpus |
| D3 | specification and reference vs third-party implementations | traces recorded against Qpid Proton, Apache Qpid J/Artemis, RabbitMQ 1.0, Dispatch router (two or more required; provenance recorded) replayed offline; both spec and ref must accept/reproduce | **over-narrow specification** (spec rejects real behaviour) and interop divergence |
| D4 | mutant controls | planted defects — dropped MUST check, off-by-one window arithmetic, wrong descriptor code, non-canonical encoding accepted, out-of-range channel accepted, credit over-granted | a differential suite that proves nothing because it cannot detect a violation |

D4 is what makes D1–D3 load-bearing and mirrors TemperMint's mutation-control discipline. Each formalized MUST-class clause names the fixture family that exercises it; the coverage report lists clauses exercised by no fixture, and that list is reviewed per milestone rather than assumed empty.

Live interop (recording) is a manual, credentialed activity performed off-gate; the committed corpus carries provenance and replays deterministically offline. No test in this repository contacts a network service, a model, a clock, or a random source.

## 13. Milestones

Each milestone: scope, planner contracts, the failure expected before implementation, and observable acceptance. Coverage is stated in ledger terms and superseded by `ledger/coverage.json`.

### S0 — basis, spike, and freezing the interfaces

Work: vendor the artifacts and notice; write `AGENTS.md` recording repository instructions, contract ownership, and the test-form decisions of §16 (the workflow reads it before choosing an approach); write `toolchain/pins.toml` and `toolchain/sources.toml`; implement the ledger generator and the first disposition pass; generate tables for the declared surface; **run the extraction spike** that validates the Rust shape the core needs (mutable state records, enums, nested records, `&mut [u8]` out-buffers, `Result`, explicit loops) against the pinned pair; freeze the interface alphabet, the trace schema, and the error-code mapping.

Contracts: `tests/contracts/a0_sources_ledger.sh` (hashes, ledger generation, reconciliation of the §1 baseline, planted-negative controls), `tests/contracts/trace.schema.json`, `tests/contracts/a0_extraction_spike.sh`.

Expected failure: `scripts/fetch-oasis.sh` fails on a missing pin; `clause-ledger.py` fails on an unresolved import; the spike fails on a missing crate.

Acceptance: ledger generated offline from vendored bytes; every §1 count reconciled with a recorded reason; regeneration byte-identical; spike extracts and builds; interface freeze recorded in `lean/Spec/Conformance.lean` with contracts referencing it.

### S1 — type system (Part 1)

Scope: all 26 primitive types, 39 encodings, described types, composite encodings, arrays; specificity preservation; decode error taxonomy (`amqp:decode-error`); the Part 1 ABNF cross-checked against the encoding table.

Contracts: `lean/Contracts/TypeSystem.lean` (round-trip and canonicality theorems at exact types), `fixtures/vectors/primitives.json` (vectors from the Part 1 examples plus foreign-library outputs), `rust/tests/wire_contract.rs`.

Expected failure: unresolved import `Spec.Value`; missing vector file.

Acceptance: decode/encode round trips proved on the canonical domain; every encoding row exercised; vectors pass in Lean and Rust; D1 codec equality for the implemented domain.

### S2 — framing and performatives (Part 2 structural)

Scope: 8-byte frame header (`SIZE`/`DOFF`/`TYPE`/`CHANNEL`), extended header (`DOFF*4 - 8` bytes, ignored), frame types 0x00/0x01, performative-plus-payload body, all 40 descriptors, field order/mandatory/default validation, `max-frame-size` enforcement, `channel-max` bounds.

Contracts: `lean/Contracts/FrameCodec.lean`, `rust/tests/frame_contract.rs`, `tests/contracts/a2_descriptor_codes.sh` (no hand-typed codes; mutation control on a vendor copy).

Acceptance: frame and performative codecs proven against generated tables; every descriptor exercised; the mutation control fires; malformed-header and oversize cases produce the mandated error codes.

### S3 — connection lifecycle and the vertical slice

Scope: protocol header and version negotiation (including the mismatch/refusal rules and security-layer negotiation), `open`/`close`, container-id, `channel-max`, `max-frame-size`, `idle-time-out`, the connection state machine, connection errors, SASL ANONYMOUS sufficient for a real handshake, `begin`/`end`, `attach` with receiver-settle-mode settled, `flow` with initial credit, `transfer` carrying a single unfragmented `data` section, `detach`. **This slice is deliberately narrow and complete**: with it, the reference implementation talks to a real broker end to end.

Contracts: `lean/Contracts/ConnectionLifecycle.lean`, `lean/Contracts/Slice1Conformance.lean`, `rust/tests/slice1_contract.rs`, `fixtures/traces/slice1-*.ndjson`, `tests/contracts/a3_vertical_slice.sh`.

Acceptance: spec and reference reproduce the slice corpus byte-identically; a recorded third-party trace of the same exchange is admitted by the specification and reproduced by the reference; every clause dispositioned in the S3 scope is formalized; extraction of the slice core succeeds and the L2 proof (codec) plus the first L3 fragment (connection step refinement) is closed.

### S4 — sessions, links, and flow control

Scope: `begin`/`end` with window rules (`incoming-window`, `outgoing-window`, `next-outgoing-id`, `remote-incoming-window`, `remote-outgoing-window` and their recomputation), session errors and `unmapped` termination, `attach` with both roles and all settle modes, handle allocation, `flow` state (`link-credit`, `delivery-count`, `available`, `drain`, `echo`), credit conservation, transfer fragmentation and `more`, `disposition` and settlement, link resumption, link errors, forced detach.

Contracts: `lean/Contracts/FlowControl.lean`, `lean/Contracts/SessionWindow.lean`, `lean/Contracts/Settlement.lean`, `rust/tests/flow_contract.rs`, `fixtures/traces/flow-*.ndjson`.

Acceptance: window arithmetic proved against the adopted reading with the ambiguity register cited; credit conservation invariant proved; drain/echo exercised; fragmentation split points admitted by the relation (adequacy control: a differently-splitting conforming implementation is still accepted).

### S5 — messaging (Part 3)

Scope: `header`, `delivery-annotations`, `message-annotations`, `properties`, `application-properties`, `data`, `amqp-sequence`, `amqp-value`, `footer`, `source`/`target` field sets, `message-format`, section framing across transfers, `received`/`accepted`/`rejected`/`released`/`modified` outcomes, `section-number`/`section-offset`.

Contracts: `lean/Contracts/MessageFormat.lean`, `fixtures/vectors/messages.json`, `rust/tests/message_contract.rs`.

Acceptance: every section type round-trips; outcome state machine proved; partial-transfer `received` path exercised; a fragmented message assembled from a recorded third-party trace is admitted.

### S6 — transactions (Part 4)

Scope: `coordinator`, `declare`/`declared`, `discharge`, `txn-id`, transactional delivery state, transaction outcomes and errors, resumption rules, interaction with settlement.

Contracts: `lean/Contracts/Transaction.lean`, `fixtures/traces/txn-*.ndjson`.

Acceptance: declared/discharged state machine proved; mandatory transaction fields enforced; transactional dispositions admitted in traces.

### S7 — security layer (Part 5)

Scope: SASL frame layer and its negotiation with the AMQP layer, `sasl-mechanisms`/`sasl-init`/`sasl-challenge`/`sasl-response`/`sasl-outcome`, `sasl-code` outcomes, ANONYMOUS/PLAIN/EXTERNAL, idle-timeout interaction, security errors, the TLS handoff as an opaque boundary with its adapter obligations.

Contracts: `lean/Contracts/Sasl.lean`, `fixtures/traces/sasl-*.ndjson`.

Acceptance: SASL state machine proved; mechanism negotiation exercised; PLAIN/EXTERNAL vectors pass; the layer-transition rules (what may be sent when) are enforced, with negative controls for sending AMQP frames before SASL completion.

### R1 — reference implementation: full driver and interop

Work: complete `amqp-ref` (event loop, buffering, timers as logical ticks, SASL/TLS adapters), the conformance CLI, and the recording procedure; record against two or more independent peers.

Contracts: `rust/tests/ref_contract.rs`, `tests/contracts/r1_recording.sh` (provenance and schema validation of recorded corpora).

Acceptance: end-to-end exchange with two independent implementations recorded, replay deterministic, corpus committed with provenance.

### R2 — extraction and the proof ladder

The ladder, per module, with proofs closing in order:

| Level | Statement | Feasibility |
| --- | --- | --- |
| L1 | specification-level theorems: codec round trip, canonicality, state-machine invariants | in scope now |
| L2 | extracted model equals specification, function-level, for the codecs | high |
| L3 | extracted endpoint `step` refines the specification relation (simulation, identical outputs) | per feature, in the order S3 → S4 → S5 → S6 → S7 |
| L4 | a downstream Rust programme refines the specification | downstream; interface fixed here |

Contracts: `lean/Contracts/CoreExtraction.lean` (generated-model binding), `lean/Contracts/CoreRefinement.lean` per feature, plus a `sorry`/axiom audit adapted from TemperMint's `scripts/check-proof-assumptions.sh` (token-aware scan with a planted-`sorry` negative control; `#print axioms` inventory of each public theorem; no reachable `sorryAx` or unapproved custom axiom).

Acceptance: L2 closed for the wire core; L3 closed for the vertical slice and each subsequent feature in milestone order; extraction regenerated immediately before the final proof build with no diff; audit clean.

### D1–D4 — differential tiers

Contracts: `tests/contracts/d1_model_spec.feature`, `tests/contracts/d2_trace_replay.feature`, `tests/contracts/d3_third_party_admission.feature`, `tests/contracts/d4_mutations.feature` (BDD at the harness boundary: the actor is a harness operator invoking the replay tool, and the observable outcome is a diff report plus exit status; the tool's refusal diagnostics are contract, not incidental log text).

Acceptance: all four tiers run offline; D4 mutants each detected with the specific expected diagnostic; coverage report lists exercised and unexercised clauses.

### T1 — tooling fit (deferred, not implemented here)

Recorded in `TOOLING-FIT.md` as requirements on TemperMint: multi-target extraction, certificates binding specification + model + corpus + refinement theorem, per-module proof-cost accounting, and a distinct certificate kind for "refines a specification" versus "computes a specified value". No TemperMint change is made during S0–S7; the specification keeps its artifacts in the shape those requirements expect so the fit is additive.

## 14. Repository layout

```
PLAN.md  AGENTS.md  TOOLING-FIT.md
flake.nix  flake.lock
toolchain/{pins.toml,sources.toml}
spec/oasis/{amqp-core-*-v1.0-os.xml,NOTICE}
ledger/{clauses.json,coverage.json,dispositions/,ambiguities/}
lean/{Spec/,Generated/{Oasis,Core}/,Contracts/,Proofs/}
rust/{amqp-codegen-generated/,amqp-wire/,amqp-engine/,amqp-ref/,amqp-conformance/,tests/}
fixtures/{traces/,vectors/}
tests/contracts/
scripts/
certificates/           (created only when a real evidence package exists)
```

Directories appear with their first real file, exactly as in TemperMint: no empty scaffolding, no build caches, no generated files without their generator.

## 15. Repository and toolchain decisions

- **Environment**: this repository gets its own `flake.nix` whose pins are copied verbatim from TemperMint `toolchain/pins.toml` — Aeneas `227f4e7ac70d687a6b1a4871b3304f5a1c6994bf` (`nightly-2026.09.21-227f4e7`), Charon `a5591f6b94c8575a6ba2ae71090614a722f2b011` (LLBC `0.1.263`), Rust `nightly-2026-09-17` with `rustc-dev`/`llvm-tools`/`rust-src`/`miri`, Lean `v4.31.0`, mathlib `v4.31.0`, nixpkgs `b3d51a0365f6695e7dd5cdf3e180604530ed33b4`. Adding our own flake is not "adjusting the toolchain": TemperMint is untouched.
- **Cross-repository pin consistency**: a contract compares the revision set in `toolchain/pins.toml` against TemperMint's at `../TemperMint/toolchain/pins.toml` and fails on divergence, so the two environments cannot drift silently. This is the only cross-repository coupling, and it is read-only.
- **Extraction and certificates**: the pinned TemperMint CLI (`check`, `mint`, `replay`, `build`, `bench`, `perf`) is used unmodified, per function, with experiment descriptors, for any unit whose shape fits its current assumptions. Where it does not fit (multi-function extraction, spec binding, corpus binding), the requirement goes to `TOOLING-FIT.md`; we do not fork, patch, or vendor it.
- **Harness-contract runner**: `.feature` contracts are executed by `scripts/run-contracts.py` in this repository, adopting the runner idiom TemperMint established (a feature file names scenarios at the harness boundary; the runner is invoked per feature file). This is a new file here; TemperMint's copy is not modified.
- **Independent checkers** (evidence about the source or the model, never part of the checked claim): `miri` is already a pinned Rust component and runs the core's tests for UB and aliasing; Kani gives bounded model checking where the non-extracted layer needs it; Verus is available as an independent verifier with a different trust base (SMT) if a cross-check of the core is ever worth its cost. The axiom audit rejects `sorryAx` and unapproved axioms, and `native_decide` (whose `Lean.ofReduceBool` trust must be treated as an axiom) requires explicit disclosure before use.
- **No new dependencies** beyond the pinned closure without a recorded decision: the generators use the Python standard library (XML parsing included); the Rust core stays dependency-free; the Rust workspace's non-core crates may use an async runtime and TLS only in `amqp-ref`, and only after the S0 spike records the exact crates and versions.

## 16. Contracts, ownership, and test forms

Planner-owned (coder and reviewer MUST NOT modify; the conductor records SHA-1 for each before implementation, and a changed hash requires an explicit planner update and a regenerated manifest):

- `toolchain/pins.toml`, `toolchain/sources.toml`
- everything under `ledger/`, including dispositions and ambiguities
- `tests/contracts/**` including schemas and feature files
- `lean/Spec/**` (the frozen specification), `lean/Contracts/**`
- `fixtures/**` once a trace or vector is committed as contract (additions are made by the planner from recorded evidence)
- every module listed in each milestone's contract list

Coder-owned: `flake.nix`, `flake.lock`, `scripts/**`, `rust/**` except contracts, `lean/Proofs/**`, `lean/Generated/**` (regenerated only).

Test forms, matching TemperMint's discipline:

- Rust tests are behavior scenarios at the public caller boundary: a caller invokes a codec or a step function and the outcome is the returned value, the written bytes, and preserved inputs — never an internal call sequence.
- Lean specification properties and refinement theorems are theorem/interface-conformance contracts, not Given/When/Then: they are mathematics over a defined domain.
- Trace replay, mint/replay, and mutation tiers are BDD scenarios at the harness boundary, where the actor is the harness operator and the refusals and exit statuses are observable contract.
- Ledger, schema, and provenance checks are data/workflow contracts.
- No test in this repository may call a network service, a model, a real clock, or randomness. Third-party recording is a manual activity whose *outputs* are committed; replay is offline. Deterministic generators use committed seeds.
- Failure-first: every new contract is run and observed failing before its implementation, with the exact command and diagnostic recorded. A test never observed to fail protects nothing.

## 17. Verification gates (mechanisms, with their negative controls)

| Gate | Mechanism | Negative control |
| --- | --- | --- |
| Source identity | SHA-256 of vendored artifacts against `sources.toml` | mutate a byte in a copy; fetch/check must fail |
| Ledger completeness | every clause has a disposition; dispositions keyed by text hash | plant an undispositioned MUST; plant a `<b>MUST</b>`; plant a wrapped `MUST\nNOT`; each must be classified |
| Table fidelity | both generators regenerate byte-identically | mutate a descriptor code in a vendor copy; generation must change and the descriptor contract must fail |
| No hand-typed codes | scan of specification, proofs, and core for literal descriptor codes and `amqp:` symbols | plant a literal `0x14` in a proof; gate must fail |
| Executability | no `noncomputable`, no `partial`, spec builds under `lake build Spec.Exec` | plant a `noncomputable def`; gate must fail |
| Proof integrity | token-aware `sorry` scan and transitive axiom inventory per public theorem | plant a `sorry`; gate must fail |
| Extraction freshness | regenerate immediately before the proof build; second extraction byte-identical | patch the generated model; freshness check must fail |
| Differential strength | D4 mutants, each with an expected diagnostic | a mutant that no tier detects is a suite defect |
| Specification adequacy | third-party traces admitted by the specification | a trace admitted by the reference but rejected by the specification fails D3 |
| Determinism | replay produces byte-identical reports across runs and machines | inject wall-clock or a random seed; gate must fail |

## 18. Constraints and invariants

- The specification is *executable* and *independent* of generated code and of `rust/**`.
- `MAY`-clauses become nondeterminism in the relation, never a silent deterministic choice; `SHOULD` is never silently promoted to `MUST`.
- The extracted core has no unsafe code, allocation, I/O, globals, concurrency, FFI, build scripts, procedural macros, or feature-dependent bodies; capacities come from the caller; capacity exhaustion is a typed error with a mandated protocol error code.
- The same Rust source and configuration feed extraction and any native build; target, features, profile, and overflow settings are disclosed when a native artifact is named.
- Total correctness uses Aeneas `WP.spec` (`⦃ ⦄`), not `dspec`; failure and divergence are excluded.
- No hand-edited generated artifact; no `sorry`; no reachable `sorryAx`; no unapproved axiom; no hidden implementation-success premise; the public theorem's precondition stays inspectable and contains only domain obligations.
- Third-party traces are evidence about the OASIS text, not authority over it: a disagreement is recorded as a finding with a decision, never patched into the specification by mimicking a peer's bug.
- The trust boundary is disclosed exactly, and no claim may cross it silently. There is **no complete semantics of Rust in Lean**: the Lean side of the pinned toolchain is a library of models, tactics, and the `WP.spec` total-correctness relation — a target for translated code, not a semantics of Rust. The machine-checked part of our claims therefore begins at the Lean model, and the following are trusted rather than proved: (i) rustc's MIR semantics; (ii) Charon's MIR→LLBC translation; (iii) Aeneas's LLBC→functional-model translation; (iv) rustc/LLVM and the execution environment for any native artifact; (v) the restriction of every claim to the supported fragment (safe, sequential, no `async`, no dynamic dispatch, no allocation in the core). Corroborating evidence exists for the middle of that chain — the LLBC model and the borrow-checking/symbolic-execution performed during translation are mechanized in **Rocq** (`AeneasVerif/mechanized-llbc`; Ho, Fromherz, Protzenko, ICFP 2024, *Sound Borrow-Checking for Rust via Symbolic Semantics*), and the functional translation was formalized in the ICFP 2022 Aeneas paper — but that mechanization is **not inherited by our Lean path** and is cited as corroboration, never counted as part of our checked claim. Specification fidelity is likewise not proved: it is evidenced by the ledger, the ambiguity register, and third-party trace admission (§12 D3).
- Every public claim names its level: specification-level theorem, extracted-model equality, endpoint refinement, or differential-testing coverage. A feature that is only differentially covered is reported as exactly that, never as verified.

## 19. Risks and mitigations

| Risk | Concrete failure mode | Mitigation |
| --- | --- | --- |
| Specification over-narrowed | a conforming third-party trace is rejected | nondeterministic relation; D3 admission tests; over-narrowing treated as a bug class |
| Extraction fragment limits | the core's shape (mutable records, enums, `&mut [u8]`, `Result`) does not survive the pinned pair | S0 spike before interface freeze; smallest-supported rewrite keeping the API; minimal upstream reproduction recorded |
| Proof cost blowup | engine refinement for S4/S5 does not close in reasonable effort | per-feature refinement theorems; spec definitions kept structurally simple and computable; proof cost measured per milestone; the milestone's differential coverage stands independently if a refinement stalls, and that is stated up front rather than discovered late |
| Prose ambiguity | two readings diverge silently between spec and reference | ambiguity register with evidence; the reference's reading must be the register's reading; third-party traces decide |
| Two transcriptions drift | spec and reference both wrong, differently | differential tiers, mutant controls, generated tables shared by construction |
| Proof effort at protocol scale | the L3 refinement proof for the endpoint state machine does not close, and the milestone stalls | prove per-feature refinement theorems instead of one monolith; reuse the L2 codec equalities; keep the step function flat and synchronous (already forced by the fragment, §10); kernel-checked, agent-assisted proof labour is a real option at this scale — 2026 reports scale Charon/Aeneas/hax→Lean 4 pipelines to production Rust with agents writing proofs that the Lean kernel still checks (arXiv 2609.15648, arXiv 2605.30106) — and any feature that stays unproved is reported as differentially covered, never as verified |
| Trusted-translation defect | a Charon or Aeneas defect makes a proved statement wrong about the source | independent, cheap evidence on the same source: miri (already in the pinned toolchain) for UB and aliasing on the core's tests; optional bounded checking (Kani) for the non-extracted layer; optional independent verifier (Verus, different trust base) on the same core; none of these replace the proof, they bound the risk it is wrong |
| Scope creep into extensions | management/filters/JMS pulled in, core never closed | core Parts 0–5 only; extension point defined in §9; extensions listed as a backlog |
| Corpus acquisition | no access to a second implementation | recording is off-gate; the slice corpus is generated from our own reference first, and third-party admission is added when available without blocking milestones |
| Nondeterminism in tests | flaky replay, irreproducible reports | logical time only; explicit environment steps; committed seeds; determinism gate |
| Vendor artifact drift | OASIS copies edited locally, ledger silently stale | hash pins; disposition text hashes; notice and immutability note |

## 20. Acceptance commands

Run in milestone order. `shell` below abbreviates the offline pinned-shell invocation; the first `develop` realises the pinned closure, everything afterwards is offline and writes only into temporary directories.

```sh
alias shell='nix --extra-experimental-features "nix-command flakes" develop --offline --no-update-lock-file .#spec --command'
nix --extra-experimental-features 'nix-command flakes' flake metadata --no-update-lock-file
nix --extra-experimental-features 'nix-command flakes' develop --no-update-lock-file .#spec --command true

# S0 — sources, ledger, tables, spike
shell bash tests/contracts/a0_sources_ledger.sh
shell bash tests/contracts/a0_extraction_spike.sh
git diff --exit-code -- lean/Generated rust/amqp-codegen-generated   # regeneration determinism

# S1–S7 — specification and reference behaviour, per milestone
shell bash -c 'cd lean && lake build Contracts.TypeSystem'
shell cargo test --manifest-path rust/Cargo.toml --test wire_contract
shell bash scripts/replay-traces.sh fixtures/traces

# R2 — extraction and proof audit
shell bash scripts/extract-core.sh
shell bash -c 'cd lean && lake build Contracts.CoreRefinement'
shell bash scripts/check-proof-assumptions.sh

# D1–D4
shell python3 scripts/run-contracts.py tests/contracts/d2_trace_replay.feature
shell python3 scripts/run-contracts.py tests/contracts/d4_mutations.feature
```

Each milestone's contract list adds the concrete `lake build Contracts.<Module>` and `cargo test --test <name>` targets for that milestone; the block above is the spine, not the full set.

## 21. Work order and first actions

Order: **S0 → S1 → S2 → S3 (vertical slice, complete) → R1/D1–D2 on the slice → R2 L2/L3 on the slice → S4 → S5 → S6 → S7**, with D3/D4 widening as corpus and features land. The slice is closed completely — specification, reference, extraction, proofs, differential testing — before breadth is added, because the slice is what proves the method on this problem; widening coverage afterwards is mechanical by comparison.

First three concrete actions:

1. Vendor the six OASIS artifacts with hashes and notice; stand up the flake with TemperMint's pins and the cross-repository pin-consistency contract.
2. Implement `scripts/clause-ledger.py` and land the first disposition pass for Part 2 `#framing` and `#performatives`, with the planted-negative controls observed failing first.
3. Run the extraction spike on the endpoint shape (`&mut` state record, enum input, `&mut [u8]` out-buffer, `Result` error), record the minimal upstream limitation reproduction if it fails, and freeze the interface alphabet from what survives.

## 22. Deferred: tooling-fit change request (T1)

Recorded now, scheduled later, implemented in TemperMint rather than here:

1. **Multi-target extraction.** One descriptor per crate/function with a shared source-closure identity, so a protocol core with many functions produces one certificate rather than N independent ones.
2. **Specification binding.** Certificate format extension binding the specification module hashes, the acceptance declarations, the refinement theorem, and the trace corpus, alongside the existing source/model/contract/proof identity.
3. **Certificate kind.** A distinct kind whose claim is "this model refines this specification" (trace/simulation) rather than "this model computes this value", with the trust disclosure naming the specification's own assumptions (environment model, ambiguity decisions) as part of the claim.
4. **Proof-cost accounting per module**, so milestone reporting can attribute effort the way M5 did for optimization cost.
5. **Corpus dimension in replay.** Preserving TemperMint's property that replay regenerates and compares *all* claim-bearing inputs byte-identically, extended to the trace corpus and vectors.

The specification repository keeps these artifacts in the shape these requirements expect: separate descriptor files per unit, content-addressed corpora, and no assumption that one certificate covers one function.

## 23. How the two implementations are obtained (operational procedure)

Both are produced from the same pinned tables and the same frozen seams; they differ in purpose. The **reference** is optimised for auditability and proof: it is the conformance oracle, and clarity outranks speed everywhere in it. The **fast implementation** is the artifact that ships, and it exists only as *seam-local candidates*, each re-proved against the identical specification. Neither is generated from the other, and neither is generated from the specification: a generated fast implementation would require the generator itself to be verified, and a generated reference would make the differential tiers vacuous. The premise the whole design rests on is TemperMint's: the *search* need not be verified, and a candidate needs no certified transformation history — only the accepted result must be proved against a stable specification.

### 23.1 What both share, and is therefore frozen first

- **Generated tables** (`§6`) from the pinned XML: descriptor codes, field order, mandatory flags, defaults, choices, encodings, error conditions. No hand-typed code or symbol anywhere in `lean/Spec`, `lean/Proofs`, or the core crates.
- **Seams**: named functions with frozen signatures — `wire::decode_value`, `wire::encode_value`, `wire::frame_decode`, `wire::frame_encode`, `performative::{decode,encode}`, `engine::step_connection`, `engine::step_session`, `engine::step_link`, `engine::step_tx`, `sasl::step`. A seam is the only place implementations may differ; changing a signature invalidates every certificate that names it. Frozen at S0/S1 by contract.
- **The specification is the fixed target.** Everything else — layouts, iteration order, buffering, batching — is an implementation choice a candidate may change.
- **Per-unit extraction, proof, audit, certificate.** Identity, freshness, and regeneration checks exactly as TemperMint's `check`/`mint`/`replay` define them; correctness evidence and performance evidence never mix in one artifact.

### 23.2 Obtaining the reference implementation

1. **Land the tables.** `scripts/gen-oasis-rust.py` → `rust/amqp-codegen-generated`; regeneration byte-identical; the mutated-vendor-copy control fires.
2. **Freeze the seams** (§23.1) and the trace schema. Record the S0 spike's outcome: which of the three plausible state shapes survives the pinned pair — caller-owned `&mut [T]` slab with explicit `len`, `[T; N]` (Aeneas documents `Array T n`), or `Vec<T>`. The spike decides; the plan does not.
3. **Write each seam from the clause text**, in milestone order (S1 → S7), *not* by reading the Lean specification — the reference is the second independent transcription of the OASIS prose, and its evidential value comes from that independence. House style: flat explicit loops, no allocation, no early-exit cleverness, explicit state records, every error a named protocol error condition, every arithmetic operation already bounded by a stated invariant.
4. **Failure first, per seam.** The planner lands the fixture and its Expected Failure note; the coder records the actual diagnostic before implementing. A seam with no observed initial failure is not yet a contract.
5. **Immediate checks.** `cargo test --test <seam>_contract` at the caller boundary; `python3 scripts/replay-traces.py <corpus>` diffing the reference against the executable specification.
6. **Extract.**
   ```sh
   (cd rust && charon cargo --preset=aeneas --dest-file target/amqp-core.llbc)
   aeneas -backend lean -loops-to-rec -split-files \
     -dest lean/Generated/Core rust/target/amqp-core.llbc
   ```
   `-split-files` matters at this size: `Types.lean`/`Funs.lean` are generated, while `TypesExternal.lean`/`FunsExternal.lean` are hand-maintained models for anything opaque and are the only permitted hand-written part of the model. Every external model is named in the certificate's trust disclosure; a generated declaration with no explanation fails the M1-style generated-declaration audit. Generated files are never edited, and a second extraction must be byte-identical.
7. **Prove.** L2 equality per codec function (whole-function, over the full byte domain), L3 refinement per endpoint feature, L1 internal theorems where the specification itself needs them. Then the audits: token-aware `sorry` scan, `#print axioms` per public theorem, no reachable `sorryAx`, no undisclosed trust addition.
8. **Certify.** One descriptor per unit; `tempermint check` then `tempermint mint`; the package lands in `certificates/`. Where a native artifact is named, its build identity (target, features, profile, overflow settings, rustflags) is recorded with it.
9. **Interop.** `amqp-ref` plus the recording procedure produce the third-party corpus (≥2 independent peers) with provenance; admission by the specification is part of the acceptance, not an afterthought.
10. **Reference done when**: corpus replay is byte-identical against the executable specification, the declared proof levels are closed, the audit is clean, the certificate is minted, and two independent peers are recorded.

### 23.3 Obtaining the fast implementation

1. **Measure and profile the reference first.** Artifact-bound native build, exactly one allowed CPU, quiet probes taken at most three times, predeclared workloads in `bench/workloads.toml`. Per-frame cost in AMQP is dominated by syscalls, copies, and message size, so the profile — not intuition — decides which seams are worth touching. A candidate with no profile evidence behind it is rejected at review.
2. **Declare the candidate.** One seam, one transformation, one stated hypothesis about the cost it removes. Candidate implementations live in `rust/candidates/<seam>-<transform>/`; the engine skeleton is not forked, because duplicating the state machine would multiply the proof surface and destroy maintainability.
3. **Stay inside the fragment.** Safe, sequential, no `async`, no `dyn`, no allocation in the core, no threads, no SIMD intrinsics (they would need semantics supplied and proved). "Fast" therefore means algorithmically and representationally fast within safe sequential Rust — plus architectural wins in the disclosed I/O layer, which are measured but never claimed as verified.
4. **Implement the transformation.** The catalogue that this problem admits:

| Seam | Transformation | What it removes |
| --- | --- | --- |
| `frame_decode` | bound the body once, hand the cursor down; split header-then-body reads | repeated per-field bounds checks; double buffering |
| `performative::decode` | dispatch on descriptor once, decode fields to a fixed record; skip absent trailing fields by count | per-field option plumbing; re-dispatch |
| `performative::encode` | emit the mandatory prefix and truncate trailing nulls in one pass | intermediate field vectors |
| `wire::decode_value` | table-driven descriptor → decoder, small-int fast paths (`0x40`–`0x56`, `0x43`/`0x44` zero forms) | branch chains on encoding code |
| `wire::encode_value` | specificity-preserving writer that picks the narrowest encoding in one pass | decode-then-re-encode round trips |
| `engine::step_link` | maintain credit and delivery-count as explicit fields updated in the step, instead of recomputing from windows | repeated window arithmetic per transfer |
| `engine::step_session` | keep handle allocation as a free-list index, not a scan | linear scans in attach/detach |
| `engine::step_connection` | precompute decisions fixed at `open` (max-frame-size, channel-max, idle threshold) into the state record | re-derivation per frame |
| relay paths | pass payload bytes through by borrowing rather than copying into a result buffer | one full message copy per hop |
| driver (unproved) | coalesce outbound frames into one write; reuse buffers; batch flush | syscalls per frame |

5. **Run the conformance battery, in this order, and accept only on all of it**: byte-identical corpus diff against the reference → D4 mutation controls still fire (a candidate that weakens a check must be caught, not accommodated) → extraction → the *same-spec* theorems re-proved for the changed seam (L2/L3, unchanged statements — a candidate never gets a weaker specification) → regeneration freshness → audit → measurement against the reference on the predeclared workloads → certificate plus a **separate** measurement attachment bound to the artifact hash.
6. **Search policy.** Candidates may be proposed by a human or an agent; rejection costs nothing and leaves nothing in the tree; only accepted candidates are committed with their evidence. A candidate inherits no trust from the reference: the reference's proof justifies the reference, and the candidate is proved against the specification itself.
7. **Report honestly.** Correctness and performance are separate artifacts. A correct-but-slow candidate gets a correctness certificate; a fast candidate whose seam proof is incomplete is reported as differentially covered, with the gap named. Performance targets are outcomes, never gates, and thresholds are never tuned after seeing ratios.
8. **Fast implementation done when**: every changed seam has its own conformance theorem against the frozen specification, the composed core passes the full corpus, the native artifact is bound by hash to the recorded build identity, measurements are attached separately, and the unproved I/O layer's obligations are disclosed item by item.

### 23.4 The endgame composition

The shipped fast implementation is the composition of (i) accepted seam candidates over the reference skeleton, (ii) the disclosed I/O layer, and (iii) per-seam `Refines` theorems. A downstream Rust programme written by anyone else is obtained the same way: it presents the same seams, and its proof is the same `Refines` instance — which is why the interface was frozen in §9 before any implementation work began.
