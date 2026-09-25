# The old plan's forward text, as originally written

The new `PLAN.md` keeps these sections in an edited, forward-only form — trimmed of
counts and status, or compressed for length. Everything removed or reworded in that
edit is here **verbatim**, with the old line ranges, so the split loses nothing. Where
the new plan and this text disagree about a fact (a module's name, a rung's status),
the new plan and the record files are the correction; this is what stood before.

## Goal, third paragraph (lines 8–10)

Nothing here is Rust: extraction through Charon and Aeneas, proofs about a Rust programme, and performance work remain downstream (§23). What this repository now provides to that work is an executable oracle. **What is left out of that sentence is performance *work*, not measurement of our own instruments**: the corpus
executables' cost is measured off-gate with the results committed (§16), because this repository has twice paid for not measuring it — an accumulator appending to the end of a list made the corpus quadratic, and
it was found by someone noticing rather than by a measurement.

## §6's rules block (lines 94–107)

`scripts/clause-ledger.py` reads only the pinned artifacts and emits `ledger/clauses.json`: one record per normative statement, deterministically ordered.

- **Identifier**: `<artifact>#<anchor path>.<n>`, e.g. `amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions.42`. The anchor path is the chain of enclosing named elements (`section:framing`, `type:open`, `field:max-frame-size`, `doc:doc-idle-time-out`), because a bare `name` is not unique — `field name="value"` occurs inside many types — and `<n>` is the 1-based index of the statement within that anchor in document order. Anchor paths are what make ids stable under unrelated edits elsewhere in the artifact.
- **Fields**: artifact, anchor, index, kind (`MUST` | `MUST NOT` | `SHOULD` | `SHOULD NOT` | `MAY` | `REQUIRED` | `OPTIONAL` | `RECOMMENDED` | `NOT RECOMMENDED`), class (`MUST` for both MUST forms, else the kind), normalised text, text SHA-256, statement SHA-256, and the names of any `<xref>` elements the statement cites. **`index` counts statements within the anchor, and a sentence carrying two keyed phrases is two statements whose entries quote the same sentence**: `field:aborted.1` is the SHOULD phrase and `field:aborted.2` the MUST one, `field:aborted.1`'s text beginning "Aborted messages SHOULD be discarded" while its `kind` says SHOULD and `.2`'s says MUST. Eighty-eight anchor groups hold more than one clause that way, and the invariant that `class` is the kind's class (audited across all 579: none differs) is what tells the two apart. An auditor who finds identical text under two classes has found this convention rather than a defect — an earlier pass spent a query on exactly that.
- **Cross-references are resolved for the reader**: `<xref name="MIN-MAX-FRAME-SIZE"/>` renders as `512` through the generated `<definition>` constant table (13 constants, resolved across artifacts because Part 5 cites a Part 2 constant), while a reference to a named element renders as `«open»`, and a reference that **selects a choice** of an element renders the choice's own name (`«settled»`, `«unsettled»`) and records it in `references` as `<element>/choice:<choice>`. That third case exists because it was missing: two clauses differing only by a `choice` attribute both rendered as the element's name, so `settled.4` — requiring the settled flag true on at least one transfer — and `settled.6` — requiring it false on every transfer — presented **identical antecedents with opposite obligations**, and the specification, the reference and the corpus generator all read the collapse the same way. A rendering that resolves a reference *for the reader* must resolve it to what the sentence actually selects, which for a choice is the choice. A constant's value changing changes the clause text, so its disposition goes stale — which is the intended behaviour, since that is a semantic change. Cross-artifact references are recorded per clause so the link survives resolution.
- **Normalisation** must handle the real markup: inline emphasis around the keyword (`<b>MUST</b>`), keywords split across source lines (`MUST\nNOT`), entity-encoded text, and must not treat `<picture>` diagram text, `revhistory`, or `acknowledgements` content as normative. This is a token-aware scan, not a regular-expression grep, and it is verified by planted negative controls (§17).
- **Dispositions** (`ledger/dispositions/*.json`, planner-authored) key on `(id, text_sha256)`, so a source change that alters a clause's text makes its disposition stale and fails the contract — the mechanism that prevents silent drift between the OASIS source and the formalisation. **A disposition is a decision about text, not about a reference**: when the extended phrase list re-split a paragraph so that an earlier sentence took the `.u1` index, the honest repair was to move the existing decision onto the text it decides about and give the newly-indexed sentence its own disposition — re-recording the hash in place would have pinned a note about the `rejected` annotation's reserved key to a statement it was never made about. The mechanism caught it, and the repair had to be a decision rather than a renumbering.
- **Disposition values**: `formalized:<Lean declaration>`, `deferred:<milestone>` (a real obligation this plan carries later; the suffix names the milestone, so deferred work is visible rather than conflated with work we decided is not ours), `environment:<id>` (an assumption discharged by the environment model, e.g. "TCP delivers an ordered byte stream"), `out-of-scope:<reason>`, `underspecified:<id>` (the artifact deliberately leaves behaviour open: nothing is enforced, and tests must not assert either reading), `informative` (explanatory, with justification), `test:<vector id>` (a statement whose only observable form is a vector expectation), `superseded:<decision id>` (decided by an entry in the ambiguity register, §8). The last two additions were forced by real statements that fit none of the first six: S3's messaging obligations are ours and not yet carried, and the two hostname sentences are explicit silence rather than a scope decision.
- **Statements without keywords are captured too.** A paragraph can state a requirement without an RFC 2119 keyword — Part 1's map type says "A map in which there exist two identical key values is invalid", one sentence among two MUST clauses — and a keyword-driven ledger reports completeness while losing it entirely. Nine keyword-free sentences matching a normative phrasing were captured; one was the specification's own definition of the keyword vocabulary rather than a requirement, and is excluded. **The count is twenty-seven as of the session layer's work, and the growth is the more useful fact**: two shapes the list could not see — `cannot …` and `Only the … can …` — turned out to be how the artifact states a rule with neither a keyword nor a listed phrase, and extending the list surfaced eighteen statements nobody's scan reached: eleven in Part 2, including the three credit-ownership sentences the S4 contract rests on, the session state's frame bar and three error-condition definitions; six in Part 3, including the resumption options and the `section-number`/`section-offset` bounds; and one in Part 4 about coordinator links. Each carries a milestone disposition, so the obligation is visible rather than silently absent — which is what the capture exists for. Each becomes a statement of kind `UNKEYED` and `check_unkeyed` fails until it carries a disposition, so an omission is a decision. One of them turned out to be an instance of a rule already formalised (`Spec.Value.MultipleMandatory`, applied to `sasl-server-mechanisms`, which the artifact declares `multiple="true" mandatory="true"`), three are explicit silence about repeated hostnames and TLS mismatch, three are rationale or a reserved name, and two are deferred to S3. The gap this closes is a *class* of omission, not one sentence: the check is run per sentence, because a unit-level check loses the keyword-free sentence of a paragraph whose other sentences have keywords.
- **Pictures are reviewed, not merely skipped.** 104 pictures are excluded from clause extraction because most are sequence diagrams — but five carry formal grammar or normative keywords, including Part 1's formal constructor BNF, which is the specification's own statement of which octets are format codes, and two Part 3 diagrams that state the receiver's `resume=true` obligations. Those are listed in `ledger/pictures.json` with a content digest and flagged `looks_normative`; `check` fails until each carries a disposition keyed to that digest, and fails again if the picture's text changes. Excluding a subtree is a decision, and the ledger makes it one.

## §8's opening entries (lines 224–234)

Entries opened at S0, from the clauses inspected while writing this programme:

- session window recomputation (`next-incoming-id` / `incoming-window` derivation of `remote-incoming-window`, Part 2 `#sessions`) and which window updates are "MAY (depending on policy)";
- `open.idle-time-out` — the local threshold rule, the halving recommendation, and which peer closes;
- `attach.initial-delivery-count` versus the first `flow.delivery-count`, and what a receiver must infer;
- `flow.available` for senders that cannot determine availability;
- link resumption: which fields change identity versus state;
- message fragmentation: the `more` flag, session-window interaction, and abort semantics;
- `received` (`section-number` / `section-offset`) obligations for partially transferred messages.

## §9's note on the module list (lines 259–264) and the starting-state paragraph (272–276)

*These are the modules the tree holds. Earlier versions of this section named `Wire.lean`, `Performative.lean`,
`Endpoint.lean`, `Flow.lean`, `Sasl.lean`, `Exec.lean` and a `Spec/Conformance.lean`; the implementation settled them
elsewhere — the header and framing into `Frame.lean`, the performatives into `FrameCodec.lean`, the state machines into
`Connection.lean` and `Session.lean`, SASL into `Connection.lean`, the driver into `Main.lean`, and the conformance
interface into `Contracts/Conformance.lean` where it belongs. **The exemption rule for forward-promised `formalized:`
values reads this list, so a name kept here that the tree will never hold protects values that nothing checks** — which
is why the earlier names are recorded as folded rather than left as plans.*

**And the specification's starting state is stated for a *layer*, not for AMQP alone** — `Endpoint.initialFor (layer : Layer)`, with `Endpoint.initial` as the AMQP-layer case — so that an
implementation's starting state can be *proved* against a specification state rather than assumed equal to one. The corpus's `AMQP\x03\x01\x00\x00` announces the AMQP layer while a peer that
offers SASL first begins in the security layer, so a constructor fixed to AMQP would have made every shell that starts in SASL assume precisely the thing the specification exists to state. The
general shape is the one the independence rules ask for: a constructor parameterised by the *choice the standard leaves open*, rather than a constant that encodes our reading of it. The endpoint
slice's other half is the same decision from the consumer's side — the shell calls the construction the specification declares, so the two cannot drift, and no second way into that state exists
to drift towards.

## §11's vector example (lines 971–979)

```json
{"vector":"span-004","kind":"positive","provenance":{"role":"server","source":"clause",
   "refs":["amqp-core-transport-v1.0-os.xml#sessions.42","…#flow.7"]},
 "steps":[{"dir":"in","bytes":"414d515000010000"},
          {"dir":"out","expect":"bytes","bytes":"…"},
          {"dir":"out","expect":"action","action":{"kind":"credit","link":0,"value":100}},
          {"env":{"tick_ms":500}}]}
```

## §13's preamble (lines 1016–1019)

Each milestone: scope, planner contracts, the failure expected before implementation, and observable acceptance. Coverage is stated in ledger terms and superseded by `ledger/coverage.json`.

## §15's runner bullet (line 1638)

- **Harness-contract runner**: `.feature` contracts are executed by `scripts/run-contracts.py` in this repository, adopting the runner idiom TemperMint established (one feature file names scenarios at the harness boundary; the runner is invoked per file). It is a new file here; TemperMint's copy is not modified.

## §17. Verification gates and their negative controls (lines 1936–1952)

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

## §16's ownership lists as written (lines 1642–1652)

Planner-owned (coder and reviewer MUST NOT modify; the conductor records SHA-1 for each before implementation, and a changed hash requires an explicit planner update and a regenerated manifest):

- `toolchain/sources.toml`, `toolchain/downstream-pins.toml`
- everything under `ledger/`, including dispositions and ambiguities
- `tests/contracts/**` including schemas and feature files
- `lean/Spec/**` (the frozen specification) and `lean/Contracts/**`
- `vectors/**` once a vector is committed as contract

Coder-owned: `flake.nix`, `flake.lock`, `scripts/**`, `lean/Proofs/**`, `lean/Generated/**` (regenerated only), `HANDOFF.md` under planner review.

## §19. Risks and mitigations (lines 1963–1977)

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

## §20's acceptance block as written (lines 1978–2006)

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

## §21. Work order and first actions (lines 2008–2016)

Order: **S0 → S1 → S2 → S3 (vertical slice, closed completely) → V1–V4 on the slice → S4 → S5 → S6 → S7 → H1**, with recorded third-party vectors added to V3 as they become available. The slice is closed completely — clauses dispositioned, theorems, vectors, adequacy, mutations — before breadth is added, because the slice is what proves the method on this problem; widening afterwards is mechanical by comparison.

First three concrete actions:

1. Vendor the six OASIS artifacts with hashes and the notice; stand up the flake with Lean and mathlib pinned to TemperMint's revisions.
2. Implement `scripts/clause-ledger.py` and land the first disposition pass for Part 2 `#framing` and `#performatives`, with the planted-negative controls observed failing first.
3. Freeze the interface alphabet, the environment assumptions, and the vector schema — then write the Part 1 tables generator and its mutation control, so `Value.lean` starts on generated data rather than transcription.

## §22's rules as written (lines 2018–2027)

The remaining milestones are decomposed into slices that can run at the same time without sharing a file, because the cost of a parallel batch is the interface that has to be fixed before it starts and the conflict that follows if it is not. Three rules hold for every batch:

* **interfaces are fixed by the planner before the batch starts** — a state type, a dispatch hook, a corpus schema. A slice that discovers it needs a different interface reports that; it does not negotiate one with its sibling, because two coders agreeing on an interface is not the same as the interface being right.
* **file ownership is disjoint, and the shared boundaries are named rather than discovered.** There are two, and the first version of this rule claimed there was one. The generator is shared between slices that add corpus families, so it is split before a wave needs two of them to touch it. **The harness is shared with everything** — every executable imports it, and so does every proof that touches a corpus — so a slice editing it can break four other slices' builds while being entirely within its brief. The rule for it is stricter because the blast radius is larger: a slice that must edit it advances it in compiling steps, and if two slices need it in the same wave the planner sequences them rather than handing it to one and hoping.

The mechanism turned out to be subtler than "keep it compiling between edits", and the slice that owned the file was in fact building after every edit. An edit *in progress* is an inconsistent file: the window between two compiling states is one a sibling's build can land in, and what the sibling then sees is an error naming a file it does not own. So the useful rules are weaker and more practical than "never break it": **write shared files whole rather than in a sequence of small edits where the tool allows it**, because a single write has no inconsistent window; **say so when you are mid-edit**, so the slices that depend on the file know a failure is expected rather than evidence of a defect; and **believe the owning slice over a build log** when the two disagree about whether the file compiles, because the log is a sample of a moving target. This was learned by paying: a mid-edit harness blocked two proof slices for the length of an edit, one of them retrying a build that could not succeed.
* **one integration owner** — the planner runs the acceptance commands, not the slices, since a slice that validates its own work is validating against its own reading of the contract.

## §23's introduction as written (lines 2051–2058)

This repository holds the specification **and**, from the implementation track recorded at the end of this section, a reference implementation of it: an AMQP 1.0 endpoint written in Lean, compiled natively, whose protocol core has the frozen interface's conformance relation *stated* for it, the proof owed (R3), with **two** named unproved parts: its socket boundary, and the Lean shell that drives it. The *core* is what is proved; a reader who takes that for a claim about the process has been misled by an omission rather than by an overstatement, which is why the shell is named here. The remaining work — a Rust implementation, its extraction through Charon and Aeneas, proofs that it conforms, performance evidence — belongs to TemperMint and is scheduled there; this repository's endpoint is a *second instance* of the same conformance relation rather than a replacement for that work. What the specification work needs from here, and what `HANDOFF.md` records:

## §23.4 The route to a real server (lines 2156–2170)

**Partly adopted.** Item 5's order is now the programme of record for this repository. Items 1–4 remain the recommendation that explains that order, and §23.5's second repository remains unadopted.

**1. The boundary is measured, and it decides the split.** §23.3's first category is the standard's own division rather than a gap: `source`/`target` semantics, routing, queues, filters, `dynamic` and node properties are the clauses the ledger classes `out-of-scope: node-and-filter-behaviour` and `out-of-scope: container-node-topology`. A specification that added routing would be specifying something else, and a broker built in this tree would be the first artefact here not checkable against the standard — the one property the tree exists to keep.

**2. What stays here.** The protocol, the corpus, the differential and the proved core, and §23.2's server narrowed to what this repository can state: no node model, no format above AMQP. Its messages are Part 3's — the layer this repository specifies and still owes through S5 — and its body a `data` section. Even that is worth doing only when there is an audience: R4 already proves the endpoint is a server, so a demo's marginal value is communication rather than evidence.

**3. The demonstration worth building is the specification narrating live traffic.** R4 drives the shipped binary over a socket and compares its per-step verdicts against the specification's in-process ones. Put a real third-party AMQP client at the other end and print, per frame, the verdict, the condition and the rule in words, with one mutation client whose violation is refused and quoted. That shows what nothing else can — a clause-level view of a real client's session — and it needs **no node model, no CloudEvents and no seam migration**, because it uses machinery that is built and green. A node server, by contrast, demonstrates a worse broker.

**4. The real server belongs in another repository, and its first artefact is its own specification.** Queues, routing, an address grammar, an application format, concurrency and durability have no AMQP clauses to conform to, so they need a node model stated its own way; this repository's *method* is the transferable part — a clause ledger, dispositions, an ambiguity register, gates. What it draws from here is what this repository exists to supply: the specification, the corpus, and `r4_wire_differential.sh`, which checks any shipped binary in any language by running it. Its implementation should be Rust through TemperMint, whose own plan already names what it needs from here.

**5. Order, adopted.** The widening comes first (26 clauses, contracts before implementation), then S5's message layer, then the narrator demonstration. Parts 1 and 2 are re-frozen with the exact link and unsettled-table indexes; part 3's twelve scenarios are carried; and part 4's implementation, projection proof, widened-conformance proof, and completed-disposition correction are present. Landing waits only on the targeted index-invariant verification and the final conductor sweep. The node server leaves this tree entirely, and its five clauses go with it. This order is not preference: the message layer depends on unsettled and settlement state, and the narrator needs both to say anything stronger than R4 already proves.

## §23.5 The second repository (lines 2171–2188)

**Recommended rather than adopted.** Adopting §23.4 item 5's order does not adopt this second repository, its name or its interface.

**The name: `SpecMQ`.** It follows this repository's convention of naming the *artefact* rather than the product — `SpecAMQP`, `TemperMint` — and it carries one ambiguity to resolve in its own first line: AMQP's M is *queueing* as well, so its description must say what it specifies, **the node layer above AMQP 1.0 core**, and what it is not, a replacement for the protocol. `SpecAMQP` stays the protocol; `SpecMQ` is what a server must *do* that the protocol leaves to it. If that ambiguity is unwelcome, `SpecNodes` is the accurate alternative and reads as jargon; `SpecBroker` reads as a product rather than a specification, which is the failure mode this repository's naming avoids.

**Its first artefact is its own specification, not scaffolding** — the same rule `TemperMint` states about `bench/` and `certificates/`, applied to a repository's opening move. A clause-level ledger of the node model: what a queue is, how a delivery is offered, settled, released and redelivered at the node, what a subscription means, what an address names, and what a filter may say. Authored the way this repository authors its own — clauses with ids, dispositions, an ambiguity register for every reading taken, gates that fail loudly — because **that method is the transferable thing**; nothing else here transfers.

**Its second artefact is a conformance interface in this repository's shape**: a state machine over a frozen interface alphabet, so a server can be *proved* against `SpecMQ` the way the endpoint here is proved against `SpecAMQP`. The relation is what a second repository should aim at, not the code.

**Its interface to here is already built.** The corpus and `r4_wire_differential.sh`: the protocol half of any server is checked by running its binary against this specification's per-step verdicts over a socket, whatever language it is written in.

**Smallest first, and the temptation to resist.** A queue with settlement at the node, and nothing else — no topics, no routing, no address hierarchy — until that much has a specification, a proof and a gate. The temptation to make `SpecMQ` a broker is the one thing that would stop it being a specification.

**What a node publishes, and where that convention comes from.** A server has to answer not only what it listens on but what it *provides*, and the protocol's own hooks for that exist and go unused: a terminus's `capabilities`, and `open`, `begin` and `attach`'s `desired-capabilities` and `offered-capabilities`. This ledger classes them `out-of-scope:extension-capabilities` (five clauses) precisely because no declaration in either reading reads them — grep: zero hits — so the fields are carried by the generated surface and nothing else. Outside the core, two published conventions do the same job and neither is a client-library invention: the **AMQP Management** specification defines a *virtual management node* queried over AMQP itself, with CBS's `$cbs` as the worked example (a client establishes a link pair and passes requests on the outbound link), and brokers publish *address grammars* instead — RabbitMQ documents `/queue/:q`, `/topic/:r` and `/amq/queue/:q`, where the address's *direction* carries the semantics: a target names an exchange, a source a queue. Outside AMQP entirely, Kafka is the clearest real case of a broker publishing what it provides, a metadata request returning topics, partitions, leaders and endpoints.

So SpecNodes' first version should **read AMQP Management before inventing a publication format** and **use the capability fields the core already has**. That turns five out-of-scope clauses here into the second repository's interface rather than a permanent exclusion, and it means the node model's first published act is one the protocol already makes room for.

---

## Appendix: pre-split lines the new plan carries only in edited form

Restored mechanically by the conductor from `git show 56aaea2:PLAN.md` — the pre-split bytes — because
the split reworded the sections below rather than moving them, and a record that claims preservation
should hold the original text. Line numbers are those of the pre-split file. Nothing here is a current
claim about the repository; it is the wording as it stood before the split.

       54  | D-g | Conformance interface: the definition of what it means to implement this specification | `lean/Spec/Conformance.lean` |
       56  | D-i | Executable driver over the vectors (`lake exe amqp-spec`) | `lean/Spec/Exec.lean` |
       63  - **No Rust, no extraction, no performance work.** The reference implementation is in Lean, and it is the only implementation here. A Rust programme, its extraction through Charon and Aeneas, proofs about it, optimised candidates and performance *targets* belong to TemperMint and are scheduled there (§23). **What this repository does measure is its own instruments**: the two corpus executables' wall
       64  time and peak RSS over named workloads, off-gate and with the results committed under `bench/`, because the corpus's cost decides how far it can grow and because two performance defects made it unusable before anyone
       65  measured anything. The distinction is deliberate — **measurement here, optimisation there** — and the numbers are not a claim about any downstream artefact's speed.
       67  - **No protocol extensions.** AMQP management (`amqp-man`), filter expressions (`filtex`), claims-based security (`amqp-cbs`), addressing, JMS mapping, HTTP-over-AMQP, event streams, and connection-info are out of scope; they exist as working drafts in `oasis-tcs/amqp-specs`, not as part of the OASIS Standard for core AMQP 1.0. Core must nonetheless model how unknown described types and pass-through annotations are handled.
       70  - **No verified native execution claims, and no claims about any programme.** The specification states what a conforming endpoint does; it does not certify anything.
       71  - Calendar promises. Progress is reported in coverage units: clauses dispositioned, declarations, vectors, theorems.
       79  1. **The definition language is present and machine-readable**: `type` (with `class` ∈ {primitive, restricted, composite}), `field` (with `type`, `mandatory`, `default`, `label`), `choice` (with `value`), `descriptor` (with `code` as `domain:descriptor`, e.g. `amqp:open:list` = `0x00000000:0x00000010`), `encoding` (with `code`, `category`, `width`). Sections carry stable `name` attributes (`framing`, `sessions`, `links`, `performatives`, `txn-declare`, `primitive-type-definitions`, …) which anchor every clause identifier.
       86  Three independence rules keep the evidence meaningful, and each has a gate (§17):
       89  2. **Vectors are authored from the clauses and from recordings, never from the executable specification.** A vector produced by running the specification would only prove the specification equals itself. The author of a vector reads the OASIS text (or a recorded third-party exchange) and writes down what must happen.
      104  - **Coverage report** (`ledger/coverage.json`) aggregates per artifact and per anchor, and is regenerated per milestone; acceptance commands diff it against the previous milestone's report so a coverage regression is visible rather than merely regrettable. It also reports picture coverage: total, reviewable, dispositioned.
      105  - **No clause can escape the ledger.** A crude token census (every text node, split by whether it sits in an excluded subtree) is compared against what the ledger accounted for, per artifact and per keyword; a keyword token in non-excluded prose that produced no clause fails `check` and names the offending element and text. This gate is what makes the ledger's completeness a measurement of the walk rather than a property of its author.
      106  - **The baseline reconciliation cannot drift.** `ledger/reconciliation.json` records the crude-scan numbers per artifact, this ledger's numbers, and the named mechanism explaining every difference; `check` fails if the recorded numbers stop matching the generated ledger, so revising the ledger means revising the record deliberately.
      198  `scripts/gen-oasis-lean.py` reads the pinned bytes and emits `lean/Generated/Oasis/`, one module per declaration kind:
      200  | Module | Contents | Records |
      202  | `Constants.lean` | the `<definition>` constants, with `constantValue?` lookup | 13 |
      203  | `Types.lean` | declared types, their class, source, semantic `provides` roles, descriptor, and artifact anchor path | 96 |
      204  | `Fields.lean` | fields in wire order with owner, index, type, mandatory flag, declared default, `multiple`/`requires`, plus `fieldsOf`/`mandatoryFields` | 125 |
      205  | `Encodings.lean` | the 39 encodings with constructor octet, category, size width, and `encodingOf` | 39 |
      206  | `Choices.lean` | declared choices, the error-condition families, and `errorConditionsOf` | 54 |
      207  | `provenance.json` | the artifact digests and record counts the modules were derived from | — |
      217  Two normalisations are deliberate and documented in the generator. Labels — the human-readable attribute text — have whitespace runs collapsed so generated diffs stay stable; no data field (value, code, flag, default) is touched. And each declaration carries the anchor path it came from, which is what links a generated record to the clause ledger's identifier for the same element.
      219  Module naming is path-derived (`lean/Generated/Oasis/Types.lean` → `Generated.Oasis.Types`), and each generated module is self-contained: `Choices.lean` imports `Types.lean` because the error-condition lookup needs the type table, and nothing else.
      223  AMQP 1.0's prose is not uniformly exact; several areas admit two readings, and real implementations disagree in practice. `ledger/ambiguities/*.json` records, per issue: the clause ids involved, the candidate readings, the reading adopted, the evidence (clause citation, third-party behaviour), and the consequences for the conformance relation.
      235  Adopting a reading is a decision *with evidence*, recorded in the ledger as a `superseded` disposition pointing at the decision. Where a mainstream implementation disagrees with our reading, the disagreement is a recorded finding, not a licence to weaken the specification — the specification states what the OASIS text requires, and the register states where practice diverges.
      265  - **Executable.** Every definition in `Spec/` is computable; `Exec.lean` runs the vector corpus and reports per-vector verdicts. `noncomputable` and `partial` are rejected by contract.
      266  - **Total where the protocol is total.** Decoding functions return an explicit error result rather than a default; there is no silent truncation and no "best effort" parse.
      267  - **Independent of consumers.** No `Spec/` declaration refers to any implementation, module path, or artifact outside `lean/` and `spec/oasis/`.
      268  - **Nondeterminism is explicit.** Where the OASIS text says MAY, the choice is a first-class input to the specification (a policy stream), not a hidden decision inside a Lean definition. This is what makes the specification testable and what keeps it from being accidentally narrower than the standard.
      269  - **Canonical encodings are specified.** The type system is formalized with specificity preservation, so round-trip theorems hold on a stated equality class rather than on "some bytes came back".
      969  One shared format for everything the specification is tested against: NDJSON, schema-validated (`tests/contracts/vector.schema.json`), **logical time only** — timestamps are ordering tags, never wall-clock, so replay is deterministic on any machine.
      982  - `refs` cite the clauses a vector is testing, and the coverage report cross-checks them against the ledger, so vectors cannot accumulate free of the clauses they claim to exercise — and clauses cannot be claimed as tested by vectors that do not cite them.
      998  V4 is what makes V2 and V3 load-bearing. A mutation that no tier detects is reported as a suite defect, not quietly tolerated.
     1014  Recording third-party vectors is a manual, credentialed, off-gate activity: run an existing peer implementation (Qpid Proton, Apache Qpid J/Artemis, RabbitMQ 1.0, Dispatch router — two or more), capture the bytes with harness glue, commit the capture with provenance. No test in this repository contacts a network service, a model, a clock, or a random source; recorded captures replay deterministically offline.
     1020  ### S0 — basis, ledger, tables, and the frozen interfaces
     1036  ### S1 — type system (Part 1)
     1093  ### S1.5 — the codec's laws, proved in rungs
     1382  ### S2 — framing and performatives (Part 2 structural)
     1417  ### S3 — connection lifecycle and the vertical slice
     1461  ### S4 — sessions, links, and flow control
     1495  ### S5 — messaging (Part 3)
     1523  ### S6 — transactions (Part 4)
     1531  ### S7 — security layer (Part 5)
     1545  ### H1 — handoff
     1636  - **Integration contract.** The Lean project is a normal Lake package with path-based module names (`Spec.*`, `Contracts.*`, `Proofs.*`, `Generated.*` under namespace `SpecAMQP.*`), importable as a dependency by downstream tooling. No symlink or re-export layer is introduced.
     1637  - **No new dependencies** beyond Lean, mathlib, and the pinned closure without a recorded decision. The scripts use the Python standard library, XML parsing included.
     1656  - **Ledger, schema, and provenance checks** are data/workflow contracts.
     1658  - **Failure-first**: every new contract is run and observed failing before its implementation, with the exact command and diagnostic recorded. A test never observed to fail protects nothing.
     1860  direction — one says the output must equal what the generator produces, the other says the check must look at the generator when the output is legitimately changing under it.
     1957  - Semantics are handwritten; generated tables are data; no clause's meaning lives outside the ledger.
     1958  - Vectors are authored from clauses or recordings, never produced by the specification.
     2008  ## 21. Work order and first actions
     2018  ## 22. Parallel work order, S3 to S7
     2102  **What this track does not claim.** Not that the binary is verified — the compiler link above is trusted and disclosed. Not that the shell is proved; it is the named hole, and it is kept small enough to read. Not performance: the endpoint is a reference to compare against, and measurement belongs to TemperMint where it is scheduled. And not that the endpoint replaces the second reading in `lean/Ref/`: the differential between two independent readings of the standard is a check on *the specification*, and adding a third runner over the same corpus does not make it redundant.
     2104  ### 23.2 The demonstration server — scope, revised after review
     2189  ## 24. The widening's contracts
     2252  ## 26. The widened model's shape
     2286  ## 27. What the tail trial found: the notes navigate, they do not cost
