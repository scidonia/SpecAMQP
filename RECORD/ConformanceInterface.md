# The conformance interface — §10's design rationale

> Moved verbatim from `PLAN.md` §10 (lines 278–966) on 2026-09-25. The interface
> itself is frozen in `lean/Contracts/Conformance.lean`; the plan keeps the frozen
> facts and the six defining rules in one line each and points here for the argument.
> Status claims below are the record of what was true when written.

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

**The interface is landed, and its first instance is the reference rather than a downstream programme — a scope decision taken on the user's instruction that revises the sentence above.** The reference implementation is in Lean and is the only implementation in this repository, so proving `Conforms spec ref` needs no extraction toolchain: both sides are trees this repository already builds. The reason to do it here rather than to wait is the same reason the interface was frozen early — a relation nobody has instantiated is a definition nobody has tested, and the first instance is where a conformance relation turns out to be either usable or under-specified. What it buys is a tier change — **and this is the sentence the value layer's finding came apart under, kept and annotated rather than rewritten, because what the work was for and what has happened are both worth having in the record**: the reference's agreement with the specification was to stop being evidence from a differential over a corpus (V2) and become a theorem (V1), with the differential left doing what only it can do — falsifying *readings* of the prose. The theorems were written; their premises were then refuted at concrete witnesses (the paragraphs below), so **the agreement has not become a theorem**, and the differential is not merely left falsifying readings — it remains, as before, the only tier that could establish the agreement, and it does not, because the divergent buffers are in no corpus. *Adding them is part of the fix*: once the two readings agree on the case, a vector pins it and the differential can see it, which is the step that would make the tier change real rather than intended.

The proof's shape is fixed by `lean/Contracts/Conformance.lean` and is the same for every layer: the specification as an `Endpoint` whose `choose` is the singleton of a step's permitted outcome, with each `MAY` a named parameter rather than a silent branch; the reference as an `Endpoint` whose `step` is the partial function it already is; a simulation relation `R` between their states; and `ConformsVia R`. `R` is the work. The layers land one at a time, the frame layer first because its observable is the wire and its state is smallest, and each instance is a contract that a later refactor of either side must keep.**

**Three instances have landed, and the third one found a hole in a per-step vocabulary it had written rather than in this section.** The frame layer's receive and send instances were joined by the connection layer's — `Contracts/ConnectionConformance.lean` declaring `Conforms specConn refConn`, `Proofs/ConnectionConformance.lean` proving it — with the two frame readers' agreement a named hypothesis rather than an assumption, and the instance load-bearing in the sense that matters: weakening the simulation relation to the state table's state alone stops the composition compiling, with five errors at the call sites that need the layer, the dialogue's phase, the announced mechanisms and both sides' limits.

**The hole, and the review that closed the question.** Composing two instances needs each step's two answers to be the **same** answer; the per-step relation as first written was a pair of implications — `spec = ok → ref = ok` and `ref = error → spec = error` — and those are **both vacuous in exactly one direction**: when the specification refuses and the reference accepts. That is the direction that matters, because a reference strictly more permissive than the specification would escape the relation entirely, while the reverse mismatch is *not* vacuous — `spec = ok` makes the first conjunct demand the opposite constructor of the reference's answer. The fix is a **shape equality** (`isOk` agreement), delivered by every step slice alongside the implications, and it is load-bearing rather than decorative: without it the `spec = error` / `ref = ok` case cannot be eliminated and the output lists cannot be compared at all. **No strengthening of `Conforms` is needed and none was made**: this section already demands a concrete matching permitted step, a related successor and exact equality of the output lists, so the weakness was never in the contract — it was in a step vocabulary written inside one proof module, and it is closed there. What the episode leaves behind is the general shape: a pair of implications relating two *constructors* is vacuous in the direction where the weaker side says nothing, and a relation meant to catch over-permissiveness has to say the direction out loud.

**And the relation's components are each load-bearing, which is a claim that needs controls rather than confidence.** Two weakenings were built and both *fail* to compile, five errors each. The first reduces `RConn` to the state table's state alone, so the relation is doing more than the state table. The second keeps six of its components — state, protocol id, the announced-by role, the offered mechanisms, and both sides' limits — and omits only the dialogue's phase, so the *SASL stage* is separately needed rather than carried along by the others, which is the component a reader would most plausibly assume was implied. A weakened relation that compiled would have been the finding; the controls exist so that "the relation is load-bearing" is a measurement rather than a hunch, and a proof that compiles is not by itself evidence that its hypotheses are doing work.

**And the hypothesis treatment is now consistent across all three**: each instance names the layer below as an explicit hypothesis — `ValueLayersAgree` for the frame's receive, `ValueCarrierAgree` and `ValueWriterAgree` for its send, `ReadersAgree` for the connection — rather than assuming it. That is not a weakening: the hypothesis is a claim this repository also makes, and naming it is what lets a reader see what an instance rests on and what would discharge it.

**Accepted, with the evidence rather than the claim.** `lean/Proofs/ConnectionConformance.lean`, 5530 lines, SHA-1 `add572e8…`, no `sorry`, `lake build Proofs.ConnectionConformance` clean at 518 jobs; `Contracts/ConnectionConformance.lean` declaring the instance at this section's type, which a review put side by side with the interface's own text and found neither narrowed nor restated; the trust gate green through all four clauses with the instance's five declarations in the axiom inventory; the corpus gates green including the whole-package build; a capture of 137498 verdict lines from both artefacts, identical before and after the landing, stated as *no regression* and not as coverage; and the two relation mutations failing with five errors each — re-run after the eleven provably-dead reductions were deleted, at the same five conformance-composition sites both times, so the control survived an edit to the proof it is testing. The two vacuity lemmas' own axiom inventory is `[propext]` alone.

**One review finding against it, and it was against a sentence rather than a proof.** The description of the vacuity was overbroad — it is vacuous in one direction, not whenever the constructors differ — and the correction made it *checkable* rather than merely right: `answersMatch_of_spec_refuses` proves the escape exists and `not_answersMatch_of_ref_refuses` refutes the reverse mismatch, both beside the definition they are about, because a docstring asserting a property of a relation decays the moment somebody edits the relation and a theorem does not. The same review cleared this section explicitly and recorded that the shape equality is load-bearing in the composition rather than decorative, which is the answer to the question the section had opened against itself.

**The value layer's instance is discharged, and the frame layer's receive half is now unconditional.** `SpecAMQP.Proofs.valueLayersAgree : ValueLayersAgree` — **no hypotheses**, axioms within
`[propext, Classical.choice, Quot.sound]` — and `Contracts.frame_conformance_public valueLayersAgree` typechecks at `Conforms specFrame refFrame`, so what this section called "conditional and undischarged
rather than vacuous" is now a statement about these two endpoints rather than about what would follow. The contract gained `frame_receive_conformance` for exactly that: the applied form is the acceptance
declaration, and its being unconditional is the difference the section insisted on. **Four instances are now landed** — frame receive, frame send (conditional on the writer law, with its consequent
separately recorded as false for a reachable array body), connection, and the value layer's.

**And the connection instance is discharged too, and it took a missing *step* rather than a missing fact.** `Proofs.readersAgree : ReadersAgree` — no hypotheses, axioms within the accepted set — and
`Contracts.connection_conformance : Conforms specConn refConn` applies it, so the connection layer joins the frame layer's receive half as an **unconditional** `Conforms` instance. The hypothesis it replaces was
open for a reason worth stating precisely: `ReadersAgree` demands `FramesAgree` on the frames, which includes `ValuesAgree` on the body — the whole value, elementwise — while the layer beneath it speaks in the
*view* vocabulary a frame reader actually consults, since **a frame reader reads a body only to ask which declared type its descriptor names and whether the frame type's role is among that type's `provides`**.
So the connection layer's hypothesis was one notch stronger than the frame layer could reach, and it stayed open until the value law's proof — which carries `BodiesAgree` internally and weakens it to view
equality only at `valueLayersAgree` — donated the step, `valuesAgree_of_bodiesAgree`. **That is the fourth shape of this kind in one layer**, after the writer's reader-reachable domain, the wire law's cursor
bound and the fuel irrelevance above the octet bound, and its distinguishing feature is that the stronger relation was *true*: what was missing was the step between two spellings of the same relation, not the
fact. The frame send half remains conditional on the writer law, with its consequent separately recorded as false for a reachable array body.

**And the discharge survived an independent review that was looking for exactly the failure modes this repository has produced before.** The reviewer measured both axiom sets itself rather than reading them
from a report, found the contract's `ValueLayersAgree` declared exactly once with no narrower copy anywhere in the tree, traced the joint induction and confirmed **no circularity** — every recursive use
consumes strictly lower fuel than the level being established, with `wireAgrees_succ`'s `ElementsDecideBelow K` supplied from the induction hypothesis at `K` rather than forwarded — checked that both
sweeps cover exactly the forty octets the reference's own literal dispatch accepts (by proving, in a fresh scratch file, that every entry satisfies `assignedConstructor` and `elementDecl?`, that both lists
have length forty, and that they are equal), and confirmed the dispatch consumes each arm one level below the conclusion. It also independently reproduced the *historic refutation* — `#eval` at fuel 2 on
`#[0xE0,0x02,0x00,0x40]` gives the reference `ok` and the specification `truncated` — which is the measurement that the bound in `WireAgrees` is load-bearing rather than decorative. Its one finding was
against my prose, and it is recorded above.

**How it closed is worth recording because the shape was not the one planned.** The plan's order was rows, then array arms, then dispatch, then induction — and it was wrong: four of the forty element rows
are *container* rows, so the element decision cannot be discharged before the value law, and the two are one mutual induction. The sitting proved `wireInvariant : ∀ n, WireAgreesUpTo n ∧ ElementsDecideBelow n`
by `Nat.rec` and read three corollaries off it, so **every named hypothesis about the readers is discharged rather than carried** — which is the distinction the acceptance turned on. The dispatch is by
*membership in the forty octets*, sweep-certified against the reference's own `assignedConstructor` test, rather than the `split at H` device the previous sitting's note designed: a completeness certificate
is stronger than an enumeration of the 216 negations the catch-all would have left, and the forty arms were untouched by the substitution. **Both departures were reported rather than taken**, and both were
better than the instruction they departed from.

**Amended twice: the receive hypothesis was refuted and is now fixed, and one instance's consequent is false rather than its hypothesis.** The first amendment below stands as history — it is why the parity order is what it is today. The second: the divergence it records was decided, both artefacts were aligned (`fd9bdc5`), and the same witness now draws the same class from both, so `ValueLayersAgree` is **undecided** — no known divergence, and no proof either, since discharging it needs the value layer's own instance. Separately, `Conforms specFrameSend refFrameSend` is **false** for a reachable array body whose refusal the two artefacts name differently, which is patch 3's `arrayElement` split; that is a false consequent rather than a false hypothesis, which is why it is a defect and not a condition. A value-layer slice set out to discharge the three hypotheses these instances rest on and found all three false at concrete witnesses, confirmed by running both artefacts. The receive instance's `ValueLayersAgree` fails on a map whose count field is odd: `Spec` tests the count's parity *before* reading items, the reference reads items, compares the declared size and then pairs them — so the same buffer is refused with `malformed` by one artefact and `sizeMismatch` by the other. That is a divergence of **reason class**, which is part of the observable: this section's `Output` carries the refusal and the corpus compares the class, so `Conforms specFrame refFrame` is false as an unconditional statement. It is reachable at the frame layer — a 14-octet frame whose body region is that buffer gives the two readers different classes and therefore different output lists, so no relation witnesses the instance at all.

`ValueWriterAgree` fails in two families, and one of them is reachable *through the corpus vocabulary*: an array whose element does not fit its declared element constructor gives one artefact `unassigned` and the other `limit`, which refutes the send instance the same way. And `ReadersAgree` is a frame-layer hypothesis, so the connection instance falls to the same witness.

**So the acceptance paragraph above is amended rather than withdrawn.** Each instance is *proved* — the proofs are real, the relation is load-bearing under both mutations, and the composition is honest — and each is **conditional on a premise now known to be false**, which makes the theorem true and empty. That is precisely what a corpus cannot tell us: the divergent buffers are not in it, and the theorem quantifies over the whole domain. **The defect the corpus could not find, the proof found**, and that is the argument for having a relation rather than a corpus, arriving as a defect instead of a confirmation.

**The value layer's three claims, stated, with the writer's domain decided.** These are the target for the slice that
proves them; the Lean statements live in `Proofs/FrameConformance.lean` and `Proofs/FrameSendConformance.lean`, and this
paragraph records the shape and the decisions rather than restating them, because a statement copied into prose drifts
and the module is what a proof is checked against.

* `ValueLayersAgree`, the receive direction: on a reference success, the same region decodes to a body the specification's
  reader also produces with the same octet count, and what the two bodies *are* is compared separately by the layer's own
  relation; on a reference refusal, a specification refusal whose reason class is the same. Both comparisons are between
  data the two artefacts carry — a count, an equality of declared types, and two `String` **fields**, the reference's from a
  `DecodeError` variant and the specification's from `Refusal.reasonClass` — so no `splitOn` survives in it. That matters
  because it was the whole of the obstruction: the statement could not be quantified over classes while it quantified over
  sentences. It is falsifiable by history rather than by argument: `#[0xC1,0x03,0x01,0x40]` refuted it before
  `Ref.Value.readMap`'s parity guard moved, and each conjunct's premise sits on the reference's answer, so no combination of
  specification and reference outcomes escapes it — the defect `AnswersMatch` once had. A search that finds no divergence
  over 114,225 buffers is evidence, not a shape that no witness could refute.
* `ValueCarrierAgree`, the corpus vocabulary: a JSON value the reference's carrier accepts is one the specification's accepts,
  with the layer's relation between the bodies. No classes, no wire, one claim, and it is the one hypothesis in the layer with
  no evidence against it. It is also the most tractable, so it is first.
* `ValueCarrierAgree`, calibrated against a scratch development that must not land: **the two carriers dispatch in different clause orders**, so
  the lockstep cannot be one `split`. The clause sets are identical and the orders are not — one lists `float, double, decimal32, decimal64,
  decimal128, char, timestamp, uuid` where the other lists `char, timestamp, float, double, decimal32, decimal64, decimal128, uuid` — so a single
  `split` pairs `float` with `char` and every later branch is matched against the wrong clause. The proof cases the *reference's* dispatch, whose
  `split at h` carries each branch's discriminant equality, and rewrites that discriminant into the specification's match: mechanical, one per
  branch, and twenty-five branches of plumbing before any clause is proved. The compound clauses differ in the *order of reading* as well — the
  specification reads `items` before `constructor`, the reference the reverse — so they need the reads re-ordered around a shared `Json` rather
  than matched step for step. That two independently authored carriers agree on the clause set and disagree on its order is a fact about the
  artefacts rather than a defect, and it is **invisible to the differential by construction**, since the same clauses in another order give the
  same answers; a proof obstacle no test here could surface is what this paragraph is for. What is calibrated and working: the fuel induction,
  with the item-loop lemma proved inside the `succ` step against the induction hypothesis over `List.mapM` of the corpus vocabulary (using
  `exists_of_bind_ok` from `ReadProgress`, and a `dsimp` after each extraction because `mapM_cons` leaves the continuation as an unreduced match
  on the pair), and the trivial clauses — null, boolean, string, symbol, binary — which close in two or three lines each once their discriminants
  are rewritten. What remains is the bulk: twenty integer branches needing the round-trip lemmas at the bounds `unsignedOf`, `signedOf` and
  `boundedField` establish, the compound clauses needing list and pair versions of the item lemma, and the four locksteps whose reads are
  ordered differently. Several hours of branch-by-branch proof, not a finishing pass.

* `ValueWriterAgree`, the send direction: **restated over the reader-reachable domain.** The body of an endpoint can only come
  from a reader — the wire is the only source of values — so a body no reader can produce cannot be sent by a conforming peer
  nor arise in the implementation answering one, and the ill-width family that refuted the unrestricted statement is a
  property of a permissive writer over values no protocol path constructs. The narrowing is stated at the statement and in the
  caveat with its witness, because a narrowed hypothesis with an unexplained narrowing is a defect wearing a domain.

**The affordance, stated narrowly, and the theorem that will be true and then false.** "Class the reference's writer" is
narrower than it sounds: the change is that `Ref.encode` answers with a *classed* failure the way `Spec.Codec.encodeValue` now does.
**`Ref.decode` needs nothing**, because `Ref.DecodeError` already carries the class as a variant — which is why the receive
direction's comparisons became statable the moment the specification's class became a field, and why the two directions have stood
in different states all along. One change to one function does two things: `ValueWriterAgree`'s class-agreement conjunct becomes a
candidate theorem rather than a prose comparison, and the endpoint's negation becomes expressible.

**And when it lands, that negation will be true in fact for a while.** With the array family already aligned by patch 3, the
reference's writer classed and the specification's classes unchanged, `¬ Conforms specFrameSend refFrameSend` is provable at the
moment the class exists — and it goes false the day the two writers' classes align. That is the withdrawal rule waiting to be
applied rather than a trap: a refutation of a defect that is about to be fixed, whose whole job is to be the record of the state
before the fix. Landing it without saying so would leave the next reader a theorem that argues for a world the next commit changes.

**The carrier route is validated end-to-end, and it is better than this paragraph's estimate.** `Proofs/ValueCarrierAgreement.lean`
carries the route with three of twenty-five clauses proved — null, boolean, string — and the shape for the rest. The key step is not a
`split`: with the discriminant as a *hypothesis*, `simp only [hk] at h ⊢` reduces **both** readers' `match kind with` trees to the
clause for that kind in one move, so the two clause orders never need reconciling at all. The dispatcher carries the ordering
question once, and each clause is three lines of plumbing plus its own reads. The estimate above — "twenty-five branches of plumbing
before any clause is proved" — is superseded by that measurement: the plumbing is one move, made once. What the module's header
records because the next person hits them first: `BodiesAgree` is a recursive `Prop` and does not reduce to `True` definitionally, so
its obligations need `simp only [BodiesAgree]` and `trivial` does not typecheck there; and a clause's shared reads are `cases` on the
`Json` accessor with the reference's success deciding each branch. Remaining and named: nineteen scalar clauses, the integer families
needing round-trip lemmas at the bounds `unsignedOf`, `signedOf` and `boundedField` establish, and four compound clauses needing
recursion at the fuel the reader hands down — `List.mapM` for items and a pair-level analogue for a map.

**Three environment facts the signed route established, each worth the next run's minute.** `norm_num` and `ring` are Mathlib tactics
and are **not available** in this module's import closure; `decide` and `omega` are the replacements, and reaching for the familiar one
produces an error that reads like a broken proof rather than a missing import. `BodiesAgree`'s signed case compares the specification's
`Int` on the *left*, so the round trip enters at `.symm` — the same orientation detail as the unsigned widths, and the reason the
second encounter cost nothing. And an unused `simp only` argument is **dropped rather than suppressed**: nine went that way with the
batch that took the proof to twenty of twenty-five, and the modules build with no lint notes at all. Progress at that point: twenty of
twenty-five clauses, with `char` next through its accessor bridge (`Nat` against `Int`, a JSON accessor lemma before any arithmetic),
then the four compounds, the fuel-64 join, and the determinism development.

**Two shapes the carrier's middle taught, both worth the next run's first minute.** The six octet payloads are **not equal functions**
on the two sides: the specification's `hexPayloadOf` and the reference's `fixedHex` perform the same reads and the same width check and
differ in their failure *text*, so they relate one-directionally on the success path (`fixedHex_ok_hexPayloadOf`) rather than by equality
as the unsigned pair does. That difference is invisible to every test here — the corpus compares classes and the classes agree — so it
would surface only in a proof that stated the two as equal functions, and it would surface looking like an arithmetic error. That two
independently authored implementations are *allowed* to differ in wording is the point of having two. And the bridge must enter as a
*local hypothesis*: `simp only` takes identifiers rather than applied terms, so an applied lemma silently does not fire.

**The statement is at fuel 64, not quantifier-general** — and that is the carrier's own bound rather than an accident, so it should
stay: the claim is an implication *from the reference's success at that fuel*, which means a value deeper than the bound is rejected by
the carrier and falls outside the domain rather than counting against the statement. Generalising the quantifier would state something
no test here asks for and no proof here needs. and the clause lemmas are proved at `valueOfJson (fuel + 1)` with the
discriminant as a hypothesis — so discharging it needs a join that is plumbing rather than mathematics: the twenty-five-way dispatch on
the kind, the extraction of the discriminant equality from the reference's own success, and the fuel instantiation at 63. Worth knowing
at the start of the remaining clauses rather than at the end of the last one, which is why it is recorded here at fifteen of twenty-five.

Remaining and routed in the module's header: the signed widths (`BitVec.toInt_ofNat'` then `Int.bmod_eq_iff` against the range
`signedOf` carries), `char`, whose disagreement with the reference is in the *accessor* rather than the arithmetic — `Nat` against `Int`,
a bridge before any proof — and the four compounds.

**A species, now with three instances: two artefacts can agree on behaviour and differ in a dimension the corpus measures nothing about.**
The third is `char`, and it is the sharpest because its dimension is not merely unmeasured but **inexpressible**. The specification reads a
code point as a JSON *natural* (`codePointOf json` is `getObjValAs? Nat "codepoint"` plus a `≤ 1114111` check); the reference reads it as a
JSON *integer* (`boundedField json "codepoint" 0 1114111`, which is `getObjValAs? Int "codepoint"` plus the same check). No vector can write
an integer where a natural is expected — the corpus is JSON text, and `65` is a natural — so **no differential over the corpus could ever see
this.** It is therefore a difference on an input the corpus cannot express rather than a conformance gap, and what it blocks is a *proof*:
the `char` clause needs an accessor bridge,

```lean
theorem getObjValAs_nat_of_int (json : Json) (key : String) (i : Int) (h0 : 0 ≤ i)
    (h : json.getObjValAs? Int key = .ok i) : json.getObjValAs? Nat key = .ok i.toNat
```

which through the instances (`FromJson Nat := ⟨Json.getNat?⟩`, `FromJson Int := ⟨Json.getInt?⟩`) reduces to the number layer — from
`n.toInt? = some i` and `0 ≤ i`, `n.toNat? = some i.toNat` for `n : JsonNumber`, in `Lean/Data/Json/Basic.lean` — a relationship that is not
in this repository's imports. So `char` is blocked on the JSON layer rather than on the standard, and the block is an hour of case analysis
rather than a gap.

The other two instances of the species are the `float`/`double` failure *text* and the two dispatchers' clause *orders*. All three belong in
one place because they are the differential's own blind spots stated in advance: **the corpus compares verdicts and classes, so it is silent
on wording, on order, and on a JSON number's type.** A downstream implementation should read that boundary before trusting a green corpus,
and the proof is where the boundary becomes visible — which is the argument for a proof existing beside a test suite rather than instead of
one.

**Twenty-four of twenty-five, and the join is *assembly* rather than construction.** `char`'s bridge was plumbing as predicted: both
accessors reduce to the same structural form — a mantissa and a zero exponent — so the lemma is a case analysis on the number, and the
negative-mantissa branch dies on the very hypothesis the reference's own range check carries. What is left is `map`, the same species with
a different subject: the specification reads the pairs array as `Array (Array Json)` where the reference reads `Array Json` and then a
`getArr?` per element, so it needs that bridge plus the pair-level analogue of `mapM_valueOfJson_agrees` with `BodiesAgreePairs` as its
obligation. Still nothing about AMQP itself is missing, which is now a fair summary of the whole remaining development: the difficulty was
never the protocol.

**And the fuel-64 join is smaller than the estimate that put it here**, for a reason worth stating: the compound clauses are already
stated with the induction hypothesis as a *parameter*, so they **are** the step lemma's own compound cases, and what remains is assembly —
derive the discriminant from the reference's own success, dispatch on it, and call the clause. That is the second time in this development
that re-reading a *statement* shortened the work rather than the proof of it, the fuel-64 observation being the first.

The bridges landed along the way are reusable and named: `unsignedOf_eq`/`signedOf_eq`, `unsignedOf_le`/`signedOf_range`/`boundedField_range`/
`boundedField_ok_getObjValAs`, the eight integer round trips `uN_toNat`/`iN_toInt`, `fixedHex_ok_hexPayloadOf`, `mapM_valueOfJson_agrees`,
and the two JSON accessor lemmas. The wire-level statements will want several of them.

**The hand-over at twenty-four of twenty-five, and what the proof surfaced that nothing else could.** Everything left in this
hypothesis is either *assembly* or a *JSON-layer lemma*: the AMQP content of the twenty-five clauses is done. `map`, the last clause,
reduced under *reading* rather than recall — `Array.fromJson? (α := Array β)` is `| .arr a => a.mapM (fromJson? (α := β))` and the element
instance for `Json` is the identity, so the reference's outer read already *is* the specification's read at the elements and the only
difference is that the specification parses each element as an array. The bridge is that list-level relation composed with `Json.getArr?`;
behind it, `map`'s case work is the pair accord with `BodiesAgreePairs` and nothing about JSON. The join's pieces are all present:
`ValueCarrierAgrees` as the formulation, `valueCarrierAgrees_zero` as the vacuous base, `valueCarrierAgree_of_agrees` as the contract's
statement at fuel 64, the scalar clauses taking the discriminant as a parameter, and `list`/`array`/`described` taking the induction
hypothesis — so what remains is to derive the discriminant from the reference's own success, dispatch, and call the clause.

**Three places where the two artefacts' *checks* already meet, which is a fact about how they were written.** The unsigned and signed
bounds (`unsignedOf`/`signedOf`), the code-point bound, and the timestamp range that supplies the JSON bridge's non-negativity: at each,
what the coverage needed was exactly what the two implementations already assert, so the proof's work collapsed from reasoning to reading.
**That is the kind of thing only a proof can surface** — a corpus measures behaviour, and this is a fact about the *shape* of two
independently written implementations converging where the artifact constrains them. It is also the programme's own claim arriving as a
measurement rather than an argument: the differential compares verdicts, and the *reason* they agree at these three points is a
coincidence of authorship that no verdict could show.

**What each instance loses, and when — the discharge map, stated where someone looking for it will find it.**
`frame_conformance_public (valueAgreement : ValueLayersAgree)` loses its hypothesis when the **wire-reading** development is proved, which
is the receive-direction agreement this section describes. `frame_send_conformance_public (carriers : ValueCarrierAgree)
(writers : ValueWriterAgree)` loses them **one at a time**: **`carriers` is discharged** — `valueCarrierAgree_all` supplies it, the theorem no
longer takes it as a parameter, and the statement did not move to meet the proof — and `writers` remains, once
the writer law is proved over `CarrierReachable`. The connection instance's `ReadersAgree` follows the receive direction, and `EndpointConforms` (R3)
sits above all of them.

**And `ValueWriterAgree`'s domain restriction is load-bearing — it must not be strengthened back.** Its unrestricted form was *refuted* at
the float-empty witnesses; the theorem was withdrawn when the narrowing landed, because a refutation whose subject no longer exists is not a
theorem, but **the witnesses remain in `Proofs/ValueLayerLaws.lean`** with prose saying what they show and why they sit outside the domain.
A reader who tidies the restriction away re-creates a hypothesis already known to be false, and the proof that follows would be a proof of
something untrue rather than a failure — which is the one outcome this repository's evidence design exists to prevent.

**And the same shape has now appeared twice, which is worth more than either instance.** The wire-agreement module's fuel law was landed as `∀ fuel, ∀ cursors` and is *false* as stated — refuted by the array element
loop, where the specification spends two extra fuel entering its element loop (`readArrayData f → readElements (f-1) → readElementsLoop (f-2)`) and the reference spends none (`readElements f → readElement f`), so the
two readers agree at every fuel only where the fuel is tied to the octets left at the cursor, with the witness `WireAgrees 2` failing on an array8 whose count is zero. **The lesson both instances teach is that a law
quantified over everything a reader can reach is not a stronger version of the law a contract needs: it is a different law, and a false one.** In both cases the repair is a restriction to the reader-reachable domain,
in both cases the restriction is *proved* or *witnessed* rather than assumed, and in both cases the contract was unaffected — which is what makes them findings about the specification rather than admissions about proofs.

**The remaining development, as a brief — the analysis is complete and only the window is missing.** ImplCore read the module, both
readers' `map` branches and the JSON instance layer, verified the instance facts the proof turns on, and landed **nothing**: the work is
multi-iteration, so it belongs outside the tree until it elaborates, which is the window rule applied without being asked twice. What it
established, for whoever holds the window:

* **The bridge's statement.** Both readers parse the same `.arr` payload and differ only in how far they parse it in place.
  `Json.getObjValAs? j α k = fromJson? (j.getObjValD k)` (`Basic.lean:275`); the instance for `Json` is the identity (`:79`); and
  `Array.fromJson? [FromJson α] : Json → Except String (Array α)` is `| .arr a => a.mapM fromJson?` (`:111–116`). So on a `.arr raw` the
  specification's `getObjValAs? (Array (Array Json)) "pairs"` is `raw.mapM (fun e => match e with | .arr b => b.mapM Except.ok | x => .error …)`,
  while the reference's `getObjValAs? (Array Json) "pairs"` is `.ok raw` with `getArr?` called per element at the point of use. The lemma to
  state is therefore: for `j : Json` and `a : Array (Array Json)`, from `Array.fromJson? (α := Array Json) j = .ok a` derive
  `∃ raw, Array.fromJson? (α := Json) j = .ok raw ∧ raw.toList.mapM (fun e => e.getArr?) = .ok a.toList ∧ raw.toList = a.toList.map Json.arr`
  — an induction over the array with `mapM` on both sides, and the `Except.ok` analogue of `List.mapM_some` is what collapses the identity
  instance (`#check` it in the pinned shell; a bare `lean` cannot see the library, which is a limit one probe of this session hit and reported).
* **`map`'s clause** mirrors `carrier_clause_list`/`carrier_clause_array`, with a pair-level analogue of `mapM_valueOfJson_agrees` whose
  obligation is `BodiesAgreePairs` (`FrameSendConformance.lean:164`). The pair accord is AMQP content; the array parsing is the bridge.
* **The step lemma and the join**: `ValueCarrierAgrees fuel → ValueCarrierAgrees (fuel + 1)` by unfolding the reference's reader, `cases hk`
  on the discriminant out of the reference's own *success*, then `match hkind` over the twenty-five literals with each branch calling its
  clause by `rw [hk, hkind]` and the compound four also passing `ih` — the default branch closes because the reference's own dispatch errors
  there. Then `∀ fuel, ValueCarrierAgrees fuel` by `Nat.rec`, and `ValueCarrierAgree` follows, since it *is* `ValueCarrierAgrees 64`
  (`FrameSendConformance.lean:204` against `ValueCarrierAgreement.lean:802`).
* **Estimate**: roughly 200 lines in four pieces with a normal number of build iterations — a development window, not an open question.
* **And it is the fourth instance of the species above**: the specification parses a pair as a nested array where the reference parses lazily
  and calls `getArr?` at the point of use. Both accept the same JSON, so no differential sees it — which is why the bridge has to be a proof
  and not a vector.

**The `map` bridge landed (`895ca90`), and the remaining obstacle is two laws the core does not carry.** The bridge is in the tree with the
module green: the `FromJson` identity instance made explicit, what each reader does with an array payload, the element-level bridge in both
directions, the list-level lemma with `l = a.map Json.arr` recorded, and `mapM_getArr?_collapse` turning the reference's `mapM` over raw
elements into a parse of the pairs plus a read of the parsed pairs — which is the shape the pair accord is stated against. What remains is
that accord's *specification* side, which is two-stage where the reference's is one, and associating them needs `Except.bind_assoc` and
`List.mapM_bind`. **Neither is in core**: `Except.bind_assoc`, `Except.bind_pure` and `Except.pure_bind` are all unknown constants, and each
is one `cases a <;> rfl` from being available. The cons case of `List.mapM_bind` needs all of them plus `List.mapM_cons`.

**And a trap worth the paragraph: `simp` cannot reduce an `Except` bind at all.** Minimal and verbatim, from the slice's own probe:
`example (f : Nat → Except String Nat) (b : Nat) (h : (Except.error "x" >>= f) = Except.ok b) : False := by simp at h` gives
"`simp` made no progress", and `simp [Except.bind]` reports the argument unused. Every earlier `simp … at h` that failed in this development
failed for that reason rather than for want of the right hypothesis — which is the difference between a dead end and a known property of the
environment, and the reason it is recorded rather than remembered.

**A plausible law that is false, caught by testing it rather than by assuming it.** `List.mapM_bind` —
`(l.mapM f >>= fun xs => xs.mapM g) = l.mapM (fun a => f a >>= g)` — does **not** hold for `Except String`, and using it to collapse the
specification's two-stage read into the one-stage form would have produced a *false* lemma. `Except` short-circuits with a message, so the
two-stage form runs every first-stage read before any second-stage read while the one-stage form interleaves them, and the two report
**different failures**: verified by `rfl` on `[1, 2]`, the two-stage form gives `error "two"` and the one-stage form `error "g"`. The law was
reached for because it is what such a collapse *looks* like it needs; what made the discovery safe was that the attempt was to *prove* it —
**a plausible law whose proof fails is a signal to test it, not to add it to a simp set.**

**What is true, and the route that follows.** `Except.bind_assoc` (`cases a <;> rfl`), `Except.pure_bind` (`rfl`) and `Except.bind_pure`
(`cases a <;> rfl`), none of them in core; and `bind_assoc` is what makes the collapse work, because it *rewrites one computation into an
equal one* rather than *reordering two independent ones* — the difference between reassociation and commutation, and the reason one is true
and the other cannot be. So the accord stays stated over the specification's **two-stage** read, which is the reader's actual shape: the
*value* has to agree, not the term. In the cons step, with `split pair = Except.ok (key, value)` from `hpairs`, the specification's side is
`(rest.mapM split) >>= fun v => ((key, value) :: v).mapM R`; `mapM_cons` and `pure_bind` turn the head's reads into
`Except.ok (bodyKey, bodyValue)` from `hbodyKey`/`hbodyValue`; then **one** `bind_assoc` in the direction
`(X >>= A) >>= F = X >>= fun ps => A ps >>= F` lands exactly on the induction hypothesis `hbodies'`. The slice's own diagnosis of its
earlier attempts is the other half: unfolding `mapM_cons` in the goal loses the do-shape the hypothesis is stated in, so the step stays in
bind form and reassociates. Caution recorded with it: `bind_assoc` in a `simp` set can loop, so it may need to be a directed `rw`.

**And a second environment fact from the same development, quoted rather than paraphrased**: *"`cases x : t` rewrites the goal but not a
hypothesis."* The equation form of `cases` generalises the scrutinee in the goal and hands back a hypothesis naming the case; hypotheses
that mention the scrutinee are not rewritten with it, so a step that expects the hypothesis to follow along needs the rewrite applied
there explicitly. Together with the `Except`-bind fact above, these are the two places where the development's failures looked like proof
difficulties and were properties of the environment.

**The carrier's clause family is complete — twenty-five of twenty-five — and the last one needed the corrected route.** `map` landed with the accord kept
over the specification's **two-stage** read, which is exactly what the false `List.mapM_bind` forced: the one-stage collapse would have reported a different
failure for the same input. What remains is the join — the step lemma and the fuel induction — drafted and compiling against the module.

**And the two environment facts recorded from ImplCore's development were both used in proving it**: peeling rather than casing, per the `cases x : t` note,
and `show` to fix a goal's spelling where `simp` cannot reduce an `Except` bind at all. That is the first time a trap written into this plan visibly saved
someone else's hour rather than its author's, and it is the only argument for writing them down that survives contact with a busy day.

**There is no bridge to build for the receive direction, and the reason is an asymmetry between the two implementations.** The frame layer needed
`beAt_eq`/`ofCode_none_iff` because it names two dispatchers; the value layer names one. The specification dispatches through `classify` and the
generated tables, while the reference **matches the constructor octet inline in its own `readValue`** with no table object anywhere — so the per-octet
correspondence **is** the branch lemma rather than a lemma ahead of it. What the tables do give is cheap resolution of their own side, measured rather
than assumed: `(dataDecl 0x40).map (fun d => (d.width, d.owner)) = .ok (0, "null")`, `classify 0x40 = .fixed 0` and `(dataDecl 0x01).isOk = false` all
close by ordinary `decide`, with **`native_decide` kept out** and the trust base unchanged.

So the receive direction is a second *application* of the clause-family method, and its branches are an ordered finite list rather than an open
question: `wireDescribed` (0x00, the only scalar-ish branch that takes the induction hypothesis twice), the four scalar categories (fixed 0/1/2/4/8/16
and variable 1/4, closing against the literal with the table lookup decided), compound `list`/`map` (recursion at the fuel beneath, with `CursorAgrees`
carried through the item loop), then `array` — whose count and limit branch is where the specification's `limit` class must meet the reference's — and
last the fuel induction with the entry-point reconciliation, which is free because both entry points call `readValue bytes.size` at `⟨bytes, 0⟩`.

**And the rule that stopped being needed is worth one line**: the reconnaissance had concluded the bridge "belongs before any branch"; the measurement
dissolved it, so what belongs first is `wireDescribed`. That is the third time in this development that reading the code removed work the plan had
assumed — after the fuel instantiation and the view — and it is the argument for reconnoitring before committing to a shape.

**A fourth reduction from reading the code, and the pattern it completes.** `wireDescribed`'s view lemma does not need the table bridge the reconnaissance
expected: both readers run `find?` over the **same generated table** — `Spec/Frame.lean:76` and `Ref/Frame.lean:39` both opening
`SpecAMQP.Generated.Oasis (TypeDecl types)` — so the descriptors are compared against one table with a representational difference inside the predicate
(`code` against `code.toNat`), which is the same `BodiesAgree` obligation one level down rather than a new one. What the branch does need is the *route*
strengthened: a `.described` body's view is its descriptor's type, so agreeing on views is not enough, and the success conjunct therefore carries
`BodiesAgree body other`, from which the contract's view equality is derived. **The contract's statement keeps its own spelling** — the strengthening is how
it is proved, and the reasoning lives in the module's header rather than in a commit message.

**Four reductions now, all from reading rather than from proving**: the fuel reconciliation that was free because both entry points start at the same cursor;
the dispatch bridge that dissolved into the branches because only one side names a dispatcher; the table lookups that decide; and the descriptor tables that
turned out to be one table. The lesson they share is worth stating once — **the two artefacts agree more often than the plan expects, and where they differ
the difference is representational rather than semantic** — with its bound attached: both artefacts are readings of one artifact, so their agreement checks our
*transcription* of it rather than the artifact itself. It is evidence about the two implementations converging, not about the standard.

**A fourth environment fact, and it is a resource rather than a tactic**: a naive `cases d <;> cases d' <;> simp` over the 25×25 product of descriptor
constructors **exceeds the heartbeat budget** in this repository's arithmetic-free case analysis, so a pattern-dispatched closer is the right shape from the
start rather than the thing one reaches for after a timeout. The predicate licenses it: `typeOfDescriptor` discriminates only `ulong` and `symbol`, so a
three-way split per side — those two plus a catch-all for the other twenty-three — is nine cases rather than six hundred and twenty-five, and where the
patterns reduce, rewriting the representational equality in makes the two sides syntactically equal and `rfl` closes them.

**And a relation arrived from the other direction, which is the strongest evidence yet that the value layer's structure is the artifact's.** `BodiesAgree` is
already the corpus side's correspondence between the two value types, and it is *exactly* what the wire route's described branch needs — so the contract's view
lemma is a **corollary of a relation that existed** rather than a definition invented to make the wire work. Together with the shared generated table, the four
reductions and the three places where the two artefacts' own checks already meet, that is a consistent picture: where two independent readings converge, they
converge at what the standard constrains.

**Two more measurements, one of them a refinement of the heartbeat fact above.** The wall is **per-invocation rather than cumulative**: 625 goals with a
targeted `simp only` chain close in about ten seconds, while a single `simp` over the full product times out. That turns "pattern dispatch rather than search"
from a preference into a **cost model** — a fixed term per goal is cheap at any count, and a search is expensive at one — which is the form a reader can plan
against.

**And the `match` prologue is the shape that looks natural and does not work.** `match d, d' with | .ulong a, .ulong b => … | _ => cases d <;> cases d'`
abstracts the values, so `cases` then acts on names the goal no longer mentions and the wildcard fails with the values still symbolic. The case-driven form —
no `match`, `cases` from the start, the interesting cases falling out of the same blast — closes 623 of the 625. Recorded because the failing form reads more
cleanly than the working one.

**And the two goals the blast leaves are closed by entering a binder rather than by a law.** With `h : n¹ = n.toNat`, the goal is an equality of two `find?`
applications whose predicates carry the payload under a lambda, so `rw [h]` has nothing at the top level to fire on and `simp only [h]` does not reach under
the binder either. The route is `congr 1`, `funext entry`, `rw [h]` — two lines, and the shared table is what makes the result an *identity* rather than an
argument about a table.

**The receive direction's state, handed on read-down rather than assumed-up.** The corpus-vocabulary hypothesis is discharged as a theorem at the library axiom set — which is
what let the frame send instance drop its `carriers` parameter, the first line of the discharge map to clear — and the receive direction is left green with its shape *read* rather
than assumed: no fuel reconciliation, because both entry points start at the same cursor; no dispatch bridge, because only one side names a dispatcher; one shared descriptor table;
a view weaker than body equality; and a finite ordered branch list. `bodyView_of_BodiesAgree` is two goals from done, and both are closed by entering the `find?` predicate's
binder (`congr 1`, `funext entry`, `rw [h]`) rather than by a law.

**And the writer hypothesis has a one-line status worth keeping verbatim**: **false unrestricted, restated with the domain that makes it true, its class still prose on the
reference's side.** That last clause is the single change that would make the send instance's law a candidate theorem *and* the endpoint's refutation expressible, which is why it
sits alone at the end of the queue rather than beside the branches.

**What discharging the hypotheses would take, in order, so the next sitting does not rediscover the shape.** The refutations stand as theorems either way — a refuted hypothesis is a theorem or it is a rumour. Then: **(i)** decide the reading for each divergence, which needs the artifact's own text — for the odd-counted map, whether the count names items or entries and whether the *form* of the count is checked before or after its consistency with the octets. Where the artifact is silent, a register entry decides it, which is what the register is for. **(ii)** Align the two artefacts to that reading, one commit per divergence, since each is symmetric in a different place. **(iii)** Add a vector per divergence, because *reachability* is what decides whether the corpus could ever have seen it: the array-element family is reachable through the corpus vocabulary and the odd-count map is not, and that difference is a fact about the corpus rather than about the defect. **(iv)** Only then are the hypotheses provable and the two conditional instances unconditional. **The order is the point**: a vector written last would be a vector written from the fix rather than from the artifact, which is the rule this repository keeps and exactly why the differential cannot be the thing that finds this class of defect.

**And a second divergence sits underneath the first, found by a sharper witness.** The reported buffer violated two rules at once — an odd count *and* a declared size inconsistent with its items — so it could not say which rule either artefact was answering. A buffer violating only parity, `#[0xC1, 0x03, 0x03, 0x40, 0x40, 0x40]` where the items measure exactly the declared three octets, gives `malformed` from the specification and `sizeMismatch "map" 3 4` from the reference: declared 3, **measured 4**. Four is what a map's content measures if the *count field is inside the size*, three if it is not — so the two artefact seem to differ about what a compound value's size field covers, which would change the class for every map and list rather than only the odd ones. The ledger's index yields the parity clause (`amqp:types/section:primitive-type-definitions/type:map.1`) and nothing on the size field's extent, so that question is open and is being settled from the artifact's prose. **It is the more important of the two**: a parity rule affects one malformed encoding, a size-accounting difference affects the whole corpus.

**And it is now localised: the divergence is the size accounting, not the parity rule.** Three buffers, one variable — the count is odd in all three and only the size field changes:

| size field | specification | reference |
|---|---|---|
| 3 (items alone) | `malformed` | `sizeMismatch "map" 3 4` |
| 4 (count + items) | `malformed` | `malformed` |
| 8 (neither) | `malformed` | `sizeMismatch "map" 8 4` |

**Where the size field agrees with the count field plus the items, the two artefacts agree** — both refuse with `malformed`, the class the parity clause implies. So the parity rule is not in dispute: the reference counts a compound value's count field *inside* its size while the specification counts the items alone.

**That also explains why `s1_differential.sh` is green, and it is the sharper lesson of the two.** The generated corpus's own odd-map vector has a size field of 6 against a one-octet count and five item octets — consistent under the reference's accounting — so it never reaches the divergence. **A corpus with one case per rule cannot see a defect that lives in a *parameter* of the case**, which is the argument for a boundary sweep rather than one vector per clause.

**Which accounting is right is a reading, and a strong candidate comes from the encoding's own purpose**: a receiver must be able to *skip* a value it does not understand, and it skips `size` octets from just after the size field. If the size did not cover the count field then the count octets would be left unconsumed and every skip would desynchronise — so the size almost certainly covers count plus elements, which would make the **reference** right and the specification's accounting wrong. The artifact does not settle it by citation: the ledger's index yields **no clause about compound values at all**, so the rule lives in the type table's labels rather than in a keyed statement, and the register is where it has to be decided. **The residual question is the order of the two checks** once the accounting is fixed: a buffer with an odd count and an inconsistent size violates both rules, and which class it reports is a second reading — on which the reference's size-first order is the safer one, since a receiver that cannot trust the declared size cannot safely enumerate items.

**Corrected, and the correction is mine to own: the accounting is *shared*, and the divergence is check precedence.** Two buffers with an **even** count — so the parity rule cannot mask anything — settle it from both sides:

| size field | specification | reference |
|---|---|---|
| 2 (items alone) | `sizeMismatch: a map declares 2 octet(s) after its size field and measures 3` | `sizeMismatch "map" 2 3` |
| 3 (count + items) | **admitted**, five octets consumed | **admitted**, five octets consumed |

Both refuse the first with the *same* class and the *same* arithmetic (2 declared against 3 measured = the count field plus two items), and both admit the second. So the two artefacts agree about what a compound value's size field covers, and the paragraph above — which says the reference counts the count field while the specification counts the items alone — was an inference from buffers that could not show it, because an odd count makes the specification answer on parity before any size opinion is observable.

**The real question is which condition a buffer that breaks two rules reports.** The reference checks the size first and the specification checks parity first, so the same buffer carries one class under one reading of "which rule wins" and another under the other; neither artefact is wrong about the arithmetic. **That is a narrower and better-posed reading question than the one recorded first**, and the traversability argument above no longer decides anything, since both readings traverse correctly.

**And the layer's own structure is now settled, in terms a reader can check.** The three hypotheses are **five claims and one relation**, not three under three names: `ValueLayersAgree` hides two — on a reference success, the same consumed count and a body the frame layer reads the same way; on a reference refusal, the same reason class — and `ValueWriterAgree` hides two more, octet equality where the reference writes and class agreement where it refuses, quantified over `BodiesAgree`, which is the layer's relation rather than a hypothesis. `ValueCarrierAgree`, the two corpus-vocabulary readers, is single and is the only one of the three with no evidence against it. The earlier reading of this section — "wire reading, corpus-vocabulary reading, writer law, body contents" — was right about the layer and wrong about the count, and it is corrected rather than annotated.

**One distinction from the connection layer is worth keeping**: `ValueLayersAgree` is **not** vacuous in one direction. A specification success against a reference refusal contradicts its first conjunct and a specification refusal against a reference success contradicts its second, so the two implications do not share a premise and the defect found in `AnswersMatch` — where both conjuncts had their premises on one side, leaving `spec = error` with `ref = ok` satisfiable by anything — does not repeat here. A reader who has met that finding will look for it in every conjunction, and this is the one place where the answer is visibly no.
 A corpus cannot decide it either — it can only make it visible — which is why the family `ImplShell` is building states the class where a single rule is violated and marks the class as a register question where two overlap.

**What follows is a fix in one of the two readings, not a proof revision**, since both artefacts *refuse* these buffers and differ only about which class names the refusal. The class is contractual — the driver's verdict vocabulary is built from it — so either one reading misreads the artifact, or the artifact is silent and the register must decide. Three pieces: a register entry, the smallest aligning patch, and the refutation theorems in `Proofs/`. The first two are mine; the third is the slice's, and a refuted hypothesis is a theorem or it is a rumour.

**And the implementation track is unaffected, which is worth stating because it is the natural thing to fear.** R3's relation is `Conforms specConn core` where the core is a *driver* over `Spec.Connection.step`: it shares the specification's decisions by construction and reads nothing. A divergence between two readings of the standard is a defect in a reading, and the endpoint does not read.

**And how much of the proof is doing work is measured rather than assumed.** Of the file's 69 `try`-guarded reductions, removing all of them produces exactly eleven errors — so eleven were dead weight and are deleted, while the other 58 reduce something and remain. That is the number a downstream reader wants when asking whether a proof of this size is load-bearing at the points it claims, and it exists because the author measured a claim they had first made in prose.

**And a defect the ledger batches found by reading, which no gate in this repository can see.** The artifact's two conditions on `transfer`'s `settled` field select *choices* of the
`sender-settle-mode` element — `<xref name="sender-settle-mode" choice="settled"/>` for "MUST be true on at least one transfer frame", `choice="unsettled"` for "MUST be false (or unset) on
every transfer frame" — and **both** artefacts read the element's *name* where each sentence selects a *choice*, so the flag that gates the obligation is computed from the opposite
negotiation. The inversion is invisible to every check here: the ledger renders the cross-reference as the element's name and so loses the choice, so the two sentences look identical; a
differential between the two artefacts reports agreement because both are wrong in the same direction; and the proofs are conditional on the flag the code computes. It was found by a
batch that read the rendered sentences as identical and went back to the artifact to see why they could be — which is the argument for a clause-by-clause ledger over a summary of what the
model happens to do: the summary would have said "settlement is handled", and been wrong in a way nothing could catch.

**The contract for it is stated as an equality, so it fails on the current code rather than describing it**: `Contracts/Settlement.lean`'s `SenderSettleModeIsTheChoiceTheClauseSelects`
requires the flag to equal the comparison against the `settled` choice, which the model cannot satisfy while it reads `unsettled`. A contract stated as the fix would be as good as the
mistake.

**And a contract's right-hand side can force the implementation's shape, which is worth knowing before it is discovered twice.** `SenderSettleModeIsTheChoiceTheClauseSelects` compares against the
*settled* choice's number as the artifact states it, and that number can only be *read* — a literal is forbidden in `lean/Contracts/` and `lean/Spec/` by the rules above — so the right-hand side
necessarily carries `choiceValue?` and `String.toNat?`. **The kernel cannot reduce those**: `String.toNat?` bottoms out in `ByteArray` primitives, so `rfl`, `decide` and `simp` all fail on them and
`native_decide` is banned by the trust gate. The response is neither to weaken the contract nor to add trust, but to write the *implementation* in the contract's own shape — the selection becomes one
expression whose successor field is definitionally the contract's right-hand side, the proof reduces to the do-block's case analysis, and every runtime branch is unchanged, which the slice argued branch by
branch rather than by sample. **A contract that states a selection as an equality makes the shape of that selection part of the contract**, and that is a reason to state it deliberately rather than a
reason to state it some other way.

**And the finding is sharper than "keyed backwards", as the ledger's own review established while confirming it independently against the XML rather than against the note.** Under `snd-settle-mode = unsettled`
the model demands what `.6` forbids, and under `snd-settle-mode = settled` the flag is false and the guard never fires, so `.4`'s obligation is **unenforced** as well as misapplied. **Three artefacts key it
the same wrong way** — the specification, the reference, and the corpus generator (`scripts/gen/slices.py`, writing `sender_settle=0` while labelling it `sender-settle-mode`) — so all three agree with each other
and disagree with the artifact's own choice attributes. That unanimity is exactly why no differential can see it, and why the defect had to be found by reading two clauses whose *rendered* text was identical
and going back to the source to ask why they could be.

**The settle-mode defect is fixed in all three artefacts at once, and the slice's evidence is the shape this repository asks for.** The selection now reads the *choice* the artifact names for each
sentence — `choiceValue? "sender-settle-mode" "settled"` in the specification, `declaredChoice … "settled"` in the reference, `choice_value(TRANSPORT, "sender-settle-mode", "settled")` in the corpus
generator — with the **proof attempted first** against the pre-fix model and observed failing on the inversion in a single line, and with a **two-directional control**: a scratch vector negotiating
the other choice is *admitted* by both artefacts, so the guard is shown to fire under `settled` and not to fire under `unsettled`, which is the defect gone in both directions rather than one.

**And the fix required reshaping the specification's own expression, which is what stating a selection as an equality costs.** `String.toNat?` is not kernel-reducible — `Slice.isNat` bottoms out in
`ByteArray` primitives — so `rfl`, `decide` and `simp` all fail on the contract's right-hand side while `native_decide` is banned by the trust gate. Writing the *implementation* in the contract's shape
makes the proof definitional and leaves every runtime branch unchanged, which the slice argued branch by branch rather than by sample. `Contracts/Settlement.lean`'s proposition is proved by
`Proofs.Settlement.senderSettleModeIsTheChoiceTheClauseSelects`; the ledger's `.4` and `.5` entries moved from `deferred:S4` to `formalized:` on that declaration and the refusal that applies it,
while `.6` stays deferred — its obligation is a safety over *every* transfer that the layer still does not check, and it is now *omitted* rather than *inverted*, which is a different sentence in the
ledger because it is a different fact.

**And the wire module's state is a map rather than an impression.** Three commits landed the foundation, the octet-step bridges, and the described branch with the zero-width and payload patterns —
**3 of 40 arms** — against a formulation that had to change: `WireAgrees fuel` as first landed quantified over *every* fuel a cursor can be paired with and is **false**, refuted by the array element
loop, where the specification spends one more fuel entering the loop than the reference spends entering its own, so the two align only where the fuel covers the octets left at the cursor. The law now
carries `c.data.size - c.pos ≤ fuel`, `StepAgrees` carries both conjuncts, and **the contract is untouched** because `ValueLayersAgree` only ever needs `readValue region.size ⟨region,0⟩`, where
`size - 0 ≤ size` holds free.

**And the evidence for the strengthened claim is a measurement rather than a proof obligation.** An entry-point differential of the two readers over **~313,000 buffers** — all buffers up to length 4
over a 26-octet alphabet, and up to length 6 over a 12-octet alphabet chosen for arrays, compounds and described values — reports **zero divergences** in shape, in reason class, in consumed count and,
for every success, in the body view. That is the target's own evidence that the bound is the true statement at the fuel the contract uses, and the two pieces of evidence do different jobs: the witness
says the law as written was *false*, the differential says the law as fixed is the one this contract *needed*.

**What remains is mapped by cost, which is what makes the next sitting mechanical — and the map was acted on.** The cheap group is **twenty-four** rows, not the twenty-three this section first
said: the union it enumerated double-counted `0x52`/`0x53` and never mentioned `0x56`, and the slice that implemented it landed the list rather than the numeral and reported the discrepancy instead of
resolving it silently. Those twenty-four and the seven signed rows are now **proved — 34 of 40 arms** — with the sign extension needing `Proofs.ValueCarrierAgreement`'s `i32_toInt`/`i64_toInt`, a
dependency the plan anticipated in substance but not in form. What is owed is one coherent unit rather than a list: the **six recursive arms** (`0xC0`, `0xC1`, `0xD0`, `0xD1`, `0xE0`, `0xF0`), the
**three loop relations** they share, the `split at H` dispatch, the `Nat.rec` induction and the entry point. The slice stopped at the arm boundary rather than landing the loop relations unattached,
on the ground that a relation with no arm using it is a declaration with no caller.

**And the arms proved a shape lesson worth carrying rather than rediscovering.** Two iterations were lost in one sitting to the same fact: **state a lemma at the shape the consumer has, not one step away
from it.** The two text families' bridge had to be stated at the *reader* level rather than as a step, because a step agreement hands its intermediate back as a component of a pair and re-pairing that
component produces a term equal to the reader's own only through `>>=`'s associativity — which is not a definitional equality, so no hypothesis can be checked against it. And the step stems take their
arguments as (steps, values, shapes, relations) rather than the obvious (step, relation, shapes), because a relation hypothesis whose right-hand side mentions the inner step through a projection cannot
be used to *infer* that step: it is not a higher-order pattern, so the shape has to be given first. Both are the same rule from different sides, and the module now records them where the next reader will
meet them.

**And the compound step found a second fuel fact, which is worth stating as an accounting difference before someone reads it as a divergence.** The reference's `readCompound` spends one fuel unit on its own
header — its match is on `fuel+1` — while the specification's `readValue` has already spent that unit by the time it reaches the item loop, so at one value-level fuel the two loops sit one apart and **the
offset compounds with nesting**: measured, `Ref.readItems 0 0` refuses where `Spec.readItems 1 0` accepts. No statement of the form `ref readItems j ↔ spec readItems j` is therefore provable, and the
three loop relations cannot be stated at a single fuel. **This is not a behavioural divergence** — the differential over 746,708 buffers answers identically at the fuel the contract uses, and the reason is
structural rather than lucky: the specification's dispatch is on `classify` and its four width cases are uniform in the row through `specElementData`, so there is no per-octet work for a fuel increment to
buy, while the reference spends its unit on a header the specification does not have. The route taken is therefore to prove **the specification's fuel irrelevant above the octet bound** — a theorem rather
than a hypothesis — which aligns the loops without re-proving the 34 landed arms at shifted pairs. It is the *third* instance of the shape this section has now recorded twice: a statement quantified wider
than its contract needs is not stronger but false, and the repair is a restriction to the domain the contract actually reaches. The route was implemented as far as its design and its tooling: the loop tooling landed green
(`a018180` — the unassigned-octet family, the element-constructor bridge, the reference's advances, `pairUp_agrees`, `specElementData` with its loop equation, the exhausted-cursor refusals), and the design
established four statement-level facts that are conditions on the *statement* rather than objections to the fact: the item loop's irrelevance is false from fuel zero to one at a zero count, the compound
reader's is false at fuel zero for a width-zero declaration the declared surface has no row for, every clause must carry the *buffer invariance* of its read because a loop's tail is read at a cursor the
item read advanced, and the specification's readers are one `mutual` block, so their unfoldings are the compiler's equations rather than iota — `unfold` or `cases` reduces them, not `rfl`.

**And the irrelevance is proved, so the fuel offset is closed at the level it was found** — `FuelIrrelevant`/`FuelIrrelevantUpTo` with `fuelIrrelevant_all`, and a corollary per reader
(`readValue_irrel`, `readItems_irrel`, `readCompound_irrel`, `readArrayData_irrel`, `specElementData_irrel`, `readElementsLoop_irrel`), resting on a six-clause buffer-invariance cluster
(`readRows_data`, the companion of `readValue_progress`) and on `AnswerAgrees`, which is the relation shape the loops need: an agreement on answers *and* classes, with its own `bind` composition
lemmas. The item loop then landed at one fuel on both sides (`ItemsAgree`, `readItems_loop`), and the compound body on the list rows (`readCompound_list_body`) — so four of the six recursive arms are
reduced to their octet step, their classify/table resolution and a call to that body. **The entry point is still not reached**, and the sitting recorded the two relations still outstanding — the map rows
and the array element loop's one-fuel offset — rather than reporting progress as proximity.

**And the whole suite is green with these proofs in it** — **19 of 19 contracts** on a tree carrying the R4 shell and comparator changes, the fuel-irrelevance family, the readers'
position invariance and 38 of the 40 arms. That matters for a reason beyond the number: every earlier sitting's work passed its own module build, and this is the first run that puts the wire module's proofs
through the *corpus* gates, the trust gate and the shell tiers together. **A proof that disturbs a gate is a proof about the wrong thing**, and the differential gates agreeing while the module's own claims
are still partial is the shape the section's evidence argument needs: the proofs are being built on a verified base rather than beside one.

**And a fourth constraint the plan did not anticipate, found by a statement that was false rather than unproved.** An element whose declared row is width zero reads nothing through
`takeBytes 0`, which succeeds exactly when the cursor is inside the buffer, and an array of zero-width values is read at exactly that cursor (`pos = size`) — so the element decision's statement is
**false** without `c.pos ≤ c.data.size`, and the loop has to carry the condition on. It is landed as the readers' position invariance (`readRows_le_size`, `specElementData_le`), and it is the fourth
instance of the shape this section now records three times: a law quantified over positions a reader cannot occupy is a different law and a false one, and the repair is a restriction to what the readers
actually reach, stated as a clause on the statement rather than as an assumption. **What remains is one hypothesis away from the contract**: the element decision's forty constructor rows are named
(`ElementsDecideAt`/`ElementsDecideBelow`) and taken as hypotheses by the loop and the array body, so the entry point must not be reached with them standing in for the rows — a version of
`ValueLayersAgree` conditional on them is a proof about a different proposition.

**And it declined to inherit a claim it could not check**: the previous sitting described the entry point as free once the loops compose, and this one says plainly that it did not verify that. **A handover
that carries an unverified claim forward is how a plan acquires facts nobody measured** — the same rule as the docstring that said the two readers spend the same fuel, one sitting later.

**And one finding refuted a second claim, in a docstring rather than a law.** `WireAgrees`'s own rationale said the two readers "spend the same fuel per value, per compound item and per array element", which
the compound rows refute; the docstring now carries the witness beside the bound it explains. **A rationale is a claim like any other and decays the same way** — this is the same lesson as the plan text
that described landed work as owed and the note that said the model was keyed wrongly, arriving this time inside a proof module, where the temptation is to read prose as commentary rather than assertion.

**And the writer law turned out to be *refutable*, by a witness the classing itself made expressible.** `Ref.encode (Ref.Value.array 0x57 [])` returns `#[0xE0,0x02,0x00,0x57]` — an array
whose declared constructor `0x57` is unassigned — while `Spec.Codec.encodeValue (.array 0x57 [])` refuses, and, decisively, **`Ref.decode` refuses the octets `Ref.encode` wrote**. That is the reference
disagreeing with *itself* rather than with the specification: `Ref.arrayElementItems` never consults the declared constructor when the element list is **empty**, so `arrayElement`'s catch-all — the arm
that names `unassigned` for the non-empty case, and the arm patch 3 split — is never reached. `.array 0x57 [.null]` refuses correctly today; `.array 0x57 []` does not.

**And the affordance did exactly what the paragraph above predicted, which is the part worth noticing.** Classing the writer fixed nothing: it made an existing defect **expressible**, turning a divergence
invisible to every gate into a theorem with a witness. The law's statement is being replaced (its error side classed), the reference's array arm is being fixed to consult its declared constructor before its
elements — the same shape as `elementDecl?` and patch 3 — and the refutation lands as the record of the state *before* the fix and is then replaced by the proof, with the witness kept in prose, because a
refutation of a defect that has been fixed argues for a world a later commit changed.

**And the writer law's second cycle closed by removing the hole rather than the refutation.** `ValueWriterAgree` is **undecided** at HEAD: it was *refuted* with a reachable witness — `Ref.encode` of an array
whose declared constructor is unassigned and whose item list is empty wrote octets that its own reader then refused — the reference's arm was fixed to consult the declared constructor, and the refutation was
**withdrawn in the same slice**, replaced by `arrayUnassignedEmpty_class_agrees` (the law's error conjunct at the witness, stated in the law's own form) and `ref_encode_unassignedConstructor` (the closure: every
array whose declared constructor is unassigned, whatever it carries, nested included). The send instance stays conditional, and **the classing removed the *type* obstruction that made its endpoint-level
refutation inexpressible** — so that refutation is now landable and is not yet landed.

**And the 49 clauses marked `deferred:S4` were triaged rather than assumed, which changed what the widening is for.** They split three ways: **one was already carried** — `definition:connection-error/choice:framing-error.u1`, whose
rule both artefacts state beside the condition constant they raise, so it was the ledger under-reporting its own coverage rather than an obligation — **25 are genuinely blocked** on the widening, and **23 belong to another class or milestone**, which is
the number that matters because it was the largest and the least expected. The blocked set also says which part of the model each needs, and the answer is not the one the D4 record leads with: **the unsettled map is wanted by 22 of the 25**, link
identity by 8, sender-side delivery bookkeeping by 6, and more than one link per session by only 2 — so the widening's centre of gravity is the map, not the second handle it is usually described by. Of the 23, four are the sending half the model
states as an exclusion in its own docstring (it transitions on frames and builds none), five are extension capabilities the plan bounds out, four are flow quantities the credit contract already excludes (`available` and `drain`), two are definitional
sentences the generated choice tables fix, two are multi-version negotiation, one is a SHOULD the conformance contract's own rule places as a fairness-qualified progress obligation, and the rest are the terminus family that belongs to `S3-session`.
**None of the 23 is blocked on the widening**, so the widening's contract list is **26 clauses rather than 49** — the 25 the triage called blocked, plus `closing-a-link.2`, whose reattach half needs the link identity the widening supplies and whose other half is frame construction. The 23 were applied as dispositions rather than left in a report: eighteen left `deferred:` entirely (five extension capabilities, four the sending side, four unread flow quantities, two definitional sentences the generated tables fix, two multi-version negotiation, one a SHOULD the conformance contract places as a progress obligation or a recorded freedom — the model being total, the freedom is what it is), and four moved between milestones (three to `S3-session` with their terminus family, `connections.u1` to `S2`, which owns the frame layer). **`deferred:` fell from 180 to 161 and S4 from 49 to 26**, and the classes are now recorded as classes, so the ledger says why nothing will carry those sentences rather than when something will.

**Why the corpus missed it is a fact about the corpus, and worth the sentence**: **no vector in `vectors/**` uses an unassigned array constructor at all** — the corpus spells `"constructor": "a1"`, `"a3"` and
assigned siblings — so 68,395 vectors and a 114,225-buffer class sweep said nothing about a hole that one authored vector found immediately. **A corpus that samples a space rather than sweeping it cannot report
what it never visits**, which is the argument for the widening slice and the reason three defects this session were invisible to every gate.

**And a third family of the same shape is being removed rather than recorded.** The reference writes a four-octet size, count or length through `u32be`, **truncating** where the specification refuses `limit`. The
octets a truncating writer emits are well-formed and wrong — a reader accepts them and calls the value something else — so it is the same defect as the array hole and the same fix (refuse rather than truncate). Its
distinguishing feature is that **no term can instantiate it**: a body reaching 2^32 octets is representable in the vocabulary and cannot be constructed, so the law is *unprovable and unrefutable* there until the
truncation goes. A specification quantified over a domain the assistant can denote but not build is a boundary worth naming.

**And the shadowing hazard bit a third time, by a different mechanism from the first two.** Naming the new classed failure `SpecAMQP.Ref.Refusal` shadowed `SpecAMQP.Harness.Refusal` through an `open` in a file the
change did not otherwise touch, breaking 23 elaborations. The rule extends: when adding a declaration, grep for `open`s that would **capture** it, not only for modules that **declare** the same name.


**And the truncation family is closed, with its extent stated rather than asserted.** The reference's writer had **seven sites and twelve field writes** emitting a four-octet size, count or length through
`u32be` — a variable value's length, an element's length, an element compound's size and count, a compound's size and count in two arms, an array's size and count in two arms — and all twelve now go through
`Ref.fieldOctets`, which refuses class `limit` where the specification's `filled`/`compoundOctets`/`arrayOctets` do. **The boundary is the useful part**: six remaining `u32be` uses are *value* fields that
cannot truncate (`.uint`/`.char` take a `UInt32`, `.int` is masked, and the same three element constructors), the `u16be` sites are narrow already, and the frame's own SIZE field was guarded from the start with
class `sizeMismatch` in both artefacts. `ValueWriterAgree`'s first conjunct is true at that boundary *trivially* — the reference refuses, so there are no `ok` octets for the hypothesis to be given — and the law
as a whole stays undecided, with the two-encoder traversal as the only thing between it and a proof.

**And adding a corpus to a gate is not the same as wiring it.** The twelve staged vectors were added to `s1_differential.sh`'s loop, and the loop's `case` still had its catch-all `*) name=generated`, so the
twelve-vector file wrote over the *generated* log and the non-vacuity check then read a histogram of one corpus while asking a question about another — red on any tree, failing on a number no change under
`lean/Ref` could move. **A list of corpora and a mapping of corpora are different edits**, and the second is the one that fails silently; the new corpus now has its own guard (at least twelve vectors, each
carrying a refusal expectation) so a small corpus cannot pass this gate vacuously, which is the failure mode small corpora are most exposed to.


**And a second coverage property, which generalises the first**: **all 77 zero-width vectors in the corpus carry a *matching* item** — `0x40` with `null`, `0x41`/`0x42` with a
boolean, `0x43` uint, `0x44` ulong, `0x45` list — so a corpus of that size said nothing about the shape where a zero-width form is handed something of another kind. Together with the unassigned-constructor
finding this is a property rather than a coincidence: **a corpus built from the artifact's grammar naturally covers the shapes the grammar admits, and the defects live in the shapes it does not.** Both
sweeps now running attack exactly those combinations, which is why the first found three defects in one outing after 68,120 vectors had found none.

**And the fix's extent was measured rather than asserted, then proved past its samples.** The zero-width family was swept exhaustively — `0x40` diverged on 8 item kinds, `0x41`/`0x42` on 7 each, and the
zero-value arms `0x43`/`0x44`/`0x45` agree with the specification on all nine each — and then *closed* by theorems that generalise (`ref_arrayElement_null_refuses_mismatch` over every item that is not
`null`, `zeroWidthMismatch_class_agrees` stated in the law's own form, and `ref_encode_zeroWidthMatch` showing the matching case still writes the same octets). **A fix that states what did *not* change is
checkable in a way that a fix stating only what did is not.**

**And the seventh sentence to outlive its subject was in a slice's report rather than in the plan** — a warning that the specification still writes `0x41` with `false`, raised two commits *after* the fix
that refuses it, with the corpus carrying four vectors for those pairs and the specification refusing each by name. The instinct was right and the timing was the problem: **in a tree where four slices land
fixes within the hour, a report should state the commit it read, not the state it read.** That is a rule for briefs and reports, not only for the plan, and it is the same rule the earlier ghost sentences
produced.


**And the session surface is swept, with the same method finding the same shape of defect.** `generated-exchanges.ndjson` went 71 vectors / 278 step verdicts to **92 / 356**, with **zero of the
278 pre-existing verdicts changed** — the sweep added coverage without moving anything it touched. Twenty-one vectors are carried, and fifteen are staged as the next fix slice's opening evidence: **four divergences**
and **eleven shared gaps**, where a shared gap is a clause neither artefact enforces, so no differential can see it and the corpus is the only instrument that can.

**Six of those fifteen have since been promoted, which empties the divergence class.** Two moved at `61c0430` once the reference's field list gained `properties` and its count reader learned that a present-and-null `delivery-count` is not an integer, and the
last four at `1a21b0a` once both artefacts read the transfer flags by value and the aborted delivery reached the credit spend — taking the corpus to **98 vectors / 383 step verdicts** with **no pre-existing verdict moved** and the refusals moving only where the
new vectors refuse (`limit` 12→14, `malformed` 18→20). **Four remain, thirteen steps between them and five of those steps failing in both artefacts.** The count and the classification are both in the file rather than here, and **these two sentences are the reason**: this passage said nine and that all of them
were shared gaps, and the promotion emptied five while the artefacts began agreeing on some of the steps of what stayed. What *fails* is still shared in both — that is what makes a staged step a blind spot — while the vectors themselves are no longer uniformly
so, and a staged file's docstring claiming every vector in it was one was found by the security window and corrected by the promotion that emptied five. **Counts and classifications move every time a milestone lands; the obligation does not.**

**And the sweep's own inference about two of those four divergences was wrong, in a way that earned a rule.** It staged the credit an aborted delivery spends as *undecided* — "the register is silent, which is why this is staged rather
than decided" — and the register is indeed silent about it, because the reading does not live in the register. `flow-control.5` ("whenever the sender increases delivery-count, it MUST decrease link-credit by the same amount"),
`flow-control.9` and `links.33` are each dispositioned **`formalized:SpecAMQP.Spec.Session.transferLink`**: the specification implements a reading, and the disposition names the declaration that carries it. **The register's silence does not make
a question open.** A `formalized:` disposition is a decision too, and it is the one a divergence should be read against *first*, because a `formalized:` that names a declaration turns the divergence into a defect and takes it out of the register's
jurisdiction altogether. The pair was waiting for a reading that already existed, one layer away from where the sweep looked.

**The same audit found the defect the deferred clauses were hiding, and it is the sharpest case yet of a family inheriting its reading from one reader.** Both artefacts read the three transfer booleans — `settled`, `aborted`, `more` — by
**presence**: `fieldSet`/`present` asks whether a field is there, so a peer writing `settled=False` was read as having written `true`. The authority is not the deferred clauses: `settled.6` ("MUST be false (or unset)") and `more.u1` are
`deferred:S4` and `deferred:S3-session`, but `settled.1`, `settled.2` and `settled.4` are formalized — and `settled.4` is the one a presence reader cannot satisfy, because it obliges the flag to be **true** under the «settled» negotiation, which a
presence read satisfies with a frame that sets it false. **The artifact's own worked diagrams are the practical form of the argument**: they write `settled=False` on transfers *and* on dispositions, so the encoding both artefacts collapsed is the
one the standard's examples use. `Delivery.step`'s docstring had already assumed a value was passed to it ("false is the first transfer's value when the field is unset"); the call site contradicted the function's own contract.

**And why it stayed invisible is worth naming**: the clause that makes the explicit-false encoding *common* — `settled.6` under the «unsettled» negotiation — is deferred, so every vector exercising the defect classifies as a shared gap rather than
as a regression, and a shared gap is exactly what a differential cannot see. *A defect against a formalized clause can hide behind a deferred sibling*, and the instrument that finds it is the corpus, not the differential.

**The check that produced the right scope was the disposition read, not the clause read.** The same grep that found the three presence reads first looked like a fixable defect against `settled.6` — which is **deferred**. Dispatching that fix
would have implemented an S4 obligation in both artefacts and moved a milestone boundary without anyone deciding to move it; the disposition read is what stopped it, and it is why the repair that did land reads bool**values** and adds no refusal
anywhere.

**The fix ran as one reading across two owners** — the shape the ownership rule forces, and the reason the reading had to be settled before either half moved: `lean/Spec/**` is the planner's, `lean/Ref/**` a coder's. `fieldBool` and `valueBool` join
`lean/Spec/Connection.lean` beside the other value readers, and the session layer's explicit `open SpecAMQP.Spec.Connection (…)` list is what makes a new definition visible to it at all — the compiler reports a missing name as an *unknown
identifier*, not as an unexported one, which cost two misdiagnoses of a stale olean before the list was read. One shared `booleanAtField` reader in `lean/Ref/Session.lean` is where the family's reading now lives. **Two sites came back beyond the
three**: the reference's `disposition`'s `settled` and the `settled` the transaction layer is handed, both the same defect, and the specification's disposition site had already been changed here — so leaving them would have been a divergence
rather than a deferral, and the field's *declaration* (`type="boolean" default="false"`, "If true, indicates that the referenced deliveries are considered settled") is the authority the clause list does not carry. **Five sites, one reading, and
no committed verdict moved** (`d50abc1`, `1540777`).

**And what remains staged is not a backlog of defects — it is the deferred obligations made visible, which is worth stating because the two look identical from the corpus's side.** the counts here are the promotion's and the classification is in the file, and what is stable is the *kind* of thing that remains: largely `deferred:S4` (`flow/field:delivery-count.3`'s receiver echo, `field:delivery-count.2`'s presence half, `transfer/field:settled.6` in both directions, `resume.2`, `resume.3`, `attach/field:unsettled.5`) or `deferred:S3-session`
(`transfer/field:rcv-settle-mode.u1`) or `deferred:S3` (`picture.24`'s `-` column). **Every one of the nine is a clause the plan already carries later**, which is why they fail in *both* artefacts and why the differential cannot see any of them: the
staged set's *failing steps* are shared in both artefacts, so the corpus is the only instrument that can see them, while the set as a whole is no longer uniform. So the staged file's job is not to be emptied; it is to hold, per milestone, the obligations a gate cannot yet require.

**The three that were blocked by a decision rather than a milestone are no longer blocked, and the distinction is the one that governs whether a queue of them moves at all.** `resume.2` and `resume.3` are placeable under the natural readings their
dispositions already name — the resume flag is consulted where it is read, on a continuation arriving at the same session — and `attach/field:unsettled.5` is pinned by an exemption vector whose note says it is the exemption and that it admits, which is weaker
evidence than a refusal and is labelled as such. A clause blocked by a decision is not waiting on work; it is waiting on somebody choosing between readings that resolve differently against the corpus, and these three were unblocked by choosing. The distinction matters to anyone picking this up: `resume.2`, `resume.3` and `attach/field:unsettled.5` each name the local unsettled map or a resumed
delivery, and `MODEL RESTRICTION: the S4 slice contains at most one link per session` (§13's D4 record) means the model has no link identity to resume and no map to consult. They are the server-side obligations §23.3 lists — resumption is what a
broker needs most — and they move only when D4's named triggers fire, not when a milestone arrives.

**One disposition was asserting more than a declaration carries, and the staged corpus is what showed it.** `flow/field:delivery-count.2` read `formalized:Spec.Session.flowCountRefusal` while its staged vector failed in both artefacts: the sentence
carries two obligations — the value ("to the current delivery-count") and its being set at all — and `flowCountRefusal?` refuses a present-but-wrong count, returning `none` when the field is absent. The note had disclosed the presence half
precisely, with the line numbers; what the *value* could not say is that half the clause is pending, so it now carries `deferred:S4` as well. **A `formalized:` that covers half a sentence conflates completed work with pending work**, and the
vocabulary had no form for it until this clause needed one.

**The priority family produced sixteen of the thirty-six, and it is the session layer's form of the shape the value sweep found three of** — a declared or negotiated value against what the frame carries. Where the
value layer's version was a *constructor* against its *contents*, the session layer's is a *negotiated mode* against a *field* (a settlement flag under the choice that forbids it, a receiver's mode under a
`first` negotiation, a count against the credit actually held), and the same three-reading split appears: what the flag says, what its presence implies, and what the negotiated state permits.

**And the corpus's blind spot showed a fifth time, in its sharpest form yet**: `flow/field:properties.1` is one of **five** sentences that read *"When the handle field is not set, this field MUST NOT be
set"*, the register's `flow-link-field-without-handle` names all five, the reference's field list names **four** — `properties` is missing — and the corpus's existing vector for that clause used `available`,
which both artefacts list. So a family of five was tested through one member, and the divergence sat behind the one nobody tried. **That is the third instance of the same property in one day** — no vector uses
an unassigned array constructor, all 77 zero-width vectors carry a matching item, and a five-member rule is pinned through one member — and the general form is worth stating once: *a corpus built from the
artifact's grammar covers the shapes the grammar admits and the members someone happened to type, and the defects live in the shapes and members it does not.*

**And the sweep stated what it could not test, which is the part a later reader needs most**: four rules that could not become vectors at all — `max-frame-size.3`'s 512-octet floor (the clause constrains the
*declaring* peer and no clause says what a receiver does, so the floor has no observable at this boundary); the **handle direction**, whose sentence is an unnumbered doc paragraph so no citation can carry it,
which is why the corpus uses handle 0 on both ends everywhere and the direction stays untested; `delivery-count.4`, unreachable because a flow naming a handle needs an attached link at that end; and five
clauses needing a link *identity* neither model has. **An untestable rule named is worth more than a test that looks like it covers one.** **And the promotion produced the mirror image of that sentence, which is the more dangerous half**: three committed refusal vectors were passing for a *different* rule than the one they cite. They had been authored as refusals of the delivery-count rules and were in fact refused earlier, on the session's own precondition that a flow's next-incoming-id is set exactly when the partner's begin has arrived — so they were evidence for nothing they claimed, and they were *green*. The promotion found them because a probe it was placing rebuilt its frame with the begin's three window fields and then failed for that reason, and the same wrong reason turned out to underwrite three vectors that had looked settled for as long as they had existed. A refusal that arrives by the wrong route is worse than no test at the same place, because it occupies the position: nothing looks missing, and the rule it names is never exercised. **So a refusal vector's evidence is its *reason*, not its verdict**, and the reviewer's job is the reason. **The same class produced the day's largest corpus defect, and it was found by adding a reader rather than by a search**: the transaction corpora carried `coordinator.capabilities` — declared `multiple` with a
`requires` role — as a **list** of symbols, where the types section gives a `multiple` field the **array** representation and the section's own worked example encodes `book.authors` as `0xE0`, which
`vectors/primitives.ndjson` reproduces as canonical. Nothing read that field until the terminus rules landed, so the vectors were green because they were *unread*; when both readers arrived they refused the
shape identically and `s6` went red. Two consequences. The corpus moves to the artifact's array form, because a positive vector has to be a conforming message. And the security layer's tolerance of the same
violation is a **defect rather than a reading**: `sasl-server-mechanisms` is also `multiple`, is carried as a list in the exchange corpora, and is admitted because that path reads it through `symbolList`
instead of through its declaration — so `s7` is green on a shape both readers refuse elsewhere. The generator should emit the array form for every `multiple` field, and its byte-identity check will show how
many corpora move when it does.
 **The review of that promotion accepted it and left two things worth more than the acceptance.** The first is *how* the reason gets checked, because the corpus cannot check it: every refusal in
this family carries `amqp:invalid-field` with class `malformed`, which is also the class the shadowing precondition produces, so the pinned condition and reason class are too coarse to tell a rule's own refusal from an earlier guard in the same chain. The reviewer
therefore built both executables, ran them against the corpora with full output, and read the harness's per-step `detail` string — the codec's own class-prefixed message — then read the Lean guard that produces each message to confirm it is the cited clause's predicate rather
than the precondition at line ~1470 that runs unconditionally before it. **A condition and a class are what a corpus can pin; the reason is what a review is for**, and the two are not substitutes. The grep that settles it is available to anyone: the precondition's text appears
in exactly two step verdicts across the whole exchange corpus, both in vectors authored *about* that rule. The second is that the mechanism which produced the vacuity is still standing: four separate places in the generator hand-build a flow's window fields as literal dicts,
because the canonical builder always writes all seven and the presence vectors need fields omitted. Nothing triggers it today, and a second writer of the same shape is how it triggered the first time. **And a fifth joined them from the security layer's work, found by the promotion rather than by a search**: an empty frame *offered* by the endpoint cannot be pinned in the
corpus at all. The shape looks available — a `send` step may carry raw octets — but both artefacts' step builders refuse to *write* one, and refuse it in prose a reader can act on: "the frame carries no body: an empty frame is how a peer with nothing to send
defeats an idle timeout, and this writer does not send one". That refusal is a MAY the writer is entitled to take, so the rule's send half has no observable at this boundary; its receive half is pinned by the SASL probes, and the send half's evidence stays the
theorem `frame_none_answers`. The promotion named it a **vocabulary gap rather than a missing vector**, which is the right name: nothing is absent from the corpus that could be added to it.
