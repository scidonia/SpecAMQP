# Findings — the cross-cutting methodological record

The most reusable content in the old plan: findings that recurred across rungs and
govern how every check in this repository is judged. Each is quoted **verbatim** from
the rung file that holds the full episode, with the source named; nothing here is
paraphrased. §27 (the tail trial) is preserved whole at the end.

## 1. A check whose failure mode is silent agreement with what it checks

Four instances in one family, from `S1.5.md` (the old §13, S1.5 span):

> **The session's sharpest methodological finding is one family with four instances: a check whose failure mode is silent agreement with what it checks.** In each case the check was written in a way that made it incapable of detecting the difference it existed to detect, and in each case it was caught by something *independent* of what it was checking:
>
> * **A corpus that encodes the implementation's error.** The connection generator's `refused()` helper defaulted every refusal to `framing-error`, so the corpus encoded the wrong condition for every state refusal — which is why 150 step verdicts agreed across two artefacts while both were wrong. The corpus could not have caught it, because the corpus *was* the error.
> * **A contract that pins the code's behaviour instead of the artifact's rule.** `slice-sasl-challenge-from-client`'s fourth step expected the condition the implementation happened to produce rather than the one the artifact defines, and the frame corpus's encode vector expected a non-canonical form derived from what the writer did rather than the table's narrowest-form rule. Both were found by owners fixing the code and watching a contract disagree.
> * **A sweep that shows only refusals.** A permission sweep made entirely of refusals cannot distinguish a correct rule from an implementation that refuses everything — the two produce identical evidence. The session sweep now gives every rule probe its complement, and the six controls that resulted are the only probes that can tell the difference.
> * **A probe that fails for a reason unrelated to the rule it tests.** The session sweep's flow frames omitted `next-incoming-id`, which the artifact requires once `begin` has been exchanged and which every state a flow can be sent from is past — so a flow cell refused for that reason would have read as a permission refusal. Found in the preparation, before anything ran against live code.
>
> The general form is worth stating because it governs how every check in this repository is judged: **a check has value only if it can fail for the reason it exists to detect, and separately from the other reasons it might fail.** The four instances are that statement's four shapes — the check agreeing with the thing it checks, the check unable to distinguish its two outcomes, and the check failing for an unrelated cause. The remedies are correspondingly four, and all four are now in use: an *independent source* (the artifact, never the implementation), an *explicit expectation* (a prediction, since a record predicts nothing), a *control* (the case the rule permits, not only the case it forbids), and a *well-formedness precondition* (so the failure has one possible cause). The checks that caught all four were each independent of what they checked: the audit read the artifact's definitions, the register compared them against a chosen condition, the coder compared the table's rule against the writer's output, and the sweep's author read the artifact's own mandatory-field rule against their own frames.

And its corollary, from the same file:

> **The family has a corollary, and the session sweep's author supplied it by applying the family to their own observer.** A check that *reports* a difference is itself a check, and it has the same failure mode: a flag that never fires is indistinguishable from a flag that always passes. So the sweep's per-family tally — each family's cell count and its refused/admitted split, with a family the model says behaves uniformly flagged SCATTERED when it does not — was **shown to fire by driving it with a synthetic run** whose every other unattached-handle cell admits, after which it reports the split and the flag; and the legitimately mixed state-permission family is left unflagged, which is the other half of the demonstration. That is the four remedies applied to the instrument rather than to the subject: an independently driven input, an explicit expected report, a control that must *not* fire, and a shape in which a firing has one possible cause. The reader of a sweep report should be able to see both that the flag can fire and that it does not fire on variation the model already expects — a flag with neither property is a green light wired to nothing.

## 2. Derived instances are invisible to the surfaces that read them

Two instances. First, `Except`'s `Functor` (from `S1.5.md`):

> **The `Functor.map` wall is retired, and its real cause was not what five rungs said it was.** `Except`'s `Functor` instance is derived from its `Monad` instance, so a call site's `x >>= f` and `f <$> x` are class *projections* applied to `Except.bind`/`Except.map`: every case equation holds by `rfl`, none is a `@[simp]` lemma, and `simp` will not unfold a class projection to find one — so `by simp` reports "made no progress" on a goal whose proof is `rfl`.

Second, `deriving BEq` opaque to the kernel — and invisible to the trust scan (from §27,
preserved whole below):

> **And a third finding, which is a trap for anyone proving anything about a `Value`.** Both artefacts' duplicate-key check compares keys through the `BEq` instance their `Value` types *derive*, and a derived instance is **opaque to the kernel**: `#print` reports `opaque …beq`, there are no equation lemmas, `unfold` and `decide` fail, and there is no `LawfulBEq`. So the obligation the duplicate path needs — that the reference's comparison agreeing implies the specification's does — is **unprovable rather than merely unproved**, a more expensive dead end than a missing lemma, because no amount of proof search reaches it. The fix is to write the comparison out; the alternative, a second comparison used only by `keysRepeat`, was rejected because two notions of key identity inside one artefact is worse than a hundred lines of case analysis.
>
> **And the trust scan cannot see this.** It scans source for the `opaque` keyword, and a `deriving` clause is not one, so an opaque definition can sit underneath a theorem whose printed inventory is clean. `deriving BEq` was the instance both artefacts used for the same purpose, so this is not a corner: whether any accepted theorem's dependencies include a derived instance is worth a check of its own, and it is named here rather than left to be rediscovered by the next author who reaches for `unfold` and finds nothing to unfold.

## 3. Latent corpus defects surface only when a model strong enough to enforce the rules exists

From `Widening.md` (the old §24): the restricted one-link model could not see that its
own corpus was invalid; the widened registry could.

> **The transaction-corpus correction is also failure-first, not a model exception.** The restricted
> one-link model ignored attach names, so the mismatch stayed invisible. The widened registry
> correctly created two identities; the following flow then named a link whose local endpoint had
> never attached and was refused by the delivery-count rule. Eighteen of the 36 transaction verdicts
> failed per artefact. The encoded peer frames remain byte-for-byte unchanged; changing only each
> mismatching structured send attach's name to its peer's name preserves valid frame sizes and the
> intended one control link. Reading delivery-count session-wide would contradict the rule's link
> endpoint subject.

## 4. The failure-first window closes at the amendment

From `Widening.md` (the old §24, part 3): once the frozen amendment requires the new
field, the pre-implementation failure can no longer be reproduced — the observation
has to happen before the freeze, and no synthetic hybrid is claimed after it.

> Against the committed pre-index reference, step 7 was observed admitted in the mapped session rather than refused as malformed. The specification at that commit cannot elaborate once this frozen amendment requires the new index field, so no synthetic hybrid is claimed as a second red observation; both artefacts give the pinned refusal after implementation. This twelfth boundary scenario is the failure-first contract for `disposition.4`'s completed case.

## 5. Hand-editing encoded frames is a silent-corruption trap

From `Widening.md` (the old §24): a frame edited by hand is a length field waiting to
disagree with its content; the repair rebuilds through the frame writer so no encoded
length is hand-maintained.

> The same pass found a separate invalid role pair in
> `txn-payload-on-a-link-that-is-not-a-control-link`: both endpoints attached as receivers before the
> peer sent a transfer. Both widened readings correctly refused it. Its peer attach is rebuilt through
> the frame writer as the sender, including the sender's mandatory initial delivery count; no encoded
> length is hand-maintained, and the non-control-link payload verdict remains admitted.

## 6. `| tail` swallows the exit status

From `S1.5.md` — a pipeline's last command, not its gate, decided the commit:

> **And the bad commit landed because a pipeline's exit status came from `tail`.** `… gate.sh | grep -v warning | tail -2 && git commit` commits whatever the gate said, because `&&` reads the last command's status — the same defect the plan recorded an hour earlier in two of my own scripts, appearing this time in a shell invocation, which is a sign the shape is about *reporting* rather than about any one tool. The correction is the same in both places: **read the exit status of the thing being checked, not of whatever prints its output.**

And the same shape one level down, from `S2.md`:

> A loud failure rather than a silent pass, which is worth having checked: the same command through a pipe reported exit 0 until the status was measured directly, which is exactly the shape of a gate that protects nothing.

## Further cross-cutting findings, indexed rather than repeated

Each of these is stated in full in the named file:

- **A claim's source must be the thing the claim is about** — and the operational forms are receipts (`S1.5.md`).
- **State the property over the states the subject actually reaches** — vacuous where the work is, or universal where only reachable states are at issue (`S1.5.md`).
- **A law quantified wider than its contract needs is not stronger but false** — four instances, each repaired by restricting to the reader-reachable domain (`ConformanceInterface.md`).
- **A corpus built from the artifact's grammar covers the shapes the grammar admits, and the defects live in the shapes it does not** (`ConformanceInterface.md`).
- **A value recoverable only from rendered prose is invisible to the kernel** — make the class a field (`S1.5.md`).
- **A moving number is never quoted bare in a document** — the sentence carries the command, not the number (`WorkingAgreements.md`). The split this directory performs is that rule applied to the plan itself.
- **A generated artefact and its generator land together or neither** (`WorkingAgreements.md`).
- **A correction reaches every sentence that asserts the old state** — grep for the claim's own words (`WorkingAgreements.md`).
- **A vector's refusal must be attributable to exactly one rule** — disable the rule and watch the vector fail (`S1.5.md`).
- **A refusal vector's evidence is its reason, not its verdict** (`ConformanceInterface.md`).

## §27. What the tail trial found: the notes navigate, they do not cost

> Moved verbatim from `PLAN.md` §27 (lines 2286–2296) on 2026-09-25.

**Two of the three notes were accurate about the site and incomplete about the cost, and both incompletenesses were load-bearing.** `map.u1`'s note named the reader and not the writer — and a reader-only refusal makes `RoundTripOnEncodedValues` and `ValueConsumption` false as stated, because the writer emits exactly what the reader would now refuse, so the law's premise stays reachable. The transport-role note named "an `Endpoint` field carrying the transport role … and a guard" and did not say that `Endpoint` is the state `Proofs/ConnectionConformance` walks guard by guard for *every* endpoint: `stepHeader_pair` and `stepSaslFrame_pair` case-split at each guard and bridge the reference's through `refPeerOf` projections, so a new guard is a change to thousands of lines of proof rather than a local edit. The slice implemented it end to end, found its `rw` patterns would not match the goals' projection forms, and reverted the whole attempt — the right call, and the clause stays deferred with its cost now known rather than guessed.

**And that clause is corpus-unreachable whatever is done.** No exchange vector can set an `Endpoint` field beyond `state` (`ConnectionCodec.start`), so the transport role can never be pinned by a corpus step; its carrier is the theorem, and the probe written for it fails to compile against today's tree — which is the failure class this repository allows for a statement that cannot be written yet.

**What this means for the remaining 92 clauses.** A note says *where* a clause's gap is; it does not say *what closing it touches*. Two dispatches so far have discovered the second thing at the point of implementation, where the discovery is expensive and where the temptation to adjust a statement is highest — one of them took a proof obligation the note did not mention and left the package unbuildable until it was fixed. So the dispatches from here ask for the costing as well as the site: which modules a change reaches, and whether the reach includes a conformance proof whose guard structure it would have to follow. That is a scout's question rather than an implementer's, and it is cheap to answer before the work starts and expensive to discover during it.

**And a third finding, which is a trap for anyone proving anything about a `Value`.** Both artefacts' duplicate-key check compares keys through the `BEq` instance their `Value` types *derive*, and a derived instance is **opaque to the kernel**: `#print` reports `opaque …beq`, there are no equation lemmas, `unfold` and `decide` fail, and there is no `LawfulBEq`. So the obligation the duplicate path needs — that the reference's comparison agreeing implies the specification's does — is **unprovable rather than merely unproved**, a more expensive dead end than a missing lemma, because no amount of proof search reaches it. The fix is to write the comparison out; the alternative, a second comparison used only by `keysRepeat`, was rejected because two notions of key identity inside one artefact is worse than a hundred lines of case analysis.

**And the trust scan cannot see this.** It scans source for the `opaque` keyword, and a `deriving` clause is not one, so an opaque definition can sit underneath a theorem whose printed inventory is clean. `deriving BEq` was the instance both artefacts used for the same purpose, so this is not a corner: whether any accepted theorem's dependencies include a derived instance is worth a check of its own, and it is named here rather than left to be rediscovered by the next author who reaches for `unfold` and finds nothing to unfold.
