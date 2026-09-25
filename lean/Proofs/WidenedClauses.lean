import Spec.Protocol

/-!
# The clauses no corpus step can pin, and what the widened model can state about them

`PLAN.md` §24's twenty-six clauses include ten that a per-step corpus cannot oblige: each requires an
endpoint to *emit* a frame with a chosen content, to hold a comparison whose outcome nothing reads, or
to restrain a send the vocabulary cannot ask for. The corpus records them as a finding about the
harness rather than about the clauses; this module is what the widened model can say about each.

**What is proved here is the state facet each clause names, not the clause.** The distinction is the
point of the module: a clause whose subject is a MUST-send, a held comparison or a reduction between
two endpoints is not discharged by a theorem about a `Bool` or a structure field, and none of the
theorems below is offered as its proof. What they establish is that the model's own vocabulary for the
clause behaves as the clause says that facet must — a comparison that reports agreement and
disagreement rather than choosing, an absence that is nothing, a predicate that is exactly "the link
holds this tag", a reduction that clears the latches and suspends both ends, and a resume claim no
continuation can move.

**Two of the ten are not carried at all, and no theorem here claims them.** `links.2`'s second half
("the first attach MUST then be closed with a link error of «stolen»") and `closing-a-link.2` ("the
partner MUST signal that it has closed the link by reattaching and then sending a closing detach")
each oblige an endpoint to *write* a frame with a chosen content. `Spec.Protocol.step` has no output
result — it answers `Except Refusal WidenedSession` — so no declaration in this development can carry
either: a refusal value naming the condition such a frame would carry is not the frame, and stating
one would count a content shadow as the clause's carrier. They remain unresolved obligations of the
model's output alphabet, named here and in `Spec.Protocol`'s own docstring rather than shadowed.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Spec
open SpecAMQP.Spec.Session
open SpecAMQP.Spec.Protocol

/-! ## `attach/field:unsettled.1` — the held comparison

The clause says the local and remote delivery states **for a delivery-tag MUST be compared** to
resolve an in-doubt delivery. The comparison is not a verdict, which is why no vector can pin it: it
produces a judgement about two observations, and the corpus observes frames. What is stated below is
that the model's comparison *is* a comparison — it reports agreement, reports disagreement, and has
nothing to say about a tag the link does not hold — and not that any endpoint acts on the outcome,
because no clause makes it. -/

/-- A tag the link does not hold has nothing to compare. -/
theorem resolve_absent {link : WidenedLink} {tag : DeliveryTag}
    (h : link.unsettled tag = none) : resolve link tag = none := by
  unfold resolve
  rw [h]

/-- Where the two observations agree, the comparison reports the state they agree on — not one of
the two picked silently, which is what a model that compared nothing would also report. -/
theorem resolve_agrees {link : WidenedLink} {tag : DeliveryTag} {entry : UnsettledDelivery}
    (h : link.unsettled tag = some entry)
    (hsame : sameState entry.localState entry.remoteState = true) :
    resolve link tag = some (.agreed entry.localState) := by
  unfold resolve
  rw [h]
  simp only [hsame, if_true]

/-- And where they differ it says so, rather than choosing one: the half a model that "resolved" by
taking the local state would fail. -/
theorem resolve_disputed {link : WidenedLink} {tag : DeliveryTag} {entry : UnsettledDelivery}
    (h : link.unsettled tag = some entry)
    (hsame : sameState entry.localState entry.remoteState = false) :
    resolve link tag = some .disputed := by
  unfold resolve
  rw [h]
  simp only [hsame, Bool.false_eq_true, if_false]

/-! ## `attach/field:incomplete-unsettled.u1` — absence is not evidence

"The absence of an entry in an incomplete map is not evidence of settlement." The widened model states
it as a definition with no terminal branch: whether an incomplete map was announced or not, an absent
tag reads as *nothing*. The theorem is that the model has no branch that says otherwise — which is the
state facet of the rule, not the endpoints' obligations under it. -/

/-- An absent tag is not settled, complete map or incomplete: there is no branch that returns a
state for it. -/
theorem absent_is_not_settlement {link : WidenedLink} {tag : DeliveryTag}
    (h : link.unsettled tag = none) : absentDeliveryState link tag = none := by
  unfold absentDeliveryState
  rw [h]

/-! ## `resuming-deliveries.3`–`.5` — which end holds the delivery

`.3`/`.4` make the *sender* ignore an unsettled delivery only the target considers unsettled, and `.5`
makes it resume the ones both hold. Both turn on the same question — does this link hold this tag —
and `Spec.Protocol.resumable` is that question. Unlike the comparisons above, this one *is* read by a
rule the corpus pins: `transferLink` consults it for `transfer/field:resume.1`'s ignore and `.2`'s
refusal, so a model that answered it wrongly fails a vector. The theorems below establish the
predicate's meaning; the sender's and receiver's obligations that the three clauses place on it are
restraint and internal state, and remain unpinnable. -/

/-- The predicate *is* "the link holds the tag": the three clauses differ only in whose map is asked. -/
theorem resumable_iff_holds (link : WidenedLink) (tag : DeliveryTag) :
    resumable link tag = true ↔ ∃ entry, link.unsettled tag = some entry := by
  unfold resumable
  cases h : link.unsettled tag with
  | none => simp
  | some entry => simp

/-- A delivery the link holds is one the sender must resume (`.5`'s requiring case). -/
theorem resumable_of_holds {link : WidenedLink} {tag : DeliveryTag} {entry : UnsettledDelivery}
    (h : link.unsettled tag = some entry) : resumable link tag = true := by
  unfold resumable
  rw [h]
  rfl

/-- And one it does not hold is one it must ignore (`.3`/`.4`) rather than treat as its own. -/
theorem not_resumable_of_absent {link : WidenedLink} {tag : DeliveryTag}
    (h : link.unsettled tag = none) : resumable link tag = false := by
  unfold resumable
  rw [h]
  rfl

/-! ## `resuming-deliveries.6`/`.7` — reduce, then suspend and re-attempt

The two ends reduce as much as they can and then suspend, which is the state a resume is sent from.
The clauses' subject is an exchange between two endpoints that the per-step vocabulary observes one
step at a time, so neither is pinnable; what can be stated is the reduction's own state facet — that
it clears both latches, suspends both lives, and is a state rather than a step that accumulates. The
"then re-attempt" half is an endpoint's action, and is not claimed here. -/

/-- Reducing twice is reducing once: the reduction is a state, not a step that accumulates. -/
theorem reduce_is_idempotent (link : WidenedLink) : reduce (reduce link) = reduce link := rfl

/-- Both latches are cleared: an endpoint that has detached and re-attached has announced a complete
map, which is `attach/field:incomplete-unsettled.3`'s lift as a state. -/
theorem reduce_clears_the_latches (link : WidenedLink) :
    (reduce link).localEndpoint.incompleteUnsettled = false ∧
      (reduce link).remoteEndpoint.incompleteUnsettled = false := ⟨rfl, rfl⟩

/-- And both lives are `suspended`, the state whose description is "the termini exist, but have no
associated link endpoints" — which is what a re-attempt resumes from. -/
theorem reduce_suspends_both_endpoints (link : WidenedLink) :
    (reduce link).localEndpoint.life = .suspended ∧
      (reduce link).remoteEndpoint.life = .suspended := ⟨rfl, rfl⟩

/-! ## `resuming-deliveries.8` — the flag is the first transfer's claim

A MUST-send, so a `send` step cannot measure it — a step's value is the vector's own. What the model
can state is the property that makes the omission detectable rather than invisible: the in-progress
record's resume bit is the *first* transfer's, and no later transfer of the same delivery can change
it. That is the state facet, not the sender's obligation to set it. -/

/-- A continuation transfer leaves the resume claim where the delivery's first transfer put it. -/
theorem resumed_is_the_first_transfers_claim (held : WidenedDelivery) (id : Nat)
    (settled resumed : Bool) :
    (deliveryStep (some held) id settled resumed).resumed = held.resumed := rfl

end SpecAMQP.Proofs
