import Spec.Message

/-!
# The message layer's outcome and structure laws

`Spec.Message` holds the machine and the rules; this module holds the laws the ledger's
dispositions name, which are the sentences Part 3 states that the machine makes checkable. The
module is the outcome machine's laws extended rather than restated — `terminal_absorbing`,
`settled_monotone` and `recordState_settled` stay where the machine is, and what is here is what
they do not already say.

**Three families, and why each is a law rather than a rule.**

* **What the machine refuses, and only that.** `accepted.u2`, `modified.u2` and `released.u2` all
  say that a delivery reaching an outcome implies nothing about the transfers that remain: the
  outcome "does not imply that the remaining transfers for the delivery will not be sent", and a
  delivery "can become accepted at the source even before all transfer frames have been sent".
  The machine's content for those sentences is that it has no precondition about transfer
  progress at all — `applyState` refuses for terminality and for nothing else — which
  `applyState_refuses_onlyTerminal` states and proves. The transport half of those sentences, that
  the `aborted` flag is the only indication of a premature termination, is the transfer
  performative's and is not this layer's to state.

* **Terminality and what it retires.** `accepted.u1`, `modified.u1` and `released.u1` each open
  with "as X is a terminal outcome", which is a fact about the declared types' roles:
  `outcomesAreTerminal` proves it for every outcome the messaging layer defines, from the
  definition the machine already carries rather than from a list of five. `accepted.u1`'s other
  half — that the message is retired from the node, so redelivery to this link is over — is
  `acceptedRetiresTheMessage`. Each clause's resumption half ("transfer of payload data will not
  be able to be resumed if the link becomes suspended") is a statement about a suspended link and
  an unsettled map, neither of which this model has; the ledger records that as the gap rather
  than as a carrier.

* **The structure's two ends, and the annotations that move.** `footer.u1` says the footer is
  where what can only be evaluated once the whole bare message has been seen belongs, which is a
  fact about the footer's *position*: `footerClosesTheMessage` and `closedAssemblyRefuses` are
  that position made checkable. `message-annotations.2` is the annotations rule with its own
  exception — an intermediary propagates them "unless the annotations are explicitly augmented or
  modified" — and the augmentation the artifact names is the `modified` outcome's
  `message-annotations` field, so the merge `Spec.Message.mergeAnnotations` performs is the rule
  and the three theorems below are what "propagate unless augmented" means for it.
  `delivery-annotations.u1` — an annotation the recipient does not understand "cannot be acted
  upon" — is the gate in front of the one place this layer looks at an annotation's value.

## Failure first

Each theorem here was stated against the tree before the rule it is about existed, and the failure
is recorded with it. The two worth naming are the ones that are not `rfl`:

* `applyState_refuses_onlyTerminal`, against a machine with a second refusal — a guard on the
  delivery's payload being complete — left the branch that guard produces as an unclosed goal:

      case h_1 ... refused : Except.error reason = Except.ok ... ⊢ ∃ current, ...

  and the same shape in the other direction for `acceptedRetiresTheMessage`, whose `redeliveryAllowed`
  branch is where a machine that retired the message on settlement rather than on acceptance
  fails.
* `mergeAnnotations_keepsUnnamed`, against a merge that took the augmentation as the whole map —
  the shape a "modified replaces the annotations" reading produces — leaves the surviving pair
  unprovable:

      case nil ⊢ (k, v) ∈ augment

  which is the sentence's "propagate unless", read as a law.

## What is not claimed

That a suspended link cannot be resumed after an outcome, that an intermediary in a network
propagates a section, and that `received` is sent only on a resumed delivery's first transfer are
all obligations whose subject this model does not have — a link's suspension, a forwarding party,
and a sender over an unsettled map. They stay in the ledger as deferrals with the gap named.
-/

namespace SpecAMQP.Proofs.MessageLaws

open SpecAMQP.Spec.Message
open SpecAMQP.Spec.Codec (Value typeName)
open SpecAMQP.Harness (Refusal)

/-! ## The machine refuses for terminality and for nothing else

`accepted.u2`, `modified.u2`, `released.u2`: a delivery reaching an outcome carries no implication
about the transfers that remain, because the machine has no precondition about them. -/

/-- **The only refusal the state machine has is terminality.** Whatever state a caller applies,
the machine refuses it only when the delivery's recorded state is terminal, and it refuses it for
no other reason: there is no guard on the payload, on how much of the message has been transferred,
or on which state is being applied. This is the machine's content for the three sentences that say
an outcome may be reached before the last transfer and implies nothing about the transfers that
remain. -/
theorem applyState_refuses_onlyTerminal (delivery : Delivery) (state : DeliveryState)
    (settled : Bool) (reason : Refusal) (refused : applyState delivery state settled = .error reason) :
    ∃ current : DeliveryState, delivery.state = some current ∧ current.terminal = true := by
  unfold applyState at refused
  split at refused
  · rename_i current held
    split at refused
    · rename_i terminal
      exact ⟨current, held, terminal⟩
    · exact absurd refused (by simp)
  · exact absurd refused (by simp)

/-- An outcome is admitted by the machine whatever the delivery's history: a delivery that has
applied no state admits every outcome, which is the same fact at the machine's initial state. -/
theorem outcomeIsAdmittedAtTheStart (outcome : Outcome) (settled : Bool) (result : Delivery)
    (applied : applyState Delivery.empty (.outcome outcome) settled = .ok result) :
    result.state = some (.outcome outcome) := by
  unfold applyState at applied
  simp only [Delivery.empty, Except.ok.injEq] at applied
  rw [← applied, recordState]

/-! ## Terminality, and what accepted retires

`accepted.u1`, `modified.u1`, `released.u1`: each opens with "as X is a terminal outcome". -/

/-- **Every outcome the messaging layer defines is terminal.** The machine carries terminality as a
property of the state's *shape* rather than as a list — an outcome is terminal and a non-terminal
state is not — so this is the four constructors rather than four remembered names, and a fifth
outcome added to the layer is terminal by this equation. -/
theorem outcomesAreTerminal (outcome : Outcome) :
    (DeliveryState.outcome outcome).terminal = true := by
  cases outcome <;> rfl

/-- **The non-terminal state is not terminal.** The other side of the artifact's distinction: the
`received` state is the one the messaging layer defines for use during link recovery, and it is
the state a later state may replace. -/
theorem receivedIsNotTerminal (sectionNumber sectionOffset : Nat) :
    (DeliveryState.received sectionNumber sectionOffset).terminal = false := rfl

/-- **Where the machine does not refuse, the step is the recording.** A delivery whose recorded
state is not terminal admits a state, and what it admits is exactly `recordState` — so the
sentences that say a delivery admits an outcome whatever the transfers that remain are a statement
about the machine's *only* precondition being terminality. -/
theorem applyState_of_notTerminal (delivery : Delivery) (state : DeliveryState) (settled : Bool)
    (current : DeliveryState) (held : delivery.state = some current)
    (notTerminal : current.terminal = false) :
    applyState delivery state settled = .ok (recordState delivery state settled) := by
  simp [applyState, held, notTerminal]

/-- **The accepted outcome retires the message.** Recording `accepted` leaves the delivery in
`accepted` with redelivery to this link forbidden — the artifact's "the message has been retired
from the node", which is the half of the sentence this model can state. That redelivery is
forbidden by *acceptance* and not by settlement is what the statement shows: the settlement a step
states is an argument of `recordState` and appears nowhere in the two quantities. -/
theorem acceptedRetiresTheMessage (delivery : Delivery) (settled : Bool) :
    (recordState delivery (.outcome .accepted) settled).redeliveryAllowed = false
      ∧ (recordState delivery (.outcome .accepted) settled).state = some (.outcome .accepted) :=
  ⟨by unfold recordState allowedOf; rfl, by unfold recordState; rfl⟩

/-- **The accepted outcome does not increment the delivery-count.** `accepted.u3`. Stated at the
rule the machine's counter reads, so a machine that counted every terminal outcome fails here
rather than only in a vector. -/
theorem acceptedDoesNotIncrement : incrementOf .accepted = 0 := rfl

/-- **The accepted outcome leaves the count it was given**, whatever the count was: the statement
above at the machine rather than at the arithmetic. The step that reaches it, and the delivery's
own state, are `applyState_of_notTerminal`'s. -/
theorem acceptedLeavesTheCount (delivery : Delivery) (settled : Bool) :
    (recordState delivery (.outcome .accepted) settled).deliveryCount = delivery.deliveryCount := by
  simp [recordState, incrementOf]

/-! ## A state outside the five applies no outcome

`txn-work.u11` in the transactions artifact is a sentence about delivery state: "if the controller
requests a rollback or the discharge attempt be unsuccessful, then the outcome is not applied."
The messaging layer's content for it is the treatment of a state it does not define. -/

/-- **Recording a state the messaging layer does not define applies no outcome.** The transaction
layer's two states fill the delivery-state role and their rules are the transaction layer's; what
this layer states — and what the sentence's delivery-state half is — is that recording one moves
neither the delivery-count nor redelivery. Only the recorded state and the settlement move, which
is why the machine's four outcome quantities cannot be moved by a state it does not define. -/
theorem unmodelledStateAppliesNoOutcome (delivery : Delivery) (typeName : String) (settled : Bool) :
    (recordState delivery (.unmodelled typeName) settled).deliveryCount = delivery.deliveryCount
      ∧ (recordState delivery (.unmodelled typeName) settled).redeliveryAllowed
          = delivery.redeliveryAllowed :=
  ⟨rfl, rfl⟩

/-! ## The footer is the tail, and nothing follows it

`footer.u1`: the footer carries what "can only be calculated or evaluated once the whole bare
message has been constructed or seen", which is a rule about where in the structure a footer can
appear. -/

/-- **A section offered to a closed assembly is refused.** The structure rule's `closed` flag is
set by the footer and by nothing else, so this is "the footer is the tail of the annotated
message": whatever kind arrives after it, the reader refuses rather than reading a second tail. -/
theorem closedAssemblyRefuses (state : Assembly) (kind : SectionKind) (closed : state.closed = true) :
    ∃ reason : Refusal, Assembly.add state kind = .error reason := by
  unfold Assembly.add
  rw [closed]
  exact ⟨_, rfl⟩

/-- **Admitting a footer closes the message.** The positive half of the same rule: a message whose
sections the reader accepts has its footer last, so the footer's contents are read when the whole
bare message has been seen. -/
theorem footerClosesTheMessage (state : Assembly) (next : Assembly)
    (admitted : Assembly.add state .footer = .ok next) : next.closed = true := by
  by_cases hclosed : state.closed = true
  · simp [Assembly.add, hclosed] at admitted
  · by_cases hposition : Slot.footer.position < state.position
    · simp [Assembly.add, hclosed, hposition, SectionKind.slot] at admitted
    · have hnext : next = { state with closed := true, position := Slot.footer.position, any := true } := by
        simpa [Assembly.add, hclosed, hposition, SectionKind.slot, Slot.isHead] using admitted.symm
      rw [hnext]

/-! ## The annotations rule's exception is the merge

`message-annotations.2`: annotations are propagated "unless the annotations are explicitly
augmented or modified (e.g., by the use of the «modified» outcome)". The augmentation the sentence
names is the `modified` outcome's `message-annotations` field, whose own documentation states the
merge; these three theorems are what "propagate unless augmented" means for it. -/

/-- **Everything the augmentation does not name survives the merge.** An annotation the message
already carried, under a key the augmenting field does not name, is in the merged map: the
propagation half of the sentence, with the augmentation as the exception it names. -/
theorem mergeAnnotations_keepsUnnamed (existing augment : List (Value × Value))
    (pair : Value × Value) (carried : pair ∈ existing)
    (unnamed : augment.any (fun entry => sameKey entry.1 pair.1) = false) :
    pair ∈ mergeAnnotations existing augment := by
  unfold mergeAnnotations
  apply List.mem_append_right
  rw [List.mem_filter]
  exact ⟨carried, by simpa using unnamed⟩

/-- **Every entry of the augmentation is in the merged map.** -/
theorem mergeAnnotations_augments (existing augment : List (Value × Value))
    (entry : Value × Value) (carried : entry ∈ augment) :
    entry ∈ mergeAnnotations existing augment := by
  unfold mergeAnnotations
  exact List.mem_append_left _ carried

/-- **An entry of the merged map whose key the augmentation names comes from the
augmentation.** This is the replacement half: where the message already carried a value for a key
the outcome names, the outcome's value is the one that survives, and the message's entry for that
key is gone. -/
theorem mergeAnnotations_replacesEachNamedKey (existing augment : List (Value × Value))
    (pair : Value × Value) (merged : pair ∈ mergeAnnotations existing augment)
    (named : augment.any (fun entry => sameKey entry.1 pair.1) = true) : pair ∈ augment := by
  unfold mergeAnnotations at merged
  rcases List.mem_append.mp merged with fromAugment | fromExisting
  · exact fromAugment
  · exact absurd (List.mem_filter.mp fromExisting).2 (by simp [named])

/-! ## An annotation the endpoint does not understand is not acted upon

`delivery-annotations.u1`: "if the recipient does not understand the annotation it cannot be acted
upon and its effects (such as any implied propagation) cannot be acted upon." The one place this
layer acts on an annotation's *value* is the reserved key whose value the artifact types, and the
key rule gates it. -/

/-- **A refused annotation key refuses the pair before any value is read.** The key rule runs
first, so a key this endpoint does not understand decides the outcome of the pair on its own: the
value beside it cannot change it, which is what "cannot be acted upon" means for a reader. The
value is a parameter of the statement and appears nowhere in the conclusion, which is the
non-interference the sentence asks for. -/
theorem refusedAnnotationKeyRefusesThePair (kind : SectionKind) (policy : Policy) (key value : Value)
    (reason : Refusal) (refused : checkAnnotationKey policy key = .error reason) :
    ∃ reason' : Refusal, checkAnnotationPair kind policy (key, value) = .error reason' := by
  refine ⟨reason, ?_⟩
  unfold checkAnnotationPair
  rw [refused]
  rfl

end SpecAMQP.Proofs.MessageLaws
