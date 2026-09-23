import Spec.Transactions

/-!
# The transaction layer's acceptance propositions

`PLAN.md` §13 names the transaction layer's criterion as **the declared/discharged state machine proved**.
This module states what that machine claims and records the obligation plainly: the machine is
*implemented* in `Spec.Transactions`, and **no theorem asserts anything about it yet**. The propositions
below are therefore stated and not claimed — the same treatment the message layer's round trip gets, and
for the same reason: a contract states the claim, and asserting it with `sorry` would be a claim.

## Why there is nothing to re-export

The message layer's contract re-exports two theorems because they exist. Nothing here corresponds: the
transaction layer's lifecycle is written, its refusals are wired to the conditions the artifact names,
and its corpus passes on both artefacts — but every law below is a claim about a function that no proof
has yet been written against. That is what §13's amendment means by the milestone's remaining obligation,
and stating it here is how a reader learns it without reading the transcript.

## What the machine does, read from the code rather than paraphrased

* `declare` refuses a settled declare and a `global-id` without the coordinator's announced capability,
  then — as the coordinator — records the id it holds next as undischarged and advances the counter.
  As the controller it allocates nothing, because the id is the resource's to give.
* `discharge` refuses a settled discharge, and retires the named transaction **before** consulting the
  register when the `fail` flag is set: the artifact states that the coordinator must always be able to
  complete a `fail=true` discharge, so the liveness check is the branch that flag skips.
* `declared` is the outcome that teaches the id to the end that asked for it, which is what makes the id
  dischargeable at all.
* `retireAll` retires every transaction the control link created, which is the clause the census's third
  extension captured and this layer then enforced.
* `step` refuses a transaction composite that arrives as a *message* rather than as a disposition's state,
  because the same value means different things in the two frames.

## What this file deliberately does not claim

* **Disposition outcomes are the link layer's.** `declared`'s arrival is modelled as the layer transition
  it is, but the frames that carry it — a `disposition` in the outcome state, a rejected outcome, a detach
  with a transaction-error — belong to the link layer, so the corpus pins the condition and not the frame.
* **The 21 `txn-work` clauses are not this machine's.** Posting, acquiring and retiring a delivery are the
  delivery-state layer's semantics; this machine carries the transactional-state composite and nothing
  about what a resource does with it.
* **`txn-work.9`'s link-capability input has no source in the model**, so its `amqp-error` is stated in the
  ledger as unenforced rather than approximated here.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Transactions

/-- A result refuses with a named condition and class. The two are separate fields on purpose: the
artifact mandates the code and the corpus pins the class, and a refusal that named the wrong one of either
would be a different claim about the wire. -/
def RefusesWith {α : Type} (result : Except Refusal α) (condition reasonClass : String) : Prop :=
  ∃ refusal : Refusal,
    result = .error refusal ∧ refusal.condition = condition ∧ refusal.reasonClass = reasonClass

/-- **A coordinator's declare allocates the id it holds next.**

The call's success carries the guards it passed, so this needs no precondition of its own: if `declare`
returned the layer, then the declare was unsettled and any `global-id` it carried was covered by the
coordinator's announced capabilities, and what follows is what it did to the register. -/
def DeclareAllocates (layer : Layer) (_globalId : Bool) (assigned : Layer) : Prop :=
  assigned.nextId = layer.nextId + 1 ∧
  assigned.transactions = ⟨layer.nextId, false⟩ :: layer.transactions

/-- **A settled declare is refused as an illegal state**, whichever end sends it. The artifact requires
the sender to receive and interpret the outcome, which a settled declare makes impossible. -/
def DeclareSettledRefused (layer : Layer) (outbound globalId : Bool) : Prop :=
  RefusesWith (declare layer outbound globalId true) illegalStateCondition "illegalState"

/-- **A `global-id` declare is refused as an invalid field** when the coordinator's announced
capabilities for this control link do not include distributed transactions. -/
def DeclareGlobalIdRefused (layer : Layer) (outbound : Bool) : Prop :=
  RefusesWith (declare layer outbound true false) invalidFieldCondition "malformed"

/-- **A settled discharge is refused as an illegal state**, as the declare is. -/
def DischargeSettledRefused (layer : Layer) (txnId : Nat) (fail : Bool) : Prop :=
  RefusesWith (discharge layer txnId fail true) illegalStateCondition "illegalState"

/-- **A `fail=true` discharge completes whatever the register holds.**

This is the clause whose unconditional wording the machine follows by retiring before it consults
liveness, and it is a law about a function rather than a remark: a coordinator whose rollback arrives
after the id was retired is exactly the case the sentence exists for. -/
def FailDischargeCompletes (layer : Layer) (txnId : Nat) : Prop :=
  ∃ retired : Layer, discharge layer txnId true false = .ok retired

/-- **A discharge naming an id this endpoint does not hold is refused as an unknown id**, when it is not
a `fail=true` completion. -/
def DischargeUnknownIdRefused (layer : Layer) (txnId : Nat)
    (_dead : layer.live txnId = false) : Prop :=
  RefusesWith (discharge layer txnId false false) unknownId "illegalState"

/-- **Retiring the control link retires every transaction it created**, which is the clause the census
extension captured and this layer enforced. -/
def RetireAllRetiresEverything (layer : Layer) : Prop :=
  (layer.retireAll).transactions = layer.transactions.map Transaction.retired

/-- **A transaction composite carried as a message is refused.**

The same value means different things in a transfer's payload and in a disposition's state, so the
refusal is about the carrier and not about the value: a `declare` or a `discharge` arriving on the payload
channel is the work the control-link sentence forbids, while the outcome composites arrive the other way.
The condition is the one `notTheControlDialogue` raises, which is the artifact's own `illegal-state` — the
condition for input its rules do not admit at the moment it arrives, since no clause names one for this
sentence. -/
def MessageCarriedWorkRefused (layer : Layer) (outbound settled : Bool)
    (value : SpecAMQP.Spec.Codec.Value) : Prop :=
  (Performative.ofValue value = .declare ∨ Performative.ofValue value = .discharge) →
    ∃ refusal : Refusal,
      step layer .payload outbound value settled = .error refusal ∧
      refusal.condition = illegalStateCondition

end SpecAMQP.Contracts
