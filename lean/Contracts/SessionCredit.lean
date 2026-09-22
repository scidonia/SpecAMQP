import Spec.Session

/-!
# The session credit contract

This file is the planner's acceptance declaration for the session layer's flow-control law.
It states the one property of a *state* that the layer's three outcome guards exist to
preserve, and it says what would discharge it.

## The law

The artifact gives the law as a definition rather than an obligation, in `flow`'s
`link-credit` and the link section's ownership sentences: *"Only the receiver endpoint can
independently set this value. The sender endpoint sets this to the last known value seen
from the receiver"*, and in the link section the same rule three more times over the
per-link flow variables — *"Only the receiver can independently choose a value for this
field"*, *"Only the sender can independently modify this field"*, *"Only the receiver can
independently modify this field"*. The doc's own formula for the sender's variable is

    link-credit_snd := delivery-count_rcv + link-credit_rcv - delivery-count_snd

which is `Position.creditFor`. So a sender's credit is not a quantity it maintains; it is
whatever the receiver's pair leaves room for, and the state below says exactly that: after
every operation the two sides agree about, the sender's credit still equals the equation
its own receiver-facing constructor computes.

## What discharges it

Five obligations: the initial state, the framing case for every operation that touches none of the four quantities, and one each for `attachLink`, `flowLink` and `transferLink`. The first two are discharged in `Proofs/SessionCredit.lean`; the last three are named there and not proved:

* **Initialisation.** At `attach`, `peerCount` and `peerCredit` are both zero, so the
   right side is `0 + 0 - initialDeliveryCount`, which truncates to zero — the state where
   a sender has nothing to spend until the receiver grants credit, which is the ownership
   sentence applied at the moment the link exists.
* **Preservation, per transition.** A received flow *sets* the equation, because the
   credit is built by `Position.creditFor` from the values that flow reported. A transfer
   *preserves* it, because both sides move by one: the credit decrements and the
   delivery-count increments, so the right side loses exactly what the left side does —
   and the credit gate is what makes the truncated subtraction agree rather than wrap,
   since a transfer with no credit left is refused before it can move either side.

## What this file deliberately does not claim

* **The three outcome guards are scenarios, not state laws.** `delivery-count.2` (a flow
  this endpoint sends carries its own current count), `delivery-count.3` (a flow received
  carries the count this endpoint's view holds) and the ownership refusal (a sender's flow
  whose `link-credit` differs from the credit this receiver last sent) are conditions
  inside the step function, observable as refused-versus-admitted and carried by the
  exchange corpus. Restating them here would add a description written from the code rather
  than from the artifact — which is how a check decays into a restatement.
* **The receiver side has no state law, and dressing one up would be claiming the guard.**
  The receiver's credit is its own quantity, so a flow it receives never moves it and the
  ownership guard's content is outcome-shaped however it is worded: the flow is refused, or
  it was admitted with this endpoint's credit untouched and the echo equal to it.
* **`available` and `drain` are outside this contract.** `available` is advisory and the
  model holds no sender-side quantity for a receiver to echo; `drain`'s direction-dependent
  meaning (actual mode sender to receiver, desired mode receiver to sender) is not modelled
  because nothing in the slice reads it. Both are recorded in the plan as scope rather than
  approximated here.

## Status

The law is **stated, and true by construction rather than proved**. `lean/Proofs/SessionCredit.lean`
carries `SenderCreditState` restated on the specification's own `Session` so the proof and the
constructor cannot drift apart, and discharges two of the five obligations: the initial state
(`initial_sender_credit`, where both clauses are vacuous because there is no link and no role) and
every operation that leaves `role`, `position`, `peerCount` and `peerCredit` where they were
(`frame_sender_credit`). The three that move the quantities are **not proved** — `attachLink` (which
sets both sides of the equation to zero), `flowLink` (whose sender's branch rebuilds the credit with
`Position.creditFor`) and `transferLink` (whose delivery-beginning transfer decrements the credit and
increments the delivery-count) — and the proof module names them rather than sketching them.

**So this file carries no acceptance theorem, and that is the state of the art rather than an
oversight**: a declaration taking a name that does not exist would be a claim nobody can defend.
When the three lemmas land, the declaration goes here, taking the conjunction of the five.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Session

/-- **The sender's credit law, in the form the induction needs.** Two clauses:

* the equation — in a state where this endpoint attached as the link's sender and a flow
  state exists, that state's credit is exactly what the receiver's last reported pair leaves
  room for: `Position.creditFor` of the peer's delivery-count and credit against this
  endpoint's own delivery-count, stated through the specification's own constructor so the
  two cannot drift apart. Read as the artifact's ownership sentence: an endpoint never
  invents the partner's quantity, and a sender never invents its own credit.
* the absence clause — an endpoint with no flow state has agreed nothing about the partner's
  quantities either: `position = none → peerCount = 0 ∧ peerCredit = 0`.

**The second clause is not decoration and the first alone is not the law to state.** The
equation is vacuous while `position` is `none` — its quantifier ranges over nothing, so it
constrains neither `peerCount` nor `peerCredit` — and those are exactly the quantities an
`attach` needs to be zero for the credit it sets to satisfy the equation. An invariant whose
interesting case is the one it cannot see would be a claim that holds for the wrong reason.
So the stated form is the one the induction actually preserves, and the equation is its
first clause. -/
def SenderCreditState (session : Session) : Prop :=
  (session.role = some LinkRole.sender →
    ∀ position, session.position = some position →
      position.credit =
        Position.creditFor session.peerCount session.peerCredit position.deliveryCount) ∧
  (session.position = none → session.peerCount = 0 ∧ session.peerCredit = 0)

end SpecAMQP.Contracts
