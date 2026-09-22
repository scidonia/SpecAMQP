import Spec.Session

/-!
# The session window contract

This file is the planner's acceptance declaration for the session layer's window arithmetic:
the four sites that update the window state, and the condition under which reducing an id into
the serial space agrees with the arithmetic the artifact talks in.

It exists because two of those clauses have no other possible carrier. `session-flow-control.4`
and `.8` write `remote-outgoing-window`, and nothing in either artifact reads it — the
dispositions' own notes record that, and record the consequence: a dropped decrement would
change no verdict, so no vector can witness the clause and a declaration that merely names the
definition does not say what the clause *requires*. A law is the only bearer left, and these
are it.

## The law

The artifact states the updates as sentences rather than formulas — *"it MUST update the
next-incoming-id directly from the next-outgoing-id of the frame"*, *"it MUST update the
remote-outgoing-window directly from the outgoing-window of the frame"*, and the computed form
`remote-incoming-window = next-incoming-id_flow + incoming-window_flow - next-outgoing-id_endpoint`
for the remaining field. Each is a claim about what the corresponding constructor does and about
what it leaves alone, so each is stated as an equation over the constructor and discharged by
unfolding it: nothing here is a theorem that could be false for arithmetic reasons, and the
value of stating them is that the clause's requirement becomes a named obligation rather than a
reading of a definition body.

## What discharges it

The four update laws below, each by `rfl` over the constructor the clause names, and one
arithmetic law that is *not* discharged as a fact about the step because it is a premise rather
than a consequence.

* **Adoption.** A received flow sets `next-incoming-id` from the frame's `next-outgoing-id`,
  adopts `remote-outgoing-window` from the frame's `outgoing-window`, and computes
  `remote-incoming-window` by the formula above. Nothing in those three is derived from this
  endpoint's own view of the peer, which is what "directly from" forbids.
* **A received transfer** increments `next-incoming-id` to the transfer's id plus one and
  decrements `remote-outgoing-window`, leaving the incoming window to policy — the `MAY` the
  artifact leaves open, which the constructor takes as a parameter rather than resolving.
* **A sent transfer** moves `next-outgoing-id` and the remote *incoming* window, and leaves
  `remote-outgoing-window` alone: the field tracks what the peer said, so sending cannot move it.

## What this file deliberately does not claim

* **No completed proof that the peer stays inside the no-wrap condition.** The law below is
  stated with its condition as a hypothesis, because it is one: nothing in this slice proves
  that a peer's ids stay within a window's reach of ours, and the subtraction in
  `afterReceivingFlow` is a plain `Nat` subtraction that truncates at zero — which the artifact's
  own comment reads as the exhausted window rather than a wrapped one. Witnessing these clauses
  is upstream work, as `session-flow-control.4`'s register entry already says.
* **Nothing about how many links a session carries.** `MODEL RESTRICTION: the S4 slice models at
  most one link per session`, and the window state is per session, so a widening of that
  restriction is what would make a per-link window law meaningful.
* **No restatement of the credit gates.** `Contracts/SessionCredit.lean` owns the credit law and
  its three guards; the windows below are the transport-accounting half and are stated without
  reference to it, which is why they can be read and checked on their own.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Session

/-- `session-flow-control.4`, the id half: `next-incoming-id` is set directly from the frame's
`next-outgoing-id`, reduced into the serial space and computed from nothing else. -/
theorem receiving_flow_adopts_next_incoming_id (w : Windows) (frameNextOutgoing frameIncoming
    frameOutgoing : Nat) (frameNextIncoming : Option Nat) :
    (w.afterReceivingFlow frameNextOutgoing frameIncoming frameOutgoing frameNextIncoming).nextIncomingId
      = frameNextOutgoing % serialModulus := rfl

/-- `session-flow-control.4`, the window half: `remote-outgoing-window` is adopted from the
frame's `outgoing-window` rather than computed, which is what "directly from" requires. -/
theorem receiving_flow_adopts_remote_outgoing_window (w : Windows) (frameNextOutgoing
    frameIncoming frameOutgoing : Nat) (frameNextIncoming : Option Nat) :
    (w.afterReceivingFlow frameNextOutgoing frameIncoming frameOutgoing frameNextIncoming).remoteOutgoingWindow
      = frameOutgoing := rfl

/-- `session-flow-control.4`, the computed field: `remote-incoming-window` is the frame's
`next-incoming-id` plus its `incoming-window`, less this endpoint's `next-outgoing-id`, reduced
into the serial space — with the frame's `next-incoming-id` taken as this endpoint's
`initial-outgoing-id` when the frame does not set it. -/
theorem receiving_flow_computes_remote_incoming_window (w : Windows) (frameNextOutgoing
    frameIncoming frameOutgoing : Nat) (frameNextIncoming : Option Nat) :
    (w.afterReceivingFlow frameNextOutgoing frameIncoming frameOutgoing frameNextIncoming).remoteIncomingWindow
      = ((frameNextIncoming.getD w.initialOutgoingId + frameIncoming) % serialModulus)
          - w.nextOutgoingId := rfl

/-- `session-flow-control.5`: a received transfer increments `next-incoming-id` to the transfer's
id plus one and decrements `remote-outgoing-window`, which is the field this contract exists to
carry. -/
theorem receiving_transfer_decrements_remote_outgoing_window (w : Windows) (transferId : Nat)
    (policy : Bool) :
    (w.afterReceivingTransfer transferId policy).remoteOutgoingWindow
      = w.remoteOutgoingWindow - 1 := rfl

/-- `session-flow-control.6`, stated as the constraint it is: sending cannot move the field that
tracks the peer's own announcement. -/
theorem sending_transfer_leaves_remote_outgoing_window (w : Windows) (policy : Bool) :
    (w.afterSendingTransfer policy).remoteOutgoingWindow = w.remoteOutgoingWindow := rfl

/-- The no-wrap condition, and the only law here that is arithmetic rather than definitional:
while a value is below the modulus, reducing it into the serial space is the identity, so the
plain subtraction in `afterReceivingFlow` is the true difference between the peer's announced
ids and ours. Past it the reduction wraps, the subtraction truncates at zero, and the window
reads as exhausted — which is a boundary the layer carries as a premise rather than proves. -/
theorem reduction_below_the_modulus_is_the_identity (x : Nat) (h : x < serialModulus) :
    x % serialModulus = x :=
  Nat.mod_eq_of_lt h

end SpecAMQP.Contracts
