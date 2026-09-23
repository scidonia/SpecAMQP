import Spec.Session

/-!
# The session window contract: the arithmetic, its citations, and the violation rule

This file is the planner's acceptance declaration for the session layer's window rules, and it is
the one carrier of them. It replaces the earlier `Contracts/SessionWindows.lean`, for the reason
the plan's own rule gives: a corrected claim *replaces* the claim it corrects, and a second copy
of the same arithmetic carrying a different citation is worse than an absent one, because a
reader would reasonably trust it. The laws below are that file's laws, moved here, with the
citations they should always have had — the earlier file attributed the received-flow adoption to
the fragment `session-flow-control.4`, which is the received-*transfer* sentence, and the received-transfer
decrement to `amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.5`, which is the *sending* transfer's.

## The citation convention

Every clause this file cites is a registered id from `ledger/clauses.json`, written in full: the
artifact, then the anchor, then the clause index —

    amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.7

Nothing here cites `section:session-flow-control`, or a fragment such as `session-flow-control.7`,
or any other derived spelling. The section-level spelling names an *area* and resolves against no
clause at all — the corpus's citations were checked for exactly this and 163 stale ones were found
the same way — and a fragment is not the id the ledger carries. Where a rule has no registered
clause this file says so and states the rule as a *reading* rather than decorating it with the
nearest anchor; the disposition fields are the standing example elsewhere in this directory, and
two of the window rules are the example here, below.

## The law

The artifact states the window updates as sentences rather than formulas — *"it MUST update the
next-incoming-id directly from the next-outgoing-id of the frame"*, *"it MUST update the
remote-outgoing-window directly from the outgoing-window of the frame"*, and the computed form
`remote-incoming-window = next-incoming-id_flow + incoming-window_flow - next-outgoing-id_endpoint`
for the remaining field, all at
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.7`. Each
is a claim about what the corresponding constructor does and about what it leaves alone, so each
is stated as an equation over the constructor and discharged by unfolding it: nothing in the
proved half is a theorem that could be false for arithmetic reasons, and the value of stating them
is that the clause's requirement becomes a named obligation rather than a reading of a definition
body.

The register's adopted reading of the rules that are *not* sentences is
`ledger/ambiguities/session-window-violation.json`, whose clause list is `.3`, `.5`, `.6`, `.7` and
`.8` of that doc — the five window clauses — and whose adopted reading has two halves no clause
states:

* a transfer that would exceed either window is refused with the `session-error` family's
  `window-violation` and the `limit` class, because the windows are declared bounds and the rule
  follows from the definitions rather than from a clause that raises it;
* the `remote-incoming-window` recomputation's subtraction **truncates at zero** rather than
  wrapping, so an exhausted window fails the next send loudly instead of admitting exactly the
  transfers the window exists to refuse.

Both are stated below as propositions over the specification's own step function. Neither is
proved, and the file says which is which rather than leaving a reader to infer it from a theorem's
presence.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Session
open SpecAMQP.Spec.Connection
  (fieldValue fieldSet invalidField missingMandatory valueNat)
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Harness (Octets)

/-! ## Adoption: what a received flow does to the three fields it is about

`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.7` is one
sentence carrying two obligations — `next-incoming-id` "directly from the `next-outgoing-id` of the
frame", and `remote-outgoing-window` "directly from the `outgoing-window` of the frame" — plus a
computed form for the third field. "Directly from" is the load-bearing phrase: neither field may be
derived from this endpoint's own view of the peer, and the endpoint's own `next-outgoing-id` may
not enter either. -/

/-- The id half of
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.7`:
`next-incoming-id` is set from the frame's `next-outgoing-id`, reduced into the serial space and
computed from nothing else. -/
theorem receiving_flow_adopts_next_incoming_id (w : Windows) (frameNextOutgoing frameIncoming
    frameOutgoing : Nat) (frameNextIncoming : Option Nat) :
    (w.afterReceivingFlow frameNextOutgoing frameIncoming frameOutgoing
      frameNextIncoming).nextIncomingId = frameNextOutgoing % serialModulus := rfl

/-- The window half of the same clause: `remote-outgoing-window` is adopted from the frame's
`outgoing-window` rather than computed, which is what "directly from" requires. -/
theorem receiving_flow_adopts_remote_outgoing_window (w : Windows) (frameNextOutgoing
    frameIncoming frameOutgoing : Nat) (frameNextIncoming : Option Nat) :
    (w.afterReceivingFlow frameNextOutgoing frameIncoming frameOutgoing
      frameNextIncoming).remoteOutgoingWindow = frameOutgoing := rfl

/-- The computed field of the same clause: `remote-incoming-window` is the frame's
`next-incoming-id` plus its `incoming-window`, less this endpoint's `next-outgoing-id`, reduced
into the serial space. -/
theorem receiving_flow_computes_remote_incoming_window (w : Windows) (frameNextOutgoing
    frameIncoming frameOutgoing : Nat) (frameNextIncoming : Option Nat) :
    (w.afterReceivingFlow frameNextOutgoing frameIncoming frameOutgoing
      frameNextIncoming).remoteIncomingWindow
      = ((frameNextIncoming.getD w.initialOutgoingId + frameIncoming) % serialModulus)
          - w.nextOutgoingId := rfl

/-- The clause's unset branch, which the ledger carries separately at
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.u1` — "If
the next-incoming-id field of the «flow» frame is not set, then remote-incoming-window is computed
as follows" — and which the computed form above folds into one expression. Stated on its own
because the two branches are two readings of one formula, and a constructor that took the wrong one
would satisfy the equation above while computing the window from the wrong id. -/
theorem receiving_flow_without_a_next_incoming_id_uses_the_initial_outgoing_id (w : Windows)
    (frameNextOutgoing frameIncoming frameOutgoing : Nat) :
    (w.afterReceivingFlow frameNextOutgoing frameIncoming frameOutgoing
      none).remoteIncomingWindow
      = ((w.initialOutgoingId + frameIncoming) % serialModulus) - w.nextOutgoingId := rfl

/-! ## A received transfer

`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.6` is the
receiving half of the pair: the endpoint "will increment the next-incoming-id to match the implicit
transfer-id of the incoming transfer plus one, as well as decrementing the remote-outgoing-window,
and MAY (depending on policy) decrement its incoming-window". All three are stated, including the
MAY, because the MAY is latitude the constructor takes as a parameter rather than resolving. -/

/-- The id half: the next expected transfer-id is the one just received plus one. -/
theorem receiving_transfer_increments_next_incoming_id (w : Windows) (transferId : Nat)
    (policy : Bool) :
    (w.afterReceivingTransfer transferId policy).nextIncomingId
      = (transferId + 1) % serialModulus := rfl

/-- The window half, with the clause that gives the field its meaning:
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.4` — "This
value MUST be decremented after every incoming «transfer» frame is received, and recomputed when
informed of the remote session endpoint state" — the field the earlier contract cited at the wrong
index, and the one clause of the five that nothing in either artifact reads, which is why a law is
its only possible carrier. -/
theorem receiving_transfer_decrements_remote_outgoing_window (w : Windows) (transferId : Nat)
    (policy : Bool) :
    (w.afterReceivingTransfer transferId policy).remoteOutgoingWindow
      = w.remoteOutgoingWindow - 1 := rfl

/-- The clause's MAY, kept as the latitude it is: the endpoint's own incoming window shrinks
exactly when the policy says so, and the constructor cannot silently choose. -/
theorem receiving_transfer_decrements_incoming_window_under_policy (w : Windows)
    (transferId : Nat) :
    (w.afterReceivingTransfer transferId true).incomingWindow = w.incomingWindow - 1 ∧
      (w.afterReceivingTransfer transferId false).incomingWindow = w.incomingWindow :=
  ⟨rfl, rfl⟩

/-! ## A sent transfer

`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.5` —
"Upon sending a transfer, the sending endpoint will increment its next-outgoing-id, decrement its
remote-incoming-window, and MAY (depending on policy) decrement its outgoing-window" — and
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.2` gives
the first of those its obligation: remote-incoming-window "MUST be decremented after every
«transfer» frame is sent, and recomputed when informed of the remote session endpoint state". The
field this pair does **not** move is `remote-outgoing-window`, which tracks the peer's own
announcement and is therefore the one quantity a send cannot touch. -/

/-- `amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.5` and
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.2`: a sent transfer spends one unit of the
peer's incoming window. -/
theorem sending_transfer_decrements_remote_incoming_window (w : Windows) (policy : Bool) :
    (w.afterSendingTransfer policy).remoteIncomingWindow = w.remoteIncomingWindow - 1 := rfl

/-- `amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.5` with
`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.1`: `next-outgoing-id` is "incremented
after each successive «transfer» according to RFC-1982 serial number arithmetic", which is the
reduction into the serial space. -/
theorem sending_transfer_increments_next_outgoing_id (w : Windows) (policy : Bool) :
    (w.afterSendingTransfer policy).nextOutgoingId
      = (w.nextOutgoingId + 1) % serialModulus := rfl

/-- `amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.5`: sending cannot move the field that tracks the peer's own
announcement. The clause states it by omission, and it is the constraint a sender most easily gets
wrong, so it is stated here rather than left to the definition body. -/
theorem sending_transfer_leaves_remote_outgoing_window (w : Windows) (policy : Bool) :
    (w.afterSendingTransfer policy).remoteOutgoingWindow = w.remoteOutgoingWindow := rfl

/-! ## The serial space, and the premise the arithmetic carries

`amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.1` makes
the transfer numbers RFC-1982 serial numbers. The no-wrap condition is a *premise* rather than a
consequence: nothing in this slice proves that a peer's ids stay within a window's reach of ours,
and the subtraction in `afterReceivingFlow` is a plain `Nat` subtraction that truncates at zero —
which the register's reading takes as the exhausted window rather than a wrapped one. -/

/-- While a value is below the modulus, reducing it into the serial space is the identity, so the
plain subtraction in `afterReceivingFlow` is the true difference between the peer's announced ids
and ours. Past it the reduction wraps and the subtraction truncates at zero, which reads as an
exhausted window — a boundary the layer carries as a premise rather than proves. -/
theorem reduction_below_the_modulus_is_the_identity (x : Nat) (h : x < serialModulus) :
    x % serialModulus = x :=
  Nat.mod_eq_of_lt h

/-! ## Stated, and not proved

The two halves of the register's reading, each stated over the specification's own step function
rather than over a paraphrase of it, so that a reader can tell what is being claimed and a proof
module has something exact to discharge. Both are obligations of the same shape as the credit
contract's three: a `do`-block whose guards must be inverted from a successor hypothesis, which no
theorem in `Proofs/` does for the windows yet. -/

/-- **A frame that would exceed the outgoing window is refused.** `Session.step` checks it before
it reads the transfer's own fields and before any link rule, so the obligation is about the window
and nothing else: in a session that may send, on the channel that session sends on, carrying a
transfer whose mandatory fields are present, an exhausted `outgoingWindow` is a refusal whose
condition is the `session-error` family's `window-violation`.

Stated rather than proved. The class the refusal carries is `limit` — the same class the DOFF field
and the declared-form refusals use, because a window is a value outside a declared bound — which is
the register's adopted reading and not a citation, since no clause raises this condition. -/
def TransfersBeyondTheOutgoingWindowAreRefused : Prop :=
  ∀ (session : Session) (channel : Nat) (body : Value) (payload : Octets),
    session.state = State.mapped →
    session.outgoing = some channel →
    Performative.ofBody body = Performative.transfer →
    missingMandatory "transfer" body = [] →
    session.windows.outgoingWindow = 0 →
    ∃ reason : Refusal,
      step session true channel body payload = .error reason ∧
        reason.condition = windowViolation

/-- **A frame that would exceed the incoming window is refused.** The receiving half of the same
rule, stated separately because the two windows belong to different peers: a sender overrunning the
window *this* endpoint announced is input this endpoint cannot process, so the refusal is the one
the section mandates for that — the state moves to `DISCARDING` — and the condition is still the
window's. -/
def TransfersBeyondTheIncomingWindowAreRefused : Prop :=
  ∀ (session : Session) (channel : Nat) (body : Value) (payload : Octets),
    session.state = State.mapped →
    session.incoming = some channel →
    Performative.ofBody body = Performative.transfer →
    missingMandatory "transfer" body = [] →
    session.windows.incomingWindow = 0 →
    ∃ reason : Refusal,
      step session false channel body payload = .error reason ∧
        reason.condition = windowViolation

/-- **The windows do not wrap.** An endpoint whose own `next-outgoing-id` has passed the peer's
announced reach reads an exhausted window — zero — rather than a wrapped one. This is the second
half of the register's reading, and the half a reader of the definition body alone would most
easily get wrong, since the arithmetic the artifact writes *is* serial-number arithmetic and
wrapping is what that arithmetic does for ids. -/
def ExhaustedWindowsDoNotWrap (w : Windows) (frameNextOutgoing frameIncoming frameOutgoing :
    Nat) : Prop :=
  w.nextOutgoingId > (w.initialOutgoingId + frameIncoming) % serialModulus →
    (w.afterReceivingFlow frameNextOutgoing frameIncoming frameOutgoing none).remoteIncomingWindow
      = 0

/-! ## What this file deliberately does not claim

* **No completed proof that the peer stays inside the no-wrap condition.**
  `reduction_below_the_modulus_is_the_identity` is stated with its condition as a hypothesis
  because it is one: nothing in this slice proves that a peer's ids stay within a window's reach of
  ours. Witnessing these clauses is upstream work, as
  `amqp-core-transport-v1.0-os.xml#amqp:transport/section:sessions/doc:session-flow-control.4`'s
  register entry already says.
* **Nothing about how many links a session carries.** `MODEL RESTRICTION: the S4 slice models at
  most one link per session`, and the window state is per session, so a widening of that
  restriction is what would make a per-link window law meaningful.
* **No restatement of the credit gates.** `Contracts/SessionCredit.lean` owns the credit law and its
  three guards; the rules here are the transport-accounting half and are stated without reference to
  it, which is why they can be read and checked on their own.
* **`drain` and `echo` are not window state.**
  `amqp-core-transport-v1.0-os.xml#amqp:transport/section:links/doc:flow-control.8` makes `drain` a
  hint about how the sender SHOULD behave and
  `amqp-core-transport-v1.0-os.xml#amqp:transport/section:performatives/type:flow/field:echo.1`
  makes `echo` a request for the peer's state; neither moves any of the seven quantities above, and
  their model sites are the link's, in `Spec.Session.flowLink`.
-/

end SpecAMQP.Contracts
