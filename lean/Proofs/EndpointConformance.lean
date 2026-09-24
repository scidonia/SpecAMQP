import Contracts.EndpointConformance
import Impl.Core
import Proofs.ConnectionConformance

/-!
# R3: the endpoint's protocol core conforms

`Contracts.EndpointConformance` freezes the claim — `ConformsVia (fun s i => i.conn = s)
specConn implCore` — and this module proves it. `PLAN.md` §23.1 is the rung; the statement's own module
is where the reasons for its three names are recorded, and they are not repeated here.

## What is actually being proved, and why it is not a restatement

The core is a *driver* over `Spec.Connection.step`: it does not restate one rule of the connection
layer, it calls it. So nothing in this proof is about a protocol decision — a state table row, a
negotiation, a SASL stage, a limit — because there is no second decision procedure to compare against
the first. What the core owns is the *plumbing*, and what this theorem says is that the plumbing the
core writes and the plumbing the specification's own endpoint writes (`Proofs/ConnectionConformance`,
where `specConn` lives) are the same plumbing:

* which field of the interface's `Input` goes to which direction of the layer (`arriving` and
  `sending`);
* how the layer's `Except Refusal Outcome` becomes the interface's `(state, List Output)`: the octets
  the step wrote, in order, then the answer (`answerOf`);
* the api reading: which call is a send, and how its octets become a `Submission`
  (`submissionOf`).

That value is not decorative. The core may not import the proof library (`AGENTS.md`: `Proofs/` is
where proofs live, `Impl/` is what ships), so the three renderings and the two readings are written
*separately* in `Impl/Core.lean`, and a difference between the two copies — a mis-ordered `++`, a
refusal placed at the wrong state, a branch taken on the opposite test — is exactly the class of defect
that a proof of this shape catches and that no protocol theorem would. The four equalities below are
the whole of that comparison, and each is a named lemma rather than an inline `rfl` so that a later
refactor of either copy fails here instead of silently changing what the endpoint answers.

Two of the four close by unfolding alone. The other two do not, for reasons that are facts about the
two modules rather than about the plumbing: `submissionOf` is written as `(callOctets call).bind
readSubmission` on the implementation's side and as a `match` on the specification's, and
`callOctets`' ok branch reads `(ofHex arg).toOption` on one side against an explicit `match` on the
other — `Except.toOption` is opaque to the elaborator's default transparency, so the agreement is
closed by a case split over the call's arguments and over the decoder's answer rather than by `rfl`.
Every case is the same case on both sides; there is no input where they disagree.

## The relation, the initial state, and the alphabet

`R` is `fun s i => i.conn = s`, so a related pair is *the same connection endpoint* — the relation does
not weaken, it identifies. `inbox` is deliberately outside it: `step` neither reads nor writes that
field, which is what the proof below shows case by case (the successor it exhibits is `out.1.conn`, and
`out.1` is the implementation's own state with its inbox untouched).

The alphabet is closed by a case split over `Input`: a frame is the layer's receive direction, a
readable call is its send direction, a tick is `none` on both sides. Each case *exhibits* the
specification's permitted step rather than appealing to a fixed point: `specConn.choose` is the
singleton of `specConnStep`, so the exhibited pair is the layer's own answer under the same equality,
and the two output clauses are then the same equality read at the state and at the list.

## What is not here

The stream corollary — that feeding a byte stream in one read equals feeding it in two — is the front
end's and rests on a residual recorded in `Proofs/CoreLaws.lean`, so it is not stated or used here.
Nothing in this module says anything about the socket boundary, about the shell that drives this core,
or about whether the connection layer's own decisions are the standard's; the first two are outside
`Conforms`'s alphabet and the third is the differential's and the corpus's business.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Contracts (ApiCall Input Output)
open SpecAMQP.Harness (Octets)

/-! ## The octets, and the api call both endpoints read

The interface carries the wire as `ByteArray` and the layer carries it as `Octets`; both modules convert
with the same pair, and the pair is what this lemma says. It is the whole of what the proof needs of the
conversion, and it needs no round trip: the two `toOctets`s are one function written twice, so an input's
octets are one term on both sides rather than two functions' results that would then have to be related. -/

/-- The implementation's octet conversion *is* the specification's: both are `ByteArray.data`. -/
theorem toOctets_agrees (bytes : ByteArray) :
    SpecAMQP.Impl.Core.toOctets bytes = toOctets bytes := rfl

/-- The octets a call asks for, as the two endpoints read them out of it.

`rfl` does not close this on its own — `Except.toOption` is opaque to the elaborator's default
transparency, so `(ofHex arg).toOption` against an explicit `match` needs the decoder's answer to be
named before the two branches are seen to be the same branch. Both sides test the same name and read
the same first argument with the same decoder, and each of the three cases below is one case on both
sides. -/
theorem callOctets_agrees (call : ApiCall) :
    SpecAMQP.Impl.Core.callOctets call = callOctets call := by
  unfold SpecAMQP.Impl.Core.callOctets SpecAMQP.Proofs.callOctets
  simp only [SpecAMQP.Impl.Core.sendName, SpecAMQP.Proofs.sendName]
  cases call.arguments with
  | nil => rfl
  | cons arg rest =>
    by_cases h : call.name = "send"
    · simp only [if_pos h]
      cases hx : SpecAMQP.Harness.ofHex arg with
      | ok octets => rfl
      | error message => rfl
    · simp only [if_neg h]

/-! ## The four plumbing equalities

Each lemma names one construction the two modules write separately and says the two writings are one
function. The order below is the order the claim descends through them: the api reading, then the two
directions, then the rendering both directions end in. -/

/-- **The api reading.** A call is a send of the octets it names, read the same way by both endpoints:
the same call is readable, and a readable call names the same `Submission`.

The implementation writes the reading as `(callOctets call).bind readSubmission`, with the two branches
(header-shaped octets are a header, everything else is a frame) inside `readSubmission`; the
specification writes one `match` with the same two branches in it. That is the case split below: the
call either names octets or it does not, and octets that are header-shaped are read as a header
whichever side reads them. -/
theorem submissionOf_agrees (call : ApiCall) :
    SpecAMQP.Impl.Core.submissionOf call = specSubmissionOf call := by
  unfold SpecAMQP.Impl.Core.submissionOf SpecAMQP.Proofs.specSubmissionOf
  rw [callOctets_agrees]
  cases h : callOctets call with
  | none => rfl
  | some octets =>
    unfold SpecAMQP.Impl.Core.readSubmission
    cases hh : SpecAMQP.Spec.Connection.headerShaped octets with
    | false => rfl
    | true => rfl

/-- **The receive direction.** One buffer offered to the connection layer: the same `arriving` call in
the same direction, rendered the same way. -/
theorem arriving_agrees (conn : SpecAMQP.Spec.Connection.Endpoint) (octets : Octets) :
    SpecAMQP.Impl.Core.arriving conn octets = specArriving conn octets := rfl

/-- **The send direction.** One submission this peer is asked to send: the same `sending` call in the
same direction, rendered the same way. That this is a *different* lemma from `arriving_agrees` is the
point — the direction is the one thing a step of this layer is told rather than decides, so a copy that
passed the wrong one would agree with itself and not with the other endpoint. -/
theorem sending_agrees (conn : SpecAMQP.Spec.Connection.Endpoint)
    (submission : SpecAMQP.Spec.Connection.Submission) :
    SpecAMQP.Impl.Core.sending conn submission = specSending conn submission := rfl

/-- **The rendering.** The layer's `Except Refusal Outcome` as the interface's pair: on an admitted
step the endpoint it left and the octets it wrote followed by the state table's own name for the step;
on a refusal the state the refusal places the peer in, and the octets it wrote while refusing followed
by the protocol condition and the reason class.

The order of the list is part of the claim — `Conforms` compares output sequences, not sets — so a copy
that emitted the answer before the wire, or placed the refusal at the state it was handed rather than
the one the refusal names, is a copy this lemma refuses. -/
theorem answerOf_agrees (conn : SpecAMQP.Spec.Connection.Endpoint)
    (answer : Except SpecAMQP.Spec.Connection.Refusal SpecAMQP.Spec.Connection.Outcome) :
    SpecAMQP.Impl.Core.answerOf conn answer = specAnswerOf conn answer := rfl

/-! ## The instance -/

/-- **The endpoint's protocol core conforms to the specification's connection endpoint.**

The relation is `fun s i => i.conn = s`: the implementation's connection field *is* the specification's
endpoint state, so the initial states are related because they are the same state, and each input is
matched by the layer's own step under `arriving_agrees` / `sending_agrees` / `submissionOf_agrees`.

Every case is the same shape. The implementation's answer is unfolded to the layer's own pair (with its
inbox carried along and untouched), the plumbing equalities turn that pair into the specification's
`Arriving`/`Sending` answer, and the exhibited successor is that pair's state and output list — which is
a permitted step because `specConn.choose` is exactly `specConnStep`'s singleton, so the membership and
the two conjuncts below are the same equality read three times. The tick case is the one where no
successor exists on either side, and the contradiction is the core's own `none`. -/
theorem endpoint_conforms : SpecAMQP.Contracts.EndpointConforms := by
  refine ⟨?_, ?_⟩
  · -- the initial states: the core's `Conn` field is the layer's initial state, by unfolding
    rfl
  · intro s i inp hR out hstep
    subst hR
    cases inp with
    | frame bytes =>
      -- one buffer, in the receive direction
      have hstep' : SpecAMQP.Impl.Core.step i (Input.frame bytes) = some out := hstep
      rw [SpecAMQP.Impl.Core.step_frame] at hstep'
      simp only [Option.some.injEq] at hstep'
      rw [toOctets_agrees, arriving_agrees] at hstep'
      refine ⟨(specArriving i.conn (toOctets bytes)).1,
        (specArriving i.conn (toOctets bytes)).2, ?_, ?_, ?_⟩
      · rw [specConnection_choose_member]
        show specConn.step i.conn (Input.frame bytes) = some (specArriving i.conn (toOctets bytes))
        simp only [specConn, specConnStep]
      · rw [← hstep']
      · rw [← hstep']
    | api call =>
      -- a call, in the send direction, if it reads as a send at all
      have hstep' : SpecAMQP.Impl.Core.step i (Input.api call) = some out := hstep
      rw [show SpecAMQP.Impl.Core.step i (Input.api call) =
        (SpecAMQP.Impl.Core.submissionOf call).map (SpecAMQP.Impl.Core.send i) from rfl] at hstep'
      rw [submissionOf_agrees] at hstep'
      cases hsub : specSubmissionOf call with
      | none =>
        simp only [hsub, Option.map_none] at hstep'
        exact absurd hstep' (by simp)
      | some submission =>
        simp only [hsub, Option.map_some, Option.some.injEq] at hstep'
        have hsend : SpecAMQP.Impl.Core.send i submission =
            ({ i with conn := (specSending i.conn submission).1 },
              (specSending i.conn submission).2) := by
          unfold SpecAMQP.Impl.Core.send
          rw [sending_agrees]
        rw [hsend] at hstep'
        refine ⟨(specSending i.conn submission).1, (specSending i.conn submission).2, ?_, ?_, ?_⟩
        · rw [specConnection_choose_member]
          show specConn.step i.conn (Input.api call) = some (specSending i.conn submission)
          simp only [specConn, specConnStep, hsub, Option.map_some]
        · rw [← hstep']
        · rw [← hstep']
    | tick t =>
      -- time crosses, and neither endpoint has a timer behind it
      have hstep' : SpecAMQP.Impl.Core.step i (Input.tick t) = some out := hstep
      simp only [SpecAMQP.Impl.Core.step] at hstep'
      exact absurd hstep' (by simp)

end SpecAMQP.Proofs
