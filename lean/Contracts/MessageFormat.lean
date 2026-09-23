import Spec.Message

/-!
# The message layer's acceptance propositions

`PLAN.md` §13 names two criteria for the message layer: that **every section type round-trips**, and
that **the outcome state machine is proved**. This module states the first and re-exports the second,
separating them the way every contract here does — one is a proposition no theorem asserts yet, and the
other is a theorem that exists.

## The outcome state machine, proved

Two theorems in `Spec.Message` carry the machine's substantive laws, and this module re-exports each at
its own type so a reader meets the claim here rather than reconstructing which theorems §13 meant:

* `terminal_absorbing_public` — a terminal delivery state is absorbing: applying any state to a delivery
  whose state is terminal is refused, with a reason. The state a delivery ends in is final whatever
  arrives afterwards.
* `settled_monotone_public` — settlement never returns to false: whatever state is applied, a delivery
  that was settled stays settled. This is the reading `ledger/ambiguities/settlement-is-absorbing.json`
  records, and the theorem is why that reading has a carrier rather than a branch in the code.

## Every section type round-trips: stated, not claimed

`SectionsRoundTrip` and `MessagesRoundTrip` below are the propositions. No theorem asserts them yet, and
`PLAN.md` §13's amendment records why: this wave carried five rungs — types, codec, machine, corpus,
differential — and the round-trip proof is the milestone's remaining obligation. Stating a proposition is
what a contract is for; asserting it with `sorry` would be a claim, which is the difference the frame
layer's contract draws between its executable evidence and its theorems.

## What this file deliberately does not claim

* **Canonicity is not claimed, and it is stronger than the round trip.** What is stated is that decoding
  the encoder's output returns the section, on the image of the encoder — the class where re-encoding is
  an identity by construction. The stronger claim, that encoding a decoder's accepted output reproduces
  its bytes, says something about the *decoder*, and §9's "canonical encodings are specified" note points
  at that shape rather than establishing it in this wave.
* **Cross-transfer section framing is out of scope**, as the S5 delegation records. A message whose
  sections span several transfer frames is a session-layer composition, and nothing here says the list
  decoded from one payload is the list a peer sent across three.
* **The structural-violation condition is a reading.** Part 3's `#message-format` states the section
  occurrence rules and names no condition for breaking them, so the layer refuses them with
  `amqp:decode-error` — the pinned condition whose definition fits — and the corpus records that as a
  reading rather than a citation.
-/

namespace SpecAMQP.Contracts

-- Both opens are needed: Spec.Message carries the section types, the codec and the machine, while the wire
-- type and the refusal `applyState` raises are the harness's. Five layers define their own `Refusal`, so the
-- one a statement means has to be in scope rather than inherited from whichever module opened last.
open SpecAMQP.Spec.Message
open SpecAMQP.Harness

/-- **Every section type round-trips.**

For any section and policy, if the encoder produces octets then the decoder recovers that section and
consumes exactly those octets — no more, because a decoder that consumed less would leave part of the
payload unexplained, and no fewer, because one that consumed more would be reading past what the
encoder wrote. -/
def SectionsRoundTrip (policy : Policy) : Prop :=
  ∀ (sec : Section) (bytes : Octets),
    encodeSection sec = .ok bytes →
    decodeSection policy bytes = .ok (sec, bytes.size)

/-- **Every message round-trips**, given that its sections do.

A message is a list of sections and its encoder is theirs composed, so this is the section-level property
lifted — stated separately so the two claims stay distinguishable when one is proved and the other is
not. The decoder returns a list, so the property is that the list comes back in order and that the whole
payload was consumed, which is what makes it a claim about a message rather than about a concatenation. -/
def MessagesRoundTrip (policy : Policy) : Prop :=
  ∀ (sections : List Section) (bytes : Octets),
    encodeMessage sections = .ok bytes →
    decodeMessage policy bytes = .ok sections

/-- **A terminal delivery state is absorbing**, at the type `Spec.Message` proves it.

Established in `SpecAMQP.Spec.Message.terminal_absorbing`; re-exported here so the acceptance is the
theorem the contract's own vocabulary names. -/
theorem terminal_absorbing_public (delivery : Delivery) (state : DeliveryState) (settled : Bool)
    (current : DeliveryState) (held : delivery.state = some current) (terminal : current.terminal = true) :
    ∃ reason : Refusal, applyState delivery state settled = .error reason :=
  SpecAMQP.Spec.Message.terminal_absorbing delivery state settled current held terminal

/-- **Settlement never returns to false**, at the type `Spec.Message` proves it.

Established in `SpecAMQP.Spec.Message.settled_monotone`; this is the law the absorbing reading of
settlement rests on, recorded in the ambiguity register as a reading and carried here as a theorem. -/
theorem settled_monotone_public (delivery : Delivery) (state : DeliveryState) (settled : Bool)
    (result : Delivery) (applied : applyState delivery state settled = .ok result)
    (carried : delivery.settled = true) : result.settled = true :=
  SpecAMQP.Spec.Message.settled_monotone delivery state settled result applied carried

end SpecAMQP.Contracts
