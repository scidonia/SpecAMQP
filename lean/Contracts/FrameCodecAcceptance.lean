import Contracts.FrameCodec
import Proofs.CodecFrameLaws

/-!
# Acceptance declarations for the frame layer

`Contracts.FrameCodec` states what the frame layer claims; this module names the proofs
that establish it, and it exists as its own module for a reason worth recording: the
proofs state their results in the contract's vocabulary, so they import `Contracts.FrameCodec`
— and a declaration *inside* that module would then have to import them back, which is a
cycle. Splitting the acceptance from the statement keeps the dependency one-way: the
statement imports the specification, the proof imports the specification and the
statement, and the acceptance imports all three.

The three claims and where each now stands:

* `AcceptedFramesCarryPerformatives` — **proved unconditionally.** Every frame the decoder
  accepts is a described value whose descriptor names a declared type carrying the frame
  type's role. This is the property that was missing in both artefacts until a mutation
  control found it, and it is now a statement about every accepted frame rather than a
  check somebody wrote.
* `ConsumedIsTheDeclaredSize` — **proved unconditionally.** A decoded frame consumes
  exactly the octet count its `SIZE` field declares, which is what makes the next frame
  start where it should.
* `FrameRoundTripOnEncodedFrames` — **proved from the value layer's consumption law**, and
  the condition is the point rather than a weakening. A frame body is a described value,
  so a frame round trip stated without the value layer's law would be a law about a smaller
  language than the codec speaks. The dependency is a parameter here, so a reader sees
  exactly what the frame law rests on and can check it against `Contracts.Codec`'s own
  statement.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Frame
open SpecAMQP.Proofs (ValueConsumption)

/-- The descriptor property, established: no accepted frame carries a body that is not a
performative the frame type can carry. -/
theorem accepted_frames_carry_performatives :
    AcceptedFramesCarryPerformatives :=
  SpecAMQP.Proofs.accepted_frames_carry_performatives

/-- The size property, established: a decoded frame's consumed count is the `SIZE` it
declares, so a buffer of frames is walked by the frames' own arithmetic. -/
theorem consumed_is_the_declared_size :
    ConsumedIsTheDeclaredSize :=
  SpecAMQP.Proofs.consumed_is_the_declared_size

/-- Frame round trip on the writer's domain, given the value layer's consumption law. The
hypothesis is explicitly *not* discharged here: it is the rung the frame law sits on top
of, and a reader should be able to see that rather than take it on faith. -/
theorem frame_round_trip_public (valueConsumption : ValueConsumption) :
    FrameRoundTripOnEncodedFrames :=
  SpecAMQP.Proofs.frame_round_trip_on_encoded_frames valueConsumption

/-- The value layer's law implies the round trip the *value* contract states, which is how
the frame law's hypothesis is anchored: `Contracts.RoundTripOnEncodedValues` follows from
`ValueConsumption`, so the frame acceptance rests on a named claim this repository already
makes rather than on an unexplained assumption. -/
theorem value_round_trip_public (valueConsumption : ValueConsumption) :
    SpecAMQP.Contracts.RoundTripOnEncodedValues :=
  SpecAMQP.Proofs.round_trip_on_encoded_values_of_consumption valueConsumption

end SpecAMQP.Contracts
