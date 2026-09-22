import Spec.Frame

/-!
# The frame layer's laws

Three statements, and they are not all the same kind of thing, so the file separates
them rather than dressing one as another.

The header arithmetic is **proved**: it is arithmetic over definitions, and it is one of
the two places a hand-written layout drifts, which is why it is proved rather than
tested.

The descriptor statement is **proved**. It says that every frame the decoder accepts
carries a performative whose descriptor names a declared type with the frame type's role —
the property that was missing in both artefacts until a mutation control found it, since
nothing stopped a body from being an anonymous described value. It is now a claim about
every accepted frame rather than a branch somebody wrote.

Frame round trip is **proved from the value layer's consumption law**, and the condition
is the point rather than a weakening. A frame body is a described value *followed in the
same buffer by the payload*, so the frame layer needs the reader to consume exactly the
value's octets out of a buffer that continues past it — a statement strictly stronger than
the value contract's own round trip, whose buffer ends where the value does. That
strengthening is a parameter of this file's acceptance theorem, and the proof module shows
it implies `Contracts.RoundTripOnEncodedValues`, so the dependency is visible from both
ends: the frame law rests on a named claim, and that claim is one this repository already
makes. The S1.5 ladder is what this sits on top of.

The proofs live in `Contracts.FrameCodecAcceptance` rather than here, because the proof
module states its results in this file's vocabulary and a declaration here would have to
import it back — the same split TemperMint uses between a contract and its conformance
module.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Frame
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Harness (Octets)

/-- The extended header is the octets between the header and the body, and `DOFF` counts
the body's start in four-octet words: at the minimum `DOFF` there is no extended header,
and each further word adds four octets of it.

Proved rather than tested because it is the layout's arithmetic: `bodyStart doff` is the
octet the body begins at, `headerOctets` is the fixed eight, and the artifact's own
diagram labels the difference `(DOFF * 4 - 8)`. A codec that counted the extended header
from the wrong end, or read `DOFF` as octets rather than words, would satisfy every vector
that has no extended header and fail this. -/
theorem extended_header_width (doff : Nat) (_h : minDoff ≤ doff) :
    bodyStart doff - headerOctets = (doff - minDoff) * doffWord := by
  simp [bodyStart, headerOctets, minDoff, doffWord]
  omega

/-- At the minimum `DOFF` the body begins exactly where the header ends. -/
theorem body_starts_after_the_header : bodyStart minDoff = headerOctets := by
  simp [bodyStart, minDoff, headerOctets, doffWord]

/-- Every frame the decoder accepts carries a performative: the body is a described value
whose descriptor names a declared type whose `provides` carries the frame type's role.

This is the statement whose absence was a conformance gap. `framing.3` requires the
performative to be one of those defined, and both artefacts accepted a frame whose body
was a described value with a descriptor naming nothing — well-formed octets that name no
performative. The check now exists in both; this proposition is what makes it a claim
about every accepted frame rather than a branch somebody wrote, and it is proved in
`Contracts.FrameCodecAcceptance`. -/
def AcceptedFramesCarryPerformatives : Prop :=
  ∀ (bytes : Octets) (frame : Frame) (consumed : Nat),
    decodeFrame bytes = .ok (frame, consumed) →
    ∃ descriptor inner,
      frame.body = .described descriptor inner ∧
        carriesPerformative frame.frameType descriptor = true

/-- A decoded frame reports the octet count its `SIZE` field declares, and that count is
the prefix of the buffer the frame occupies. Everything downstream depends on it: a frame
whose `SIZE` disagreed with its octets would make the next frame start in the wrong place,
which is exactly the framing error the negative vectors pin. Proved in
`Contracts.FrameCodecAcceptance`. -/
def ConsumedIsTheDeclaredSize : Prop :=
  ∀ (bytes : Octets) (frame : Frame) (consumed : Nat),
    decodeFrame bytes = .ok (frame, consumed) →
    consumed = beAt bytes 0 sizeOctets ∧ headerOctets ≤ consumed ∧ consumed ≤ bytes.size

/-- Frame round trip on the writer's domain: every frame the writer encodes is read back
byte for byte, consuming the whole buffer.

Stated over `encodeFrame`'s own domain, like the value layer's law, so that where the
writer refuses there is nothing to claim. It depends on the value layer's consumption law,
because the body is a described value followed by a payload in the same buffer: this is the
rung that sits on top of S1.5 rather than a separate result, and its proof is in
`Contracts.FrameCodecAcceptance`, conditional on exactly that law. -/
def FrameRoundTripOnEncodedFrames : Prop :=
  ∀ (frame : Frame) (bytes : Octets),
    encodeFrame frame = .ok bytes →
    decodeFrame bytes = .ok (frame, bytes.size)

end SpecAMQP.Contracts
