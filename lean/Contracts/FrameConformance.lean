import Contracts.Conformance
import Proofs.FrameConformance
import Proofs.FrameSendConformance

/-!
# Acceptance: the frame layer conforms

`Contracts.Conformance` states what conformance *is*; this module names the proof that establishes it for
the frame layer. It is the first instance of that relation, which is the reason the interface was landed at
all — a relation nobody has instantiated is a definition nobody has tested, and instantiating it is how the
frame layer's two independently written readers stopped being compared by a differential over a corpus and
started being related by a theorem.

It is a separate module for the reason `FrameCodecAcceptance.lean` records for its own split: the proof
states its result in the interface's vocabulary, so it imports `Contracts.Conformance`, and a declaration
placed before those imports would have to import them back. Statement, then proof, then acceptance, one way
round.

## What it claims, and what it does not

The claim is the **receive direction**: given the value layer's agreement, every step the reference frame
layer takes on the wire is matched by a step the specification's frame layer permits, leaving the two
states related and emitting the same answer — the same frame with the same octets consumed, or a refusal
of the same class. The relation `R` is the proof's, and it is deliberately no stronger than the layer's own
semantics: the body clause compares what the frame layer *reads of* a body rather than the two value types,
because how far two bodies agree is the value layer's relation and not this one's.

The hypothesis is not a convenience. `ValueLayersAgree` says the reference's value reader's answer is one
the specification's reader also gives — the same octets consumed and a body the frame layer reads the same
way, or a refusal of the same class — and it is named in the statement so that a reader sees exactly what
the theorem rests on and what would discharge it. It is a value-layer claim, and its proof belongs there.

**The send direction is claimed too**, in `Proofs.FrameSendConformance`: `ConformsVia R' specFrameSend
refFrameSend`, given two value-layer hypotheses the statement names — `ValueCarrierAgree` for the value layer's
reading of the corpus vocabulary and `ValueWriterAgree` for its writer.

This module said the opposite for a while, and the reason it gave was wrong. A *carrier* for a frame being
written was believed missing because the reference exposes no writer type; it is not missing. The corpus frame
vocabulary plus each artefact's own `frameOfJson` is the carrier both already read — a frame-encode vector is
exactly that — so no change to either artefact was needed and none was made. What is genuinely missing is a
writer *law*, and it is a named hypothesis in the statement rather than an assumption, which is the same
treatment every other layer boundary gets here.
-/

namespace SpecAMQP.Contracts

/-- **The frame layer conforms, given the value layer's agreement.**

An instance of `Conforms` at the frame layer, the first in the repository: the specification's endpoint as
`choose`, the reference's as `step`, and a simulation between their states preserving the wire.
-/
theorem frame_conformance_public (valueAgreement : SpecAMQP.Proofs.ValueLayersAgree) :
    Conforms SpecAMQP.Proofs.specFrame SpecAMQP.Proofs.refFrame :=
  conforms_of_conforms_via SpecAMQP.Proofs.specFrame SpecAMQP.Proofs.refFrame _
    (SpecAMQP.Proofs.ref_frame_conforms valueAgreement)

/-- **The frame layer conforms in the send direction**, given the two value-layer hypotheses.

An instance of `Conforms` at the send half of the frame layer: the specification's writer as `choose`, the
reference's as `step`, and a simulation preserving the octets that go on the wire.
-/
theorem frame_send_conformance_public (carriers : SpecAMQP.Proofs.ValueCarrierAgree)
    (writers : SpecAMQP.Proofs.ValueWriterAgree) :
    Conforms SpecAMQP.Proofs.specFrameSend SpecAMQP.Proofs.refFrameSend :=
  conforms_of_conforms_via SpecAMQP.Proofs.specFrameSend SpecAMQP.Proofs.refFrameSend _
    (SpecAMQP.Proofs.ref_frame_send_conforms carriers writers)

end SpecAMQP.Contracts
