import Contracts.Conformance
import Proofs.FrameConformance
import Proofs.FrameSendConformance
import Proofs.ValueCarrierAgreement
import Proofs.ValueWireAgreement

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

## The receive hypothesis has no known divergence left, and the send direction's consequent is false

A later slice set out to discharge `ValueLayersAgree` and refuted it, and the refutation was checked
here at the source rather than taken from the report. Six octets are enough:

`#[0xC1, 0x08, 0x03, 0x40, 0x40, 0x40]` — a `map8` whose count field is 3, odd — *was* refused by the
specification as `malformed:` and by the reference as `DecodeError.sizeMismatch "map" 8 4`: both
refused, and they disagreed about **which class named the refusal**, which is part of the observable,
since §10's `Output` carries the refusal and the corpus compares the class. The parity order was
aligned to the artifact's reading and **the same buffer now draws `malformed` from both**, and a sweep
of 114,225 buffers — every buffer of length one to three over the format-code alphabet, every length-four
buffer over a narrower one, all 256 array element constructors, arrays of zero-width and nested and
described elements, and compounds with size and count crossed — finds **no remaining class divergence**,
with both readers refusing the same 77,124 of them. So the sentence this paragraph used to support,
that `Conforms specFrame refFrame` is false as an unconditional statement, has no witness left, and
therefore:

* `ValueLayersAgree` is **proved**, by `Proofs.ValueWireAgreement`'s `valueLayersAgree` — no
  hypotheses, axioms within `[propext, Classical.choice, Quot.sound]`. **`frame_conformance_public` is
  therefore discharged and unconditional**, and `frame_receive_conformance` below states the frame
  layer's receive instance with no hypothesis standing in for the value layer. The theorem was
  *vacuous* while the hypothesis was refuted and *conditional* while the value layer was unproved; it is
  neither now, and this section has had to distinguish three states here — refuted, unproved, proved. A
  reader who met the earlier bullets is owed the correction explicitly: the frame layer's receive half
  **is** established, and the sentence that said it was not has been removed rather than left beside its
  replacement. What the discharge rests on is the wire-agreement module's forty arms, the fuel
  irrelevance that aligns its loops, and the readers' position invariance — each of which had to be
  *found* rather than assumed.
**The statuses are deliberately not restated here, and that is a decision with evidence behind it.** This
block has been rewritten three times in one day because it asserted the *state* of four instances whose
states moved under it — a hypothesis refuted and then withdrawn, a `String` removed from a writer's error
type, a relation proved between two passes over the same paragraph, and a sentence claiming a theorem that
had never been in the tree at all. **Every rewrite left the parts it was not looking at**, which makes this
the most-edited prose in the repository and the only block whose claims track facts that change by the hour.
So the statuses live where the slices that change them can keep them:

* **the frame send direction** — conditional on `ValueWriterAgree`, and what is known about its consequent
  is stated in `Proofs/FrameSendConformance.lean`'s closing section, together with the search that
  established it and what a witness would have to be;
* **the connection layer** — unconditional, by `connection_conformance` below;
* **the frame receive half** — unconditional, by `frame_receive_conformance` below;
* **the value layer's agreement** — proved, `Proofs.valueLayersAgree`.

**And the one thing this section keeps, because it does not move**: the order of discharge is to decide the
reading, align the artefacts, then add a vector — a vector written before the fix is authored from the
artifact, and one written after it is authored from the fix.
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

/-- **The frame layer conforms in the send direction**, given the writer law.

An instance of `Conforms` at the send half of the frame layer: the specification's writer as `choose`, the
reference's as `step`, and a simulation preserving the octets that go on the wire.

The carrier hypothesis is discharged rather than assumed: `valueCarrierAgree_all` supplies
`ValueCarrierAgree`, and **the statement did not move to meet the proof** — `ValueCarrierAgrees 64` *is*
`ValueCarrierAgree` by definitional equality, which is why `valueCarrierAgree_of_agrees` is `:= h`. What
remains is the writer law, and behind it the reference's writer carrying a class, which is the change that
would also make the endpoint's refutation expressible.
-/
theorem frame_send_conformance_public (writers : SpecAMQP.Proofs.ValueWriterAgree) :
    Conforms SpecAMQP.Proofs.specFrameSend SpecAMQP.Proofs.refFrameSend :=
  conforms_of_conforms_via SpecAMQP.Proofs.specFrameSend SpecAMQP.Proofs.refFrameSend _
    (SpecAMQP.Proofs.ref_frame_send_conforms SpecAMQP.Proofs.valueCarrierAgree_all writers)

/-- **The frame layer's receive direction conforms, discharged.**

`frame_conformance_public` with its hypothesis supplied rather than named: the value layer's agreement
is a theorem in this tree, so nothing stands between this statement and the two artefacts. It is the
acceptance declaration for the frame layer's receive half, and its being unconditional is the
difference between a claim about what would follow and a claim about these two endpoints.

The send half stays conditional on the writer law, and its consequent is separately recorded as false
for a reachable array body — so this theorem is half of a layer's conformance rather than the whole of
it, and the section above says which half and why. -/
theorem frame_receive_conformance :
    Conforms SpecAMQP.Proofs.specFrame SpecAMQP.Proofs.refFrame :=
  frame_conformance_public SpecAMQP.Proofs.valueLayersAgree

end SpecAMQP.Contracts
