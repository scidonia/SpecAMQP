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

* `frame_conformance_public` is *true and vacuous*: its hypothesis is false, so the theorem says
  nothing about the two artefacts. It is not withdrawn — the proof is real, the relation is
  load-bearing under both mutation controls, and the composition is honest — but a reader must not
  take it as the frame layer's agreement established.
* `ValueLayersAgree` is **undecided**: no divergence is known — forty-five value-layer buffers, ten
  frame-level and the eight odd-map corpus vectors agree in class on both artefacts — and no proof
  exists, because discharging its two conjuncts needs the value layer's own `Conforms` instance.
  Refuted and unproved are different states, and this one is the second. `frame_conformance_public`
  is therefore conditional and undischarged rather than vacuous: its hypothesis is named rather than
  assumed, and calling it vacuous now would be an assertion about a conjecture.
* **The send direction is a different shape, and worse — `Conforms specFrameSend refFrameSend` is
  false.** Not its hypothesis: its consequent. `.array 0x00 [null]` and `.array 0xE0 [null]` are
  accepted by `frameOfJson`, the specification names the refusal `malformed:` because the element is
  not the scalar that encoding requires, and the reference's `arrayElement` catch-all still names it
  `limit:`. A reachable input, two classes, one observable. `Proofs/FrameSendConformance.lean` carries
  that refutation as a theorem, so the day someone weakens the reference rather than fixing it, the
  theorem goes red — which is what a refutation is for.
* And it reaches the connection instance, whose `ReadersAgree` names the same layer and inherits the
  receive direction's status: no known divergence, no proof.

**What follows was a fix in one of the two readings, and the receive half is done.** Both artefacts
refused those buffers and differed only about the class, so either one misread the artifact or the
artifact was silent and the register decided; the reading was decided, both artefacts were aligned to
it (`fd9bdc5`), and the witness above now draws the same class from both. The **send** half
is closed as far as alignment goes and *not* closed as a theorem: patch 3 split the reference's
`arrayElement` catch-all, and three shape refusals on the specification's side were reclassified with it
(`writeFixedData`, `writeVariableData`, `writeCompoundData`), so the two writers now name the same class
for every array body either can reach. **No refutation is provable**, and the reason is a type rather than
a missing witness: the reference's writer returns `Except String Octets`, so its class can only be
recovered by splitting a sentence — the same unreducible step that blocked the value-layer refutations
before the specification's class became a field. `Conforms specFrameSend refFrameSend` is therefore
*believed false before patch 3 and undecided after it, and unprovable in both cases* until the reference's
writer carries a class. `PLAN.md` §10 records the order of discharge — decide the reading, align the
artefacts, then add a vector, because a vector written before the fix is authored from the artifact and one
written after it is authored from the fix.
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
