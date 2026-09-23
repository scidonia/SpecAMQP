import Contracts.Conformance
import Proofs.ConnectionConformance
import Proofs.ReadersAgree

/-!
# Acceptance: the connection layer conforms

`Contracts.Conformance` states what conformance *is*; this module names the proof that establishes it
for the connection layer, the repository's third instance of that relation and the first above the
frame layer. The frame layer's two instances relate two *readers* of the same octets; this one relates
two exchange endpoints, so it is the first place the relation covers a state machine that decides
negotiation, the SASL dialogue and the connection's own transitions rather than one that only decodes.

It is a separate module for the reason `FrameCodecAcceptance.lean` records for its own split: the
proof states its result in the interface's vocabulary, so it imports `Contracts.Conformance`, and a
declaration placed before those imports would have to import them back. Statement, then proof, then
acceptance, one way round.

## What it claims

Given two frame readers' agreement, every step the reference takes on an input of the interface's
alphabet is a step the specification permits, leaving the two states related by `RConn` and emitting
the same outputs — the same octets, or a refusal of the same class. Both directions of the layer are
inside that: the receive column through `arriving_matched`, and the send column through `stepAgrees`,
which covers the header exchanges, a bodyless frame, the two layer dispatches and the arriving case
reduced to the other.

The hypothesis is named in the statement rather than assumed, which is this repository's treatment of
every layer boundary: `ReadersAgree` is a *frame-layer* claim — that the reference's reader's answer is
one the specification's reader also gives — and it is discharged by the frame instances above, not by
this module. The same shape `frame_conformance_public` has for the value layer.

## What it does not claim, and the one question this instance raised

It does not claim the transport: the endpoint's alphabet is octets and API calls, and the socket layer
is outside the relation entirely (`PLAN.md` §23.1 names it as the implementation's one unproved
dependency). A conformance instance says nothing about how the octets arrive.

And it raises a point about the *per-step vocabulary* rather than about §10, recorded here because the
question was raised against this declaration. The composition needs each step's two answers to be the
**same** answer; the per-step relation as first written was `AnswersMatch`, whose two conjuncts are
`spec = ok → ref = ok` and `ref = error → spec = error`, and those are **both vacuous in exactly one
direction**: when the specification refuses and the reference accepts. That is the direction that
matters — a reference strictly more permissive than the specification would escape the relation
entirely — while the reverse mismatch is *not* vacuous, because `spec = ok` makes the first conjunct
demand the opposite constructor of the reference's answer.

A *shape equality* (`so.isOk = ro.isOk`), delivered by each step slice alongside the implications, is
what closes it, and it is load-bearing in the composition rather than decorative: without it the
`spec = error` / `ref = ok` case cannot be eliminated and the output sequences cannot be compared.

**No strengthening of §10 is needed and none was made.** `ConformsVia` already demands a concrete
matching permitted step, a related successor, and exact equality of the two output lists — the
weakness was never in the contract. It was in a step vocabulary written inside the proof module, and
it is closed there.
-/

namespace SpecAMQP.Contracts

/-- **The connection layer conforms, given the two frame readers' agreement.**

An instance of `Conforms` at the connection layer: the specification's exchange endpoint as `choose`,
the reference's as `step`, and a simulation between their states preserving the wire. Built through the
interface's own `conforms_of_conforms_via`, so that what this declares is the relation §10 defines
rather than a lookalike of it. -/
theorem connection_conformance_public (readers : SpecAMQP.Proofs.ReadersAgree) :
    Conforms SpecAMQP.Proofs.specConn SpecAMQP.Proofs.refConn :=
  SpecAMQP.Proofs.ref_connection_conforms_existential readers

/-- **The connection layer conforms, discharged.**

`connection_conformance_public` with its hypothesis supplied rather than named: `Proofs.readersAgree`
proves the two frame readers' agreement with no hypotheses of its own, so this states the connection
layer's conformance of the two endpoints themselves rather than of what would follow from a relation.
The connection instance joins the frame layer's receive half as an unconditional `Conforms` instance.

**One sentence of history, because it explains why the hypothesis was open rather than overlooked.**
`ReadersAgree` demands `FramesAgree` on the frames, which includes `ValuesAgree` on the body — the whole
value, elementwise — while the layer beneath it speaks in the *view* vocabulary a frame reader actually
consults, since a frame reader reads a body only to ask which declared type its descriptor names and
whether the frame type's role is among that type's `provides`. So the connection layer's hypothesis was
one notch stronger than the frame layer could reach, and it stayed open until the value law's proof —
which carries `BodiesAgree` internally and weakens it to view equality only at `valueLayersAgree` —
donated the missing step, `valuesAgree_of_bodiesAgree`. **A relation stated one notch stronger than the
layer beneath it can deliver is the fourth shape of this kind this specification has produced**, and in
this case the stronger relation turned out to be true: what was missing was the step, not the fact. -/
theorem connection_conformance :
    Conforms SpecAMQP.Proofs.specConn SpecAMQP.Proofs.refConn :=
  connection_conformance_public SpecAMQP.Proofs.readersAgree

end SpecAMQP.Contracts
