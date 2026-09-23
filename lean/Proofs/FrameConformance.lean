import Contracts.Conformance
import Spec.Frame
import Ref.Frame

/-!
# The frame layer's first `Conforms` instance

`SpecAMQP.Contracts.Conformance` fixes what conformance means and says that the first instance is
the reference rather than a downstream programme. This module is that instance for the frame layer:
`Spec.Frame`'s reader against `Ref.Frame`'s, proved as a theorem instead of compared as a
differential over a corpus.

## The observable step of each side

Neither frame layer is a state machine, and that is the first thing the interface has to be told.
Both are codecs: one pure function of a buffer,

  `readFrame : Octets → Except Refusal (Frame × Nat)`

reading a frame from the front of a buffer and reporting the octets that carried it, and a second,

  `writeFrame : Frame → Except Refusal Octets`

writing a frame back. Neither layer has a field that survives a call. What each layer's state is,
is the wire: the octets the reader was handed, and the octets the writer produces.

Each refusal carries its reason class as a field, and each layer also exposes the same two
functions rendered as the message a caller sees (`decodeFrame`, `encodeFrame`), which are
`readFrame`/`writeFrame` with the class and the prose spelled out. A proof works with the classed
form, because a class read back out of prose by `String.splitOn` is one no kernel proof can reason
about; a caller and the corpus keep the message form, whose bytes are what they always were.

So this is the mapping onto the interface's alphabet:

* **`Input.frame bytes` is the receive direction.** Octets arrive on the wire and the layer
  answers whether they carry a frame, which frame, and how many octets carried it.
* **`Output.api ⟨name, ok⟩` is that answer.** The interface's alphabet carries a frame nowhere —
  `Output` is `ByteArray` or `ApiResponse`, and `ApiResponse` is a name and a flag — so the answer
  is reported as the two things both layers can name in the same words: `ok` is whether a frame
  was read, and `name` is the refusal's class where one was refused, or the frame type's own name
  (`AMQP`/`SASL`) where one was read. The class, not the prose: the two artefacts spell their prose
  differently by design, and the corpus compares classes between them, so a class is what "the same
  answer" means here. The frame itself is what the state holds, and `R` compares it.
* **`Input.tick` is an input this layer has nothing to say about.** The frame layer has no timers,
  so the step is `none` and `choose` — the singleton of the step's outcome — is empty for a tick.
* **`Input.api` is the send direction, and this instance does not cover it.** See "What this rests
  on, and what it does not cover".

This instance is the receive direction, which is the half the layer's observable *is*: bytes in,
an answer out. That it is stated for `Input.frame` alone is a narrowing with a named reason
rather than a silent one, and the reason is below.

## The state

`Conforms` is a simulation over a state, and a memoryless layer has none to offer, so the state is
the one thing the interface observes of a call: **the layer's answer to the last buffer it was
handed** — `Verdict.read frame consumed`, or `Verdict.refused reasonClass`, with `none` for "no
answer yet". The choice matters and is not cosmetic: with `Unit` states the only relation between
them is `True`, and `R` would be `fun _ _ => True`, which is the vacuous simulation the assignment
forbids. The state has to carry the layer's answer or the relation has nothing to be about.

## The relation

`R` says the two layers answered alike, and it is *the smallest relation that says so*:

* `none` to `none`: neither has answered yet. Nothing else can be asserted, because neither layer
  holds anything.
* `read` to `read`: the same consumed count, and `FrameAgrees` — the two frames agree on every
  field the layout fixes (`doff`, `channel`, `extended`, `payload`), on the frame type up to the
  two layers' naming of it, and on the body *as the frame layer reads a body*: whether it is a
  described value, and which declared type its descriptor names. It is not the frames' bodies
  being equal values: the two value types share nothing, and how far two bodies agree is the value
  layer's relation to state, not this one's. What the frame layer itself reads out of a body is
  exactly this much, and it is what decides the layer's every remaining answer (malformed,
  unsupported, or accepted with a role test), so the relation is as strong as the layer's own
  semantics and no stronger. The consumed count is part of it because it is what the layer's
  answer gives the caller: the frame's extent in the buffer, which the body's own extent follows
  from once the offset agrees.
* `refused` to `refused`: the same refusal class. Both layers' documentation puts the class in
  the interface ("the reason-class vocabulary ... because the differential contract compares
  classes between the artefacts"), so two refusals for different reasons are not an agreement.
* Anything else: false. A read against a refusal is a disagreement, and saying so is the whole
  point of the relation.

Weakening it loses one of those clauses and with it the corresponding half of the claim. `R`
without `FrameAgrees` would let the layers read different frames from the same octets; without the
consumed count it would let them disagree about the frame's extent, which is what a reader of a
stream hands to the caller; without the refusal class it could not tell "both refuse" from "both
refuse for the same reason", which is the difference the corpus compares. `R := fun _ _ => True`
is weaker than all of them and proves nothing.

## What this rests on, and what it does not cover

**It rests on the value layer's reader agreement.** A frame's body is a described value, and both
frame layers read it with their own value layer (`Spec.Codec.decodeValue`, `Ref.Value.decode`) —
two independently written codecs. Whether a buffer's body decodes, to what, and how many octets it
took, is therefore a value-layer question that no frame-layer proof can answer, and the frame
layer consults the answer twice (the body must be a described value, and its descriptor must name
a declared type carrying the frame type's role). `ValueLayersAgree` is that obligation, named in
the theorem below rather than left in prose: for every buffer, the reference's reader's answer is
one the specification's reader also gives — the same consumed count and a body the frame layer
reads the same way, or a refusal whose class agrees, in the specification's case by the class its
value layer's message leads with and in the reference's by the class its value layer's own variant
names. It is a claim about the value layer, which is where its proof belongs; nothing here assumes
anything about frames.

**It does not cover the send direction.** `Input.api` — the application asking the layer to write a
frame — is outside the model, and that is a gap with a reason rather than an oversight. Two things
are missing, and neither is in either tree today:

1. a *carrier*: `Conforms` feeds the same `Input` to both endpoints, and the two layers' `Frame`
   types share no definition, so the only vocabulary a frame can cross in is the wire — which
   makes the send direction a decode followed by an encode, and needs each side's reader and
   writer to agree with each other before either can be compared;
2. a *value relation and a writer law on it*: the octets the two writers produce for two bodies
   are not determined by how the frame layer reads those bodies. `Spec.Frame`'s writer law exists
   (`Contracts.FrameCodec.FrameRoundTripOnEncodedFrames`, conditional on the value layer's
   consumption law); `Ref` exposes no writer law and no relation between its values and the
   specification's, and the value layer's own instance is where both belong.

Assuming a frame-level writer agreement instead would be assuming the conclusion for that
direction, so the direction is reported as an obligation rather than worked around.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Contracts
open SpecAMQP.Harness (Octets)

/-! ## The vocabulary the two layers can be compared in -/

/-- The reference's name for a specification frame type. The two layers each assign the same two
frame types to the same two code octets; this is that agreement as a function, so a statement can
say "the same frame type" rather than "the same octet". -/
def refKind (frameType : SpecAMQP.Spec.Frame.FrameType) : SpecAMQP.Ref.Frame.Kind :=
  match frameType with
  | .amqp => .amqp
  | .sasl => .sasl

/-- The mapping preserves the name the layers give a frame type, which is what the answer's name is
on an accepted frame. -/
theorem refKind_name (frameType : SpecAMQP.Spec.Frame.FrameType) :
    SpecAMQP.Spec.Frame.FrameType.name frameType =
      SpecAMQP.Ref.Frame.Kind.name (refKind frameType) := by
  cases frameType <;> rfl

/-- And the role a frame type carries, which is what decides whether a body's performative belongs
in the frame. -/
theorem refKind_role (frameType : SpecAMQP.Spec.Frame.FrameType) :
    SpecAMQP.Spec.Frame.FrameType.role frameType =
      SpecAMQP.Ref.Frame.Kind.role (refKind frameType) := by
  cases frameType <;> rfl

/-- The two layers' type-code dispatch is one dispatch: a code the reference reads as a frame type
is a code the specification reads as the same frame type. -/
theorem ofCode_matched (code : Nat) (kind : SpecAMQP.Ref.Frame.Kind)
    (h : SpecAMQP.Ref.Frame.Kind.ofCode code = some kind) :
    ∃ frameType : SpecAMQP.Spec.Frame.FrameType,
      SpecAMQP.Spec.Frame.FrameType.ofCode code = some frameType ∧ refKind frameType = kind := by
  unfold SpecAMQP.Ref.Frame.Kind.ofCode at h
  unfold SpecAMQP.Spec.Frame.FrameType.ofCode
  simp only [SpecAMQP.Ref.Frame.amqpType, SpecAMQP.Ref.Frame.saslType,
    SpecAMQP.Spec.Frame.amqpTypeCode, SpecAMQP.Spec.Frame.saslTypeCode] at h ⊢
  split at h <;> simp_all [refKind]

/-- What the frame layer reads out of a body: `none` if it is not a described value (the layout
refuses that as malformed), `some none` if it is one whose descriptor names no declared type (the
layout refuses that as unsupported), and `some (some decl)` if it names one, in which case the
frame type must carry the role the declaration provides. A frame layer reads nothing else out of a
body, so this is the whole of a body as far as this layer is concerned. -/
abbrev BodyView := Option (Option SpecAMQP.Generated.Oasis.TypeDecl)

/-- The specification's body view. -/
def specBodyView (body : SpecAMQP.Spec.Codec.Value) : BodyView :=
  match body with
  | .described descriptor _ => some (SpecAMQP.Spec.Frame.typeOfDescriptor descriptor)
  | _ => none

/-- The reference's body view, the same function written against the other value type. -/
def refBodyView (body : SpecAMQP.Ref.Value) : BodyView :=
  match body with
  | .described descriptor _ => some (SpecAMQP.Ref.Frame.typeOfDescriptor descriptor)
  | _ => none

/-- Two frames are the same reading: the layout's fields agree, the frame type agrees up to the two
layers' naming of it, and the bodies agree as far as the frame layer reads a body. -/
def FrameAgrees (frame : SpecAMQP.Spec.Frame.Frame) (other : SpecAMQP.Ref.Frame.Frame) : Prop :=
  frame.doff = other.doff ∧
  refKind frame.frameType = other.kind ∧
  frame.channel = other.channel ∧
  frame.extended = other.extended ∧
  frame.body.map specBodyView = other.body.map refBodyView ∧
  frame.payload = other.payload

/-! ## The layer's answer, and the two endpoints -/

/-- One frame layer's answer to one buffer: the frame it read and the octets that carried it, or
the class of the refusal it reported. The class rather than the whole refusal, because the two
layers' prose differs by design and the class is the part of a refusal that is interface. -/
inductive Verdict (Frame : Type) where
  /-- A frame was read, and this many octets carried it. -/
  | read (frame : Frame) (consumed : Nat)
  /-- No frame: the layer refused, and this is the class of its refusal. -/
  | refused (reasonClass : String)

/-- The specification's answer to a buffer, in the specification's own reader's terms. -/
def specAnswer (bytes : ByteArray) : Verdict SpecAMQP.Spec.Frame.Frame :=
  match SpecAMQP.Spec.Frame.readFrame bytes.data with
  | .ok (frame, consumed) => .read frame consumed
  | .error refusal => .refused refusal.reasonClass

/-- The reference's answer to a buffer, in the reference's own reader's terms. -/
def refAnswer (bytes : ByteArray) : Verdict SpecAMQP.Ref.Frame.Frame :=
  match SpecAMQP.Ref.Frame.readFrame bytes.data with
  | .ok (frame, consumed) => .read frame consumed
  | .error refusal => .refused refusal.reasonClass

/-- An answer as the interface's alphabet can carry it: whether a frame was read, and the class
where none was, or the frame type's name where one was. -/
def specOutput (answer : Verdict SpecAMQP.Spec.Frame.Frame) : Output :=
  match answer with
  | .read frame _ => .api ⟨frame.frameType.name, true⟩
  | .refused reasonClass => .api ⟨reasonClass, false⟩

/-- The reference's answer as the same alphabet carries it. -/
def refOutput (answer : Verdict SpecAMQP.Ref.Frame.Frame) : Output :=
  match answer with
  | .read frame _ => .api ⟨frame.kind.name, true⟩
  | .refused reasonClass => .api ⟨reasonClass, false⟩

/-- The specification endpoint's state: its answer to the last buffer it was handed, or `none`
before the first. -/
abbrev SpecState := Option (Verdict SpecAMQP.Spec.Frame.Frame)

/-- The reference endpoint's state, the same thing. -/
abbrev RefState := Option (Verdict SpecAMQP.Ref.Frame.Frame)

/-- The specification's step. The layer is memoryless, so the state after a step is the answer to
the input and not a function of the state before it; a tick and an application call get no answer
from the frame layer at all. -/
def specStep (_ : SpecState) (inp : Input) : Option (SpecState × List Output) :=
  match inp with
  | .frame bytes =>
    let answer := specAnswer bytes
    some (some answer, [specOutput answer])
  | .tick _ => none
  | .api _ => none

/-- The reference's step, the same shape over the reference's reader. -/
def refStep (_ : RefState) (inp : Input) : Option (RefState × List Output) :=
  match inp with
  | .frame bytes =>
    let answer := refAnswer bytes
    some (some answer, [refOutput answer])
  | .tick _ => none
  | .api _ => none

/-- The specification as an endpoint: every permitted outcome is the layer's own reader's answer
and nothing else, because `choose` is the singleton of the step's outcome. The frame layer's
receive direction has no `MAY`: the artifact's own `MAY` in this layer is the empty frame on the
send side (`writeFrame` refuses to write one), and the negotiated maximum frame size is another
send-side latitude; neither appears in what a receiver must answer. -/
def specFrame : Endpoint SpecState where
  init := none
  step := specStep
  choose := fun s inp => {out | specStep s inp = some out}

/-- The reference as an endpoint. `ConformsVia` never consults the implementation's `choose` — an
implementation has none, which is why the field is empty here rather than a second set that could
drift. -/
def refFrame : Endpoint RefState where
  init := none
  step := refStep
  choose := fun _ _ => ∅

/-- **The relation**, as described at the head of this module. -/
def R : SpecState → RefState → Prop
  | none, none => True
  | some (.read frame consumed), some (.read other used) =>
    FrameAgrees frame other ∧ consumed = used
  | some (.refused reasonClass), some (.refused other) => reasonClass = other
  | _, _ => False

/-! ## The tie-back: what the endpoint permits is what the layer does -/

/-- The endpoint's permitted outcomes are its own step's outcome, which is what defines `choose`
rather than a coincidence about it. -/
theorem specFrame_choose_member (s : SpecState) (inp : Input) (out : SpecState × List Output) :
    out ∈ specFrame.choose s inp ↔ specFrame.step s inp = some out := Iff.rfl

/-- **The tie-back, in the layer's own vocabulary.** A permitted outcome on a buffer is exactly the
specification's own reader's answer: this frame consumed this many octets, or a refusal of this
class. Stated against `Spec.Frame.readFrame` — the layer's own reader, whose refusal carries the
class as a field, and whose rendered form `decodeFrame` is what a caller sees — rather than against
the endpoint's own step, because a `choose` tied only to its own wrapper is a proof about a
relation the specification does not have.

This is also what makes the instance mutation-sensitive where it counts: with `choose` widened to
`Set.univ` the simulation below still compiles — it only ever consumes membership — and this
equivalence fails, because a tick or an application call has no permitted outcome and would then
permit every outcome. -/
theorem specFrame_choose_is_the_reader (s : SpecState) (bytes : ByteArray)
    (s' : SpecState) (outs : List Output) :
    (s', outs) ∈ specFrame.choose s (.frame bytes) ↔
      (∃ (frame : SpecAMQP.Spec.Frame.Frame) (consumed : Nat),
          SpecAMQP.Spec.Frame.readFrame bytes.data = .ok (frame, consumed) ∧
          s' = some (.read frame consumed) ∧ outs = [specOutput (.read frame consumed)]) ∨
      (∃ refusal : SpecAMQP.Spec.Frame.Refusal,
          SpecAMQP.Spec.Frame.readFrame bytes.data = .error refusal ∧
          s' = some (.refused refusal.reasonClass) ∧
          outs = [specOutput (.refused refusal.reasonClass)]) := by
  rw [specFrame_choose_member]
  unfold specFrame specStep specAnswer
  dsimp only []
  cases h : SpecAMQP.Spec.Frame.readFrame bytes.data
  all_goals simp only []
  all_goals grind

/-- The endpoint's answer to a buffer is that buffer's frame, when the specification's reader reads
one. -/
theorem specAnswer_read (bytes : ByteArray) (frame : SpecAMQP.Spec.Frame.Frame) (consumed : Nat) :
    specAnswer bytes = .read frame consumed ↔
      SpecAMQP.Spec.Frame.readFrame bytes.data = .ok (frame, consumed) := by
  unfold specAnswer
  cases h : SpecAMQP.Spec.Frame.readFrame bytes.data
  all_goals simp only []
  all_goals grind

/-- The endpoint's answer to a buffer is that buffer's refusal's class, when the specification's
reader refuses it. -/
theorem specAnswer_refused (bytes : ByteArray) (reasonClass : String) :
    specAnswer bytes = .refused reasonClass ↔
      ∃ refusal : SpecAMQP.Spec.Frame.Refusal,
        SpecAMQP.Spec.Frame.readFrame bytes.data = .error refusal ∧
        refusal.reasonClass = reasonClass := by
  unfold specAnswer
  cases h : SpecAMQP.Spec.Frame.readFrame bytes.data
  all_goals simp only []
  all_goals grind

/-! ## The obligation this instance rests on -/

/-- **The value layer's reader agreement**, as the frame layer uses it: for every buffer, whatever
the reference's value reader answers is an answer the specification's value reader also gives —
the same octets consumed and a body the frame layer reads the same way, or a refusal whose class
agrees, where the specification's class is the one its value layer's message leads with and the
reference's is the one its value layer's own variant names.

This is a claim about the value layer, and the value layer's own `Conforms` instance is where it is
proved. It is named in the theorem below because the frame layer consults the value layer, and
because a frame proof that quietly re-derived it would be claiming another layer's theorem. -/
def ValueLayersAgree : Prop :=
  ∀ region : Octets,
    (∀ (other : SpecAMQP.Ref.Value) (used : Nat),
        SpecAMQP.Ref.decode region = .ok (other, used) →
        ∃ body : SpecAMQP.Spec.Codec.Value,
          SpecAMQP.Spec.Codec.decodeValue region = .ok (body, used) ∧
          specBodyView body = refBodyView other) ∧
    (∀ failure : SpecAMQP.Ref.DecodeError,
        SpecAMQP.Ref.decode region = .error failure →
        ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
          SpecAMQP.Spec.Codec.decodeValue region = .error refusal ∧
          (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-! ## The proof -/

/-- The reference's answer to a buffer is one the specification's reader also gives: the same frame
and the same extent, or a refusal whose class agrees. This is the whole content of the simulation
at the level the two layers answer at, before the endpoint wraps it. -/
def AnswerMatched (spec : Except SpecAMQP.Spec.Frame.Refusal (SpecAMQP.Spec.Frame.Frame × Nat))
    (ref : Except SpecAMQP.Ref.Frame.Refusal (SpecAMQP.Ref.Frame.Frame × Nat)) : Prop :=
  (∀ (other : SpecAMQP.Ref.Frame.Frame) (used : Nat),
      ref = .ok (other, used) →
      ∃ (frame : SpecAMQP.Spec.Frame.Frame) (consumed : Nat),
        spec = .ok (frame, consumed) ∧ consumed = used ∧ FrameAgrees frame other) ∧
  (∀ failure : SpecAMQP.Ref.Frame.Refusal,
      ref = .error failure →
      ∃ refusal : SpecAMQP.Spec.Frame.Refusal,
        spec = .error refusal ∧ refusal.reasonClass = failure.reasonClass)

/-! ## The specification's reader, branch by branch

The two readers decide the same questions in the same order over the same octets, so the proof of
agreement is a walk of the specification's own decision tree against the branch facts the
reference's supplies. These lemmas are that walk, one branch at a time, and they are stated in the
octets' own terms (`8`, `4`, `1`, `2` are the layout's constants unfolded, and `beAt` is the field
reader the two layers spell the same way) so that a branch fact from either layer is a fact both
lemmas can use. Each says what the specification's reader answers, and with which class, where the
whole of the reference's branch is known. -/

/-- The field reader is one function in both layers, so a branch of one reader's walk is a branch
fact about the other's. -/
theorem beAt_eq : SpecAMQP.Spec.Frame.beAt = SpecAMQP.Ref.Frame.beAt := rfl

/-- The type-code dispatch is one dispatch in the other direction: a code the reference does not
assign is a code the specification does not assign. -/
theorem ofCode_none_iff (code : Nat) :
    SpecAMQP.Spec.Frame.FrameType.ofCode code = none ↔
      SpecAMQP.Ref.Frame.Kind.ofCode code = none := by
  unfold SpecAMQP.Spec.Frame.FrameType.ofCode SpecAMQP.Ref.Frame.Kind.ofCode
  simp only [SpecAMQP.Spec.Frame.amqpTypeCode, SpecAMQP.Spec.Frame.saslTypeCode,
    SpecAMQP.Ref.Frame.amqpType, SpecAMQP.Ref.Frame.saslType]
  by_cases h₀ : code = 0
  · simp [h₀]
  · by_cases h₁ : code = 1
    · simp [h₀, h₁]
    · simp [h₀, h₁]

/-- A buffer shorter than a frame header: the specification refuses it, with the class the
reference refuses it with. -/
theorem spec_refuses_short (bytes : Octets) (h : bytes.size < 8) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "truncated" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets]
  rw [if_pos h]
  exact ⟨_, rfl, rfl⟩

/-- `SIZE` below the frame header. -/
theorem spec_refuses_size_below_header (bytes : Octets)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "sizeMismatch" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets, beAt_eq]
  rw [if_neg h₁, if_pos h₂]
  exact ⟨_, rfl, rfl⟩

/-- `DOFF` below the minimum. -/
theorem spec_refuses_doff_below_minimum (bytes : Octets)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "sizeMismatch" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, beAt_eq]
  rw [if_neg h₁, if_neg h₂, if_pos h₃]
  exact ⟨_, rfl, rfl⟩

/-- `DOFF` putting the body past the octets `SIZE` declares. -/
theorem spec_refuses_doff_past_size (bytes : Octets)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "sizeMismatch" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    beAt_eq]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_pos h₄]
  exact ⟨_, rfl, rfl⟩

/-- A buffer shorter than the octets `SIZE` declares. -/
theorem spec_refuses_buffer_shorter_than_size (bytes : Octets)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "truncated" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    beAt_eq]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_pos h₅]
  exact ⟨_, rfl, rfl⟩

/-- A frame type the artifact does not assign. -/
theorem spec_refuses_unassigned_type (bytes : Octets)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : ¬ (bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₆ : SpecAMQP.Ref.Frame.Kind.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = none) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "unsupported" := by
  have h₆' : SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = none :=
    (ofCode_none_iff _).mpr h₆
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    beAt_eq, h₆']
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅]
  exact ⟨_, rfl, rfl⟩

/-! ### The body, once the frame's own arithmetic has passed

The remaining branches consult the value layer and the body's descriptor. Their hypotheses name
the value layer's answer for the frame's body region — the octets `DOFF` places the body at, to the
end of the buffer — which is what `ValueLayersAgree` below relates between the two layers. -/

/-- The specification's frame type for the type code, where the reference read one. -/
theorem spec_ofCode_of_refCode (bytes : Octets) (kind : SpecAMQP.Ref.Frame.Kind)
    (h : SpecAMQP.Ref.Frame.Kind.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = some kind) :
    ∃ frameType : SpecAMQP.Spec.Frame.FrameType,
      SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = some frameType ∧
      refKind frameType = kind :=
  ofCode_matched _ _ h

/-- A body the value layer refuses with a truncation: the frame layer reports the framing mismatch
the layout's own arithmetic makes of it. Both layers do, and for the same reason. -/
theorem spec_refuses_truncated_body (bytes : Octets) (e : SpecAMQP.Spec.Codec.Refusal)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : ¬ (bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hτ : SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = some frameType)
    (hne : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧ SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2))
    (hdec : SpecAMQP.Spec.Codec.decodeValue
      (bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4)
        bytes.size) = .error e)
    (htrunc : (e.reasonClass == "truncated") = true) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "sizeMismatch" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    SpecAMQP.Spec.Frame.channelOctets, beAt_eq, SpecAMQP.Ref.Frame.wordOctets, hτ]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg hne, hdec]
  dsimp only []
  rw [if_pos htrunc]
  exact ⟨_, rfl, rfl⟩

/-- A body the value layer refuses for any other reason: the frame layer reports that refusal, with
the class its message leads with, and so does the specification's. -/
theorem spec_refuses_body (bytes : Octets) (e : SpecAMQP.Spec.Codec.Refusal)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : ¬ (bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hτ : SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = some frameType)
    (hne : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧ SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2))
    (hdec : SpecAMQP.Spec.Codec.decodeValue
      (bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4)
        bytes.size) = .error e)
    (hpass : ¬ (e.reasonClass == "truncated") = true) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = e.reasonClass := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    SpecAMQP.Spec.Frame.channelOctets, beAt_eq, SpecAMQP.Ref.Frame.wordOctets, hτ]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg hne, hdec]
  dsimp only []
  rw [if_neg hpass]
  exact ⟨_, rfl, rfl⟩

/-- A performative that runs past the `SIZE` its frame declares. -/
theorem spec_refuses_performative_past_size (bytes : Octets) (body : SpecAMQP.Spec.Codec.Value)
    (consumed : Nat)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : ¬ (bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hτ : SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = some frameType)
    (hne : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧ SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2))
    (hdec : SpecAMQP.Spec.Codec.decodeValue
      (bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4)
        bytes.size) = .ok (body, consumed))
    (hpast : SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 + consumed > SpecAMQP.Ref.Frame.beAt bytes 0 4) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "sizeMismatch" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    SpecAMQP.Spec.Frame.channelOctets, beAt_eq, SpecAMQP.Ref.Frame.wordOctets, hτ]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg hne, hdec]
  dsimp only []
  rw [if_pos hpast]
  exact ⟨_, rfl, rfl⟩

/-- A frame body that is not a described type at all. -/
theorem spec_refuses_malformed_body (bytes : Octets) (body : SpecAMQP.Spec.Codec.Value)
    (consumed : Nat)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : ¬ (bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hτ : SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = some frameType)
    (hne : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧ SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2))
    (hdec : SpecAMQP.Spec.Codec.decodeValue
      (bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4)
        bytes.size) = .ok (body, consumed))
    (hpast : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 + consumed > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hnodesc : ∀ (descriptor inner : SpecAMQP.Spec.Codec.Value),
      body ≠ .described descriptor inner) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "malformed" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    SpecAMQP.Spec.Frame.channelOctets, beAt_eq, SpecAMQP.Ref.Frame.wordOctets, hτ, hdec]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg hne, if_neg hpast]
  exact ⟨_, rfl, rfl⟩

/-- A described body whose descriptor names no declared type. -/
theorem spec_refuses_unresolved_descriptor (bytes : Octets)
    (descriptor inner : SpecAMQP.Spec.Codec.Value) (consumed : Nat)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : ¬ (bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hτ : SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = some frameType)
    (hne : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧ SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2))
    (hdec : SpecAMQP.Spec.Codec.decodeValue
      (bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4)
        bytes.size) = .ok (.described descriptor inner, consumed))
    (hpast : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 + consumed > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hdecl : SpecAMQP.Spec.Frame.typeOfDescriptor descriptor = none) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "unsupported" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    SpecAMQP.Spec.Frame.channelOctets, beAt_eq, SpecAMQP.Ref.Frame.wordOctets, hτ, hdec, hdecl]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg hne, if_neg hpast]
  exact ⟨_, rfl, rfl⟩

/-- A described body naming a declared type that does not carry the frame type's role. -/
theorem spec_refuses_role_mismatch (bytes : Octets)
    (descriptor inner : SpecAMQP.Spec.Codec.Value) (consumed : Nat)
    (decl : SpecAMQP.Generated.Oasis.TypeDecl)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : ¬ (bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hτ : SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) = some frameType)
    (hne : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧ SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2))
    (hdec : SpecAMQP.Spec.Codec.decodeValue
      (bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4)
        bytes.size) = .ok (.described descriptor inner, consumed))
    (hpast : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 + consumed > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hdecl : SpecAMQP.Spec.Frame.typeOfDescriptor descriptor = some decl)
    (hrole : decl.provides.contains frameType.role = false) :
    ∃ refusal, SpecAMQP.Spec.Frame.readFrame bytes = .error refusal ∧
      refusal.reasonClass = "unsupported" := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    SpecAMQP.Spec.Frame.channelOctets, beAt_eq, SpecAMQP.Ref.Frame.wordOctets, hτ, hdec, hdecl]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg hne, if_neg hpast, hrole]
  exact ⟨_, rfl, rfl⟩

/-! ### The two branches that accept, as equations

Both accept branches return a frame, so what the specification's reader answers there is an
*equation* about its own reader: the record below is the one the reference's reader built from the
same octets, and the specification reads it too. -/

/-- The empty frame: `SIZE` and `DOFF` at their minimum window the header alone. -/
theorem spec_reads_empty_frame (bytes : Octets) (frameType : SpecAMQP.Spec.Frame.FrameType)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : ¬ (bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hτ : SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) =
      some frameType)
    (h₇ : SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧ SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2) :
    SpecAMQP.Spec.Frame.readFrame bytes =
      .ok (⟨SpecAMQP.Ref.Frame.beAt bytes 4 1, frameType, SpecAMQP.Ref.Frame.beAt bytes 6 2,
          bytes.extract 8 (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4), none, #[]⟩,
        SpecAMQP.Ref.Frame.beAt bytes 0 4) := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    SpecAMQP.Spec.Frame.channelOctets, beAt_eq, hτ]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_pos h₇]

/-- A frame carrying a performative, as the record the reference's reader built: the same body,
the same extent, the same performative. -/
theorem spec_reads_body (bytes : Octets) (frameType : SpecAMQP.Spec.Frame.FrameType)
    (descriptor inner : SpecAMQP.Spec.Codec.Value) (used : Nat)
    (decl : SpecAMQP.Generated.Oasis.TypeDecl)
    (h₁ : ¬ (bytes.size < 8)) (h₂ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8))
    (h₃ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2))
    (h₄ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (h₅ : ¬ (bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hτ : SpecAMQP.Spec.Frame.FrameType.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) =
      some frameType)
    (h₇ : ¬ (SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧ SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2))
    (hdec : SpecAMQP.Spec.Codec.decodeValue
      (bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4) bytes.size) =
        .ok (.described descriptor inner, used))
    (hpast : ¬ (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 + used >
      SpecAMQP.Ref.Frame.beAt bytes 0 4))
    (hdecl : SpecAMQP.Spec.Frame.typeOfDescriptor descriptor = some decl)
    (hrole : decl.provides.contains frameType.role = true) :
    SpecAMQP.Spec.Frame.readFrame bytes =
      .ok (⟨SpecAMQP.Ref.Frame.beAt bytes 4 1, frameType, SpecAMQP.Ref.Frame.beAt bytes 6 2,
          bytes.extract 8 (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4),
          some (.described descriptor inner),
          bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 + used)
            (SpecAMQP.Ref.Frame.beAt bytes 0 4)⟩,
        SpecAMQP.Ref.Frame.beAt bytes 0 4) := by
  unfold SpecAMQP.Spec.Frame.readFrame
  simp only [SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.minDoff, SpecAMQP.Spec.Frame.doffWord, SpecAMQP.Spec.Frame.bodyStart,
    SpecAMQP.Spec.Frame.channelOctets, beAt_eq, hτ]
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, if_neg h₅, if_neg h₇, hdec]
  dsimp only []
  rw [if_neg hpast, hdecl]
  dsimp only []
  rw [if_pos hrole]

/-! ### The agreement, branch by branch

One walk per direction, over the reference's own decision tree: `by_cases` on each of the layout's
questions in the order the layout forces, so that each leaf names the branch of the reference's
reader that answered, and then the corresponding branch lemma for the specification's reader, which
answers the same questions to the same octets. -/

/-- Whatever the reference's frame layer answers for a buffer, the specification's frame layer
answers a frame it also reads, or refuses with the class it also refuses with. -/
theorem ref_answer_matched (valueAgreement : ValueLayersAgree) (bytes : Octets) :
    AnswerMatched (SpecAMQP.Spec.Frame.readFrame bytes)
      (SpecAMQP.Ref.Frame.readFrame bytes) := by
  unfold AnswerMatched
  constructor
  · -- the reference read a frame, so the specification must read the same one
    intro other used hok
    unfold SpecAMQP.Ref.Frame.readFrame at hok
    simp only [] at hok
    dsimp only [SpecAMQP.Ref.Frame.headerOctets, SpecAMQP.Ref.Frame.minDoff,
      SpecAMQP.Ref.Frame.wordOctets, SpecAMQP.Ref.Frame.channelOctets] at hok
    by_cases h₁ : bytes.size < 8
    · rw [if_pos h₁] at hok
      exact absurd hok (by simp)
    · rw [if_neg h₁] at hok
      by_cases h₂ : SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8
      · rw [if_pos h₂] at hok
        exact absurd hok (by simp)
      · rw [if_neg h₂] at hok
        by_cases h₃ : SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2
        · rw [if_pos h₃] at hok
          exact absurd hok (by simp)
        · rw [if_neg h₃] at hok
          by_cases h₄ : SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4
          · rw [if_pos h₄] at hok
            exact absurd hok (by simp)
          · rw [if_neg h₄] at hok
            by_cases h₅ : bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4
            · rw [if_pos h₅] at hok
              exact absurd hok (by simp)
            · rw [if_neg h₅] at hok
              cases hkind : SpecAMQP.Ref.Frame.Kind.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) with
              | none =>
                rw [hkind] at hok
                exact absurd hok (by simp)
              | some kind =>
                rw [hkind] at hok
                dsimp only [] at hok
                obtain ⟨frameType, hτ, hkind'⟩ := ofCode_matched _ _ hkind
                by_cases h₇ : SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧
                  SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2
                · -- the empty frame
                  rw [if_pos h₇] at hok
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hok
                  obtain ⟨rfl, rfl⟩ := hok
                  refine ⟨⟨SpecAMQP.Ref.Frame.beAt bytes 4 1, frameType,
                      SpecAMQP.Ref.Frame.beAt bytes 6 2,
                      bytes.extract 8 (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4), none, #[]⟩,
                    SpecAMQP.Ref.Frame.beAt bytes 0 4,
                    spec_reads_empty_frame bytes frameType h₁ h₂ h₃ h₄ h₅ hτ h₇, rfl, ?_⟩
                  unfold FrameAgrees
                  exact ⟨rfl, hkind', rfl, rfl, rfl, rfl⟩
                · -- a body follows the header
                  rw [if_neg h₇] at hok
                  cases hdec : SpecAMQP.Ref.decode
                      (bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4) bytes.size) with
                  | error failure' =>
                    simp only [hdec] at hok
                    by_cases htrunc : (SpecAMQP.Ref.Frame.valueFailure failure').reasonClass =
                      "truncated"
                    · rw [if_pos htrunc] at hok
                      exact absurd hok (by simp)
                    · rw [if_neg htrunc] at hok
                      exact absurd hok (by simp)
                  | ok answer =>
                    obtain ⟨body, used'⟩ := answer
                    rw [hdec] at hok
                    dsimp only [] at hok
                    by_cases hpast : SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 + used' >
                      SpecAMQP.Ref.Frame.beAt bytes 0 4
                    · rw [if_pos hpast] at hok
                      exact absurd hok (by simp)
                    · rw [if_neg hpast] at hok
                      cases body with
                      | described descriptorRef innerRef =>
                        dsimp only [] at hok
                        cases hdecl : SpecAMQP.Ref.Frame.typeOfDescriptor descriptorRef with
                        | none =>
                          rw [hdecl] at hok
                          exact absurd hok (by simp)
                        | some decl =>
                          rw [hdecl] at hok
                          dsimp only [] at hok
                          by_cases hrole : decl.provides.contains kind.role = true
                          · -- a performative the frame type carries
                            rw [if_pos hrole] at hok
                            simp only [Except.ok.injEq, Prod.mk.injEq] at hok
                            obtain ⟨rfl, rfl⟩ := hok
                            obtain ⟨specBody, hspecDec, hview⟩ :=
                              (valueAgreement (bytes.extract
                                (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4) bytes.size)).1
                                (.described descriptorRef innerRef) used' hdec
                            obtain ⟨descriptor, inner, hdesc⟩ :
                                ∃ d v, specBody = .described d v := by
                              cases specBody with
                              | described d v => exact ⟨d, v, rfl⟩
                              | _ => simp [specBodyView, refBodyView] at hview
                            rw [hdesc] at hspecDec hview
                            have hview' : SpecAMQP.Spec.Frame.typeOfDescriptor descriptor =
                                SpecAMQP.Ref.Frame.typeOfDescriptor descriptorRef := by
                              simpa [specBodyView, refBodyView] using hview
                            have hdecl' : SpecAMQP.Spec.Frame.typeOfDescriptor descriptor =
                                some decl := by rw [hview', hdecl]
                            have hrole' : decl.provides.contains frameType.role = true := by
                              rw [refKind_role, hkind']
                              exact hrole
                            refine ⟨⟨SpecAMQP.Ref.Frame.beAt bytes 4 1, frameType,
                                SpecAMQP.Ref.Frame.beAt bytes 6 2,
                                bytes.extract 8 (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4),
                                some (.described descriptor inner),
                                bytes.extract
                                  (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 + used')
                                  (SpecAMQP.Ref.Frame.beAt bytes 0 4)⟩,
                              SpecAMQP.Ref.Frame.beAt bytes 0 4,
                              spec_reads_body bytes frameType descriptor inner used' decl
                                h₁ h₂ h₃ h₄ h₅ hτ h₇ hspecDec hpast hdecl' hrole', rfl, ?_⟩
                            unfold FrameAgrees
                            refine ⟨rfl, hkind', rfl, ?_, ?_, rfl⟩
                            · simp only [SpecAMQP.Ref.Frame.headerOctets,
                                SpecAMQP.Ref.Frame.wordOctets,
                                SpecAMQP.Spec.Frame.headerOctets,
                                SpecAMQP.Spec.Frame.doffWord,
                                SpecAMQP.Spec.Frame.bodyStart]
                            · simp only [specBodyView, refBodyView, Option.map_some,
                                Option.some.injEq]
                              exact hview'
                          · rw [if_neg hrole] at hok
                            exact absurd hok (by simp)
                      | _ =>
                        dsimp only [] at hok
                        exact absurd hok (by simp)
  · -- the reference refused, so the specification must refuse with the same class
    intro failure herr
    unfold SpecAMQP.Ref.Frame.readFrame at herr
    simp only [] at herr
    dsimp only [SpecAMQP.Ref.Frame.headerOctets, SpecAMQP.Ref.Frame.minDoff,
      SpecAMQP.Ref.Frame.wordOctets, SpecAMQP.Ref.Frame.channelOctets] at herr
    by_cases h₁ : bytes.size < 8
    · rw [if_pos h₁] at herr
      simp only [Except.error.injEq] at herr
      obtain ⟨refusal, hspec, hclass⟩ := spec_refuses_short bytes h₁
      exact ⟨refusal, hspec,
        hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
    · rw [if_neg h₁] at herr
      by_cases h₂ : SpecAMQP.Ref.Frame.beAt bytes 0 4 < 8
      · rw [if_pos h₂] at herr
        simp only [Except.error.injEq] at herr
        obtain ⟨refusal, hspec, hclass⟩ := spec_refuses_size_below_header bytes h₁ h₂
        exact ⟨refusal, hspec,
          hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
      · rw [if_neg h₂] at herr
        by_cases h₃ : SpecAMQP.Ref.Frame.beAt bytes 4 1 < 2
        · rw [if_pos h₃] at herr
          simp only [Except.error.injEq] at herr
          obtain ⟨refusal, hspec, hclass⟩ := spec_refuses_doff_below_minimum bytes h₁ h₂ h₃
          exact ⟨refusal, hspec,
            hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
        · rw [if_neg h₃] at herr
          by_cases h₄ : SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 > SpecAMQP.Ref.Frame.beAt bytes 0 4
          · rw [if_pos h₄] at herr
            simp only [Except.error.injEq] at herr
            obtain ⟨refusal, hspec, hclass⟩ := spec_refuses_doff_past_size bytes h₁ h₂ h₃ h₄
            exact ⟨refusal, hspec,
              hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
          · rw [if_neg h₄] at herr
            by_cases h₅ : bytes.size < SpecAMQP.Ref.Frame.beAt bytes 0 4
            · rw [if_pos h₅] at herr
              simp only [Except.error.injEq] at herr
              obtain ⟨refusal, hspec, hclass⟩ :=
                spec_refuses_buffer_shorter_than_size bytes h₁ h₂ h₃ h₄ h₅
              exact ⟨refusal, hspec,
                hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
            · rw [if_neg h₅] at herr
              cases hkind : SpecAMQP.Ref.Frame.Kind.ofCode (SpecAMQP.Ref.Frame.beAt bytes 5 1) with
              | none =>
                rw [hkind] at herr
                simp only [Except.error.injEq] at herr
                obtain ⟨refusal, hspec, hclass⟩ :=
                  spec_refuses_unassigned_type bytes h₁ h₂ h₃ h₄ h₅ hkind
                exact ⟨refusal, hspec,
                  hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
              | some kind =>
                rw [hkind] at herr
                dsimp only [] at herr
                obtain ⟨frameType, hτ, hkind'⟩ := ofCode_matched _ _ hkind
                by_cases h₇ : SpecAMQP.Ref.Frame.beAt bytes 0 4 = 8 ∧
                  SpecAMQP.Ref.Frame.beAt bytes 4 1 = 2
                · rw [if_pos h₇] at herr
                  exact absurd herr (by simp)
                · rw [if_neg h₇] at herr
                  cases hdec : SpecAMQP.Ref.decode
                      (bytes.extract (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4) bytes.size) with
                  | error failure' =>
                    rw [hdec] at herr
                    dsimp only [] at herr
                    obtain ⟨message, hspecDec, hclass⟩ :=
                      (valueAgreement (bytes.extract
                        (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4) bytes.size)).2 failure' hdec
                    by_cases htrunc : (SpecAMQP.Ref.Frame.valueFailure failure').reasonClass =
                      "truncated"
                    · rw [if_pos htrunc] at herr
                      simp only [Except.error.injEq] at herr
                      obtain ⟨refusal, hspec, hclass'⟩ :=
                        spec_refuses_truncated_body bytes message h₁ h₂ h₃ h₄ h₅ hτ h₇
                          hspecDec (by rw [beq_iff_eq]; exact hclass ▸ htrunc)
                      exact ⟨refusal, hspec,
                        hclass'.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
                    · rw [if_neg htrunc] at herr
                      simp only [Except.error.injEq] at herr
                      obtain ⟨refusal, hspec, hclass'⟩ :=
                        spec_refuses_body bytes message h₁ h₂ h₃ h₄ h₅ hτ h₇ hspecDec
                          (by rw [beq_iff_eq]; exact fun hc => htrunc (hclass.trans hc))
                      refine ⟨refusal, hspec, ?_⟩
                      rw [hclass', ← herr]
                      exact hclass.symm
                  | ok answer =>
                    obtain ⟨body, used'⟩ := answer
                    rw [hdec] at herr
                    dsimp only [] at herr
                    by_cases hpast : SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4 + used' >
                      SpecAMQP.Ref.Frame.beAt bytes 0 4
                    · rw [if_pos hpast] at herr
                      simp only [Except.error.injEq] at herr
                      obtain ⟨message, hspecDec, _⟩ :=
                        (valueAgreement (bytes.extract
                          (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4) bytes.size)).1 _ used' hdec
                      obtain ⟨refusal, hspec, hclass⟩ :=
                        spec_refuses_performative_past_size bytes message used' h₁ h₂ h₃ h₄ h₅ hτ h₇ hspecDec hpast
                      exact ⟨refusal, hspec,
                        hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
                    · rw [if_neg hpast] at herr
                      cases body with
                      | described descriptorRef innerRef =>
                        dsimp only [] at herr
                        cases hdecl : SpecAMQP.Ref.Frame.typeOfDescriptor descriptorRef with
                        | none =>
                          rw [hdecl] at herr
                          simp only [Except.error.injEq] at herr
                          obtain ⟨specBody, hspecDec, hview⟩ :=
                            (valueAgreement (bytes.extract
                              (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4) bytes.size)).1
                              (.described descriptorRef innerRef) used' hdec
                          obtain ⟨descriptor, inner, hdesc⟩ :
                              ∃ d v, specBody = .described d v := by
                            cases specBody with
                            | described d v => exact ⟨d, v, rfl⟩
                            | _ => simp [specBodyView, refBodyView] at hview
                          rw [hdesc] at hspecDec hview
                          have hview' : SpecAMQP.Spec.Frame.typeOfDescriptor descriptor =
                              SpecAMQP.Ref.Frame.typeOfDescriptor descriptorRef := by
                            simpa [specBodyView, refBodyView] using hview
                          have hnone : SpecAMQP.Spec.Frame.typeOfDescriptor descriptor = none := by
                            rw [hview', hdecl]
                          obtain ⟨refusal, hspec, hclass⟩ :=
                            spec_refuses_unresolved_descriptor bytes descriptor inner used' h₁ h₂ h₃
                              h₄ h₅ hτ h₇ hspecDec hpast hnone
                          exact ⟨refusal, hspec,
                            hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
                        | some decl =>
                          rw [hdecl] at herr
                          dsimp only [] at herr
                          by_cases hrole : decl.provides.contains kind.role = true
                          · rw [if_pos hrole] at herr
                            exact absurd herr (by simp)
                          · rw [if_neg hrole] at herr
                            simp only [Except.error.injEq] at herr
                            obtain ⟨specBody, hspecDec, hview⟩ :=
                              (valueAgreement (bytes.extract
                                (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4) bytes.size)).1
                                (.described descriptorRef innerRef) used' hdec
                            obtain ⟨descriptor, inner, hdesc⟩ :
                                ∃ d v, specBody = .described d v := by
                              cases specBody with
                              | described d v => exact ⟨d, v, rfl⟩
                              | _ => simp [specBodyView, refBodyView] at hview
                            rw [hdesc] at hspecDec hview
                            have hview' : SpecAMQP.Spec.Frame.typeOfDescriptor descriptor =
                                SpecAMQP.Ref.Frame.typeOfDescriptor descriptorRef := by
                              simpa [specBodyView, refBodyView] using hview
                            have hsome : SpecAMQP.Spec.Frame.typeOfDescriptor descriptor =
                                some decl := by rw [hview', hdecl]
                            have hrole' : decl.provides.contains frameType.role = false := by
                              rw [refKind_role, hkind']
                              simpa [Bool.not_eq_true] using hrole
                            obtain ⟨refusal, hspec, hclass⟩ :=
                              spec_refuses_role_mismatch bytes descriptor inner used' decl h₁ h₂ h₃ h₄
                                h₅ hτ h₇ hspecDec hpast hsome hrole'
                            exact ⟨refusal, hspec,
                              hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩
                      | _ =>
                        dsimp only [] at herr
                        simp only [Except.error.injEq] at herr
                        obtain ⟨message, hspecDec, hview⟩ :=
                          (valueAgreement (bytes.extract
                            (SpecAMQP.Ref.Frame.beAt bytes 4 1 * 4) bytes.size)).1 _ used' hdec
                        have hnodesc : ∀ (d v : SpecAMQP.Spec.Codec.Value),
                            message ≠ .described d v := by
                          intro d v hd
                          rw [hd] at hview
                          simp [specBodyView, refBodyView] at hview
                        obtain ⟨refusal, hspec, hclass⟩ :=
                          spec_refuses_malformed_body bytes message used' h₁ h₂ h₃ h₄ h₅ hτ h₇
                            hspecDec hpast hnodesc
                        exact ⟨refusal, hspec,
                          hclass.trans (by rw [← herr]; simp only [SpecAMQP.Ref.Frame.refusal])⟩

/-- **The first instance of `Conforms`.** The reference's frame layer is a simulation of the
specification's frame layer, related by `R`, preserving the wire's answer exactly — given the value
layer's reader agreement, which is what the frame layer's body handling rests on and which is
named here rather than assumed silently. -/
theorem ref_frame_conforms (valueAgreement : ValueLayersAgree) :
    ConformsVia R specFrame refFrame := by
  refine ⟨trivial, ?_⟩
  intro s i inp hR out hstep
  -- the reference's step, on each input of the alphabet
  cases inp with
  | tick t =>
    unfold refFrame refStep at hstep
    exact absurd hstep (by simp)
  | api call =>
    unfold refFrame refStep at hstep
    exact absurd hstep (by simp)
  | frame bytes =>
    unfold refFrame refStep at hstep
    dsimp only [] at hstep
    simp only [Option.some.injEq] at hstep
    rw [← hstep]
    -- and the reference's own answer, which the specification matches
    cases href : SpecAMQP.Ref.Frame.readFrame bytes.data with
    | ok answer =>
      obtain ⟨other, used⟩ := answer
      obtain ⟨frame, consumed, hread, hcount, hagrees⟩ :=
        (ref_answer_matched valueAgreement bytes.data).1 other used href
      refine ⟨some (.read frame consumed), [specOutput (.read frame consumed)], ?_, ?_, ?_⟩
      · rw [specFrame_choose_member]
        unfold specFrame specStep
        dsimp only []
        rw [show specAnswer bytes = .read frame consumed by simp [specAnswer, hread]]
      · simp only [refAnswer, href]
        exact ⟨hagrees, hcount⟩
      · simp only [refAnswer, href, specAnswer, hread, refOutput, specOutput]
        rw [← hagrees.2.1, ← refKind_name frame.frameType]
    | error failure =>
      obtain ⟨refusal, hread, hclass⟩ := (ref_answer_matched valueAgreement bytes.data).2 failure href
      refine ⟨some (.refused refusal.reasonClass), [specOutput (.refused refusal.reasonClass)],
        ?_, ?_, ?_⟩
      · rw [specFrame_choose_member]
        unfold specFrame specStep
        dsimp only []
        rw [show specAnswer bytes = .refused refusal.reasonClass by simp [specAnswer, hread]]
      · simp only [refAnswer, href]
        exact hclass
      · simp only [refAnswer, href, specAnswer, hread, refOutput, specOutput]
        rw [hclass]

/-- The same claim in the existential form `Conforms` states, built through the interface's own
`conforms_of_conforms_via` so that the instance is the one the interface defines rather than a
lookalike. -/
theorem ref_frame_conforms_existential (valueAgreement : ValueLayersAgree) :
    Conforms specFrame refFrame :=
  conforms_of_conforms_via specFrame refFrame R (ref_frame_conforms valueAgreement)

end SpecAMQP.Proofs
