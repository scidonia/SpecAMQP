import Contracts.Conformance
import Proofs.FrameConformance
import Proofs.CodecFrameLaws
import Spec.FrameCodec
import Ref.Vectors

/-!
# The frame layer's second `Conforms` instance: the send direction

`Proofs.FrameConformance` instantiates `ConformsVia` for the frame layer's **receive**
direction — octets in, an answer out — and says in its last section that the **send**
direction is not claimed, for two named reasons: the reference exposes no *carrier* for a
frame being written, and there is no value-layer *writer* law. This module checks both
claims rather than inheriting them, and it is the send direction's instance.

## What the send direction's observable step is

An application asks the frame layer to write a frame. The layer answers with the octets it
wrote, on the wire, or with a refusal. So the mapping onto the interface's alphabet is:

* **`Input.api call` is the send direction.** The interface's `ApiCall` is
  `{ name : String, arguments : List String }` — what a call *is* belongs to the endpoint's
  own API — and the frame layer's write call is `⟨"write-frame", [text]⟩`, where `text` is a
  frame in the **corpus vocabulary**: the same rendering a `frame-encode` vector hands an
  artefact (`tests/contracts/frame-vector.schema.json`, read by `Spec.FrameCodec.frameOfJson`
  and `Ref.Vectors.frameOfJson`). That is the carrier the receive instance said did not
  exist, and it does: the corpus vocabulary is the repository's stated comparison vocabulary
  ("comparisons happen in the corpus vocabulary — never between the artefacts' internal
  representations"), and both artefacts already read a frame from it. The frame value crosses
  the interface as the text of that rendering, which each endpoint parses with the same
  reader the corpus runner parses a line with (`Json.parse`).
* **`Output.frame octets` is that answer.** A writer's answer *is* the wire, and `Output`
  carries octets, so unlike the receive direction there is nothing to report second-hand. A
  *refusal* is the other answer: `Output.api ⟨class, false⟩`, the reason class — the class,
  not the prose, for the reason the receive instance gives.
* **`Input.frame` and `Input.tick` are inputs this instance says nothing about.** They
  belong to the receive direction (`Input.frame` is octets arriving on the wire, which the
  first instance already fixed) and to timers the frame layer does not have. The step is
  `none` there and `choose` — the singleton of the step's outcome — is empty, which is what
  the two emptiness lemmas below pin.

## The state

As in the receive direction, a memoryless layer has no state to offer, so the state is
**the frame it built and the answer it gave**: `some (frame, .wrote octets)`,
`some (frame, .refused class)`, or `none` before the first call. `Unit` states would make
`R'` the vacuous `fun _ _ => True`; carrying the frame and the answer is what gives the
relation something to be about.

## The relation

`R'` says the two layers built the same frame and answered alike: on `wrote`, the octets are
literally equal (both are the wire's own type, so equality is the observable); on `refused`,
the reason classes are equal; anything else — a write against a refusal — is false, and
saying so is the point. `FramesWriteAgree` is what "the same frame" means to a *writer*: the
layout's fields equal, the frame type related by `refKind`, and the bodies related by
`BodiesAgree`. It is deliberately a different relation from the receive direction's
`FrameAgrees`, which compares bodies *as the frame layer reads them*: a writer needs more
than a reading — two bodies the reader cannot tell apart can encode differently — and no
more than the value layer's own agreement.

## What it rests on

Two named obligations, both about the **value layer**, and neither is in either tree today —
this is the second thing the receive instance said was missing, and it is a hypothesis rather
than a workaround:

1. `ValueCarrierAgree` — the reference's reading of a corpus value is one the specification
   also reads, and the two readings agree as values (`BodiesAgree`). This is the value-layer
   reader agreement *in the corpus vocabulary*, which is how the frame layer's carrier
   reaches it.
2. `ValueWriterAgree` — bodies that agree as values are written to the same octets, or
   refused with the same class. **This is the writer law the reference does not expose.** It
   is a claim about the value layer, and the value layer's own instance is where it is
   proved. It is quantified over the **carrier-reachable** values (`CarrierReachable`), and
   `PLAN.md` §10 states why: this instance's bodies arrive through its own carrier
   (`frameOfJson` → `valueOfJson`), a body the carrier cannot produce is a body this endpoint
   cannot send, and the endpoint proof supplies the reachability from `frameOfJson`'s own
   construction. **The domain's two boundaries are named here because a boundary explained
   only where it excludes something is half-explained.** It excludes the ill-width family: the
   reference's writer emits a raw payload at whatever width the value carries, so
   `Ref.encode (.float #[]) = .ok #[0x72]` where the specification refuses — a permissive
   writer's property over values no protocol path constructs, since `hexPayloadOf` fixes a
   float's payload at four octets on the way in. And carrier-reachability does **not** imply
   the wire reader's reachability (`ReaderReachable`, which is the domain of the wire-level
   claims, including `ValueLayersAgree`): bridging the two would need a reference writer–reader
   round trip that `Ref` does not expose, which is the same absence that makes this law a
   hypothesis at all. An earlier statement of this law was quantified over every related pair
   and was refuted by that ill-width witness; `Proofs.ValueLayerLaws.not_valueWriterAgree`
   recorded the refutation and was withdrawn in the commit that narrowed the domain, with the
   two artefacts' answers kept there as the witness. There has since been a second cycle of the
   same kind, and the domain did not move this time, so the two are worth telling apart: classing
   the reference's writer — its failure is `Ref.EncodeRefusal` now, a class the kernel can
   compare — made `not_valueWriterAgree` expressible again at a **reachable** hole, an array whose
   declared element constructor the grammar assigns no encoding and which carries no elements.
   The reference wrote it where the specification refused, and it wrote octets its own reader
   refused. The fix that closed the hole (the reference consults its declared constructor before
   its elements) withdrew that refutation too, and `Proofs.ValueLayerLaws` carries both cycles:
   the witness, the class agreement the fixed writers now show for it, and the closure in general.

Assuming a frame-level writer agreement instead would be assuming this direction's
conclusion, so the module states the value-layer law and proves the frame layer's part of it.

## The tie-back, and what would make this vacuous

`specFrameSend_choose_is_the_writer` spells a permitted outcome out in the layer's own
vocabulary: the specification's own writer (`Spec.Frame.writeFrame`), reached through the
specification's own carrier reader (`Spec.FrameCodec.frameOfJson`). With `choose` widened to
`Set.univ` the simulation below still compiles — it only ever consumes membership — and the
tie-back and the two emptiness lemmas fail.

## Whether the negation is true, asked and answered

The question this direction's record has carried and never tested — is `¬ Conforms specFrameSend
refFrameSend` true, is there a reachable input where the two writers part? — is answered at the end of
this module, in the section *the consequent's status*: **undecided**, false before patch 3 and aligned
since, with the search that says so (80,204 frame-encode inputs, its families named, no input on which
the reference takes a step the specification does not permit) and the family agreement that stands where
the last reachable refutation did (`Proofs.ValueLayerLaws.unassignedConstructor_class_agrees`). -/

namespace SpecAMQP.Proofs

open SpecAMQP.Contracts
open SpecAMQP.Harness (Octets)
open Lean (Json)

/-! ## The value layer's relation for written bodies -/

mutual

/-- **The value layer's relation for written frames.** Two bodies agree when they are the
same AMQP value in the two artefacts' representations: the same shape, the same scalar
payload, and the same parts where a value has parts.

The shapes are structural rather than derived, because a writer branches on shape — a body
that is a described value and a body that is not are written by different arms — so a
relation that left the shape to be inferred from a rendering would be leaving the writer's
own decision to a proof about a different function. The parts are structural for the same
reason a value has them at all, and the whole relation is what the value layer can establish
from its own reader and what its own writer law can be stated against. -/
def BodiesAgree : SpecAMQP.Spec.Codec.Value → SpecAMQP.Ref.Value → Prop
  | .null, .null => True
  | .boolean a, .boolean b => a = b
  | .ubyte a, .ubyte b => a = b.toNat
  | .ushort a, .ushort b => a = b.toNat
  | .uint a, .uint b => a = b.toNat
  | .ulong a, .ulong b => a = b.toNat
  | .byte a, .byte b => a = b.toInt
  | .short a, .short b => a = b.toInt
  | .int a, .int b => a = b.toInt
  | .long a, .long b => a = b.toInt
  | .float a, .float b => a = b
  | .double a, .double b => a = b
  | .decimal32 a, .decimal32 b => a = b
  | .decimal64 a, .decimal64 b => a = b
  | .decimal128 a, .decimal128 b => a = b
  | .char a, .char b => a = b.toNat
  | .timestamp a, .timestamp b => a = b.toInt
  | .uuid a, .uuid b => a = b
  | .binary a, .binary b => a.toList = b
  | .string a, .string b => a = b
  | .symbol a, .symbol b => a = b
  | .list a, .list b => BodiesAgreeList a b
  | .map a, .map b => BodiesAgreePairs a b
  | .array constructor a, .array otherConstructor b =>
    constructor = otherConstructor ∧ BodiesAgreeList a b
  | .described descriptor value, .described otherDescriptor otherValue =>
    BodiesAgree descriptor otherDescriptor ∧ BodiesAgree value otherValue
  | _, _ => False
termination_by body other => sizeOf body + sizeOf other

/-- Two lists of values agree when they agree item by item, in order. -/
def BodiesAgreeList : List SpecAMQP.Spec.Codec.Value → List SpecAMQP.Ref.Value → Prop
  | [], [] => True
  | item :: items, other :: others => BodiesAgree item other ∧ BodiesAgreeList items others
  | _, _ => False
termination_by items others => sizeOf items + sizeOf others

/-- Two maps agree when their pairs agree, in the order the wire carried them. -/
def BodiesAgreePairs : List (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Value) →
    List (SpecAMQP.Ref.Value × SpecAMQP.Ref.Value) → Prop
  | [], [] => True
  | (key, value) :: pairs, (otherKey, otherValue) :: others =>
    BodiesAgree key otherKey ∧ BodiesAgree value otherValue ∧ BodiesAgreePairs pairs others
  | _, _ => False
termination_by pairs others => sizeOf pairs + sizeOf others

end

/-- The bodies of two frames agree: both absent, or both present and agreeing. -/
def OptionBodiesAgree : Option SpecAMQP.Spec.Codec.Value → Option SpecAMQP.Ref.Value → Prop
  | none, none => True
  | some body, some other => BodiesAgree body other
  | _, _ => False

/-- **The frame relation the writer needs.** The layout's fields agree, the frame type
agrees up to the two layers' naming of it, and the bodies agree as values. It is not the
receive direction's `FrameAgrees`: what a reader can tell apart and what a writer must agree
on are different questions, and a writer needs the second. -/
def FramesWriteAgree (frame : SpecAMQP.Spec.Frame.Frame)
    (other : SpecAMQP.Ref.Frame.Frame) : Prop :=
  frame.doff = other.doff ∧
  refKind frame.frameType = other.kind ∧
  frame.channel = other.channel ∧
  frame.extended = other.extended ∧
  frame.payload = other.payload ∧
  OptionBodiesAgree frame.body other.body

/-! ## The obligations this instance rests on -/

/-- **The value layer reads the corpus vocabulary the same way.** For every corpus value,
whatever the reference's reader answers is a value the specification's reader also reads,
and the two readings agree as values.

This is a claim about the value layer — its reader, stated in the vocabulary the corpus
already carries — and the value layer's own instance is where it is proved. It is named here
because the frame layer's carrier is a corpus frame, whose body is a corpus value, and
because a frame proof that quietly re-derived a value-layer reading would be claiming another
layer's theorem. -/
def ValueCarrierAgree : Prop :=
  ∀ (json : Json) (other : SpecAMQP.Ref.Value),
    SpecAMQP.Ref.Vectors.valueOfJson 64 json = .ok other →
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson 64 json = .ok body ∧ BodiesAgree body other

/-- **The values this instance's carrier can produce.** A reference value is carrier-reachable
when the corpus reader this instance's own carrier is built on yields it. `PLAN.md` §10 fixes
this as the domain of the writer law below, and the two notions of reachability are not
interchangeable: `FrameConformance.ReaderReachable` is reachability through the *wire* reader
and is the domain of the wire-level claims, while this one is reachability through the
carrier, which is the path this instance's bodies actually arrive by. Bridging the two would
need a reference writer–reader round trip that `Ref` does not expose. -/
def CarrierReachable (v : SpecAMQP.Ref.Value) : Prop :=
  ∃ json : Json, SpecAMQP.Ref.Vectors.valueOfJson 64 json = .ok v

/-- A carrier-reachable value reached by the corpus reader directly. -/
theorem carrierReachable_of_valueOfJson {json : Json} {v : SpecAMQP.Ref.Value}
    (h : SpecAMQP.Ref.Vectors.valueOfJson 64 json = .ok v) : CarrierReachable v :=
  ⟨json, h⟩

/-- **The value layer writes related bodies the same way**, over the values this instance's
carrier can produce: bodies that agree as values are written to the same octets, or refused
with the same reason class.

This is the writer law the reference exposes nowhere and the specification exposes only
against itself (`Contracts.FrameCodec.FrameRoundTripOnEncodedFrames` is the *frame* layer's
own round trip, and it says nothing about another artefact's writer). It is a value-layer
claim, and the value layer's own instance is where it belongs; naming it here is what keeps
this instance from assuming its own conclusion. The domain is `CarrierReachable`, and this
module's head states both of its boundaries with their reasons. -/
def ValueWriterAgree : Prop :=
  ∀ (body : SpecAMQP.Spec.Codec.Value) (other : SpecAMQP.Ref.Value),
    CarrierReachable other →
    BodiesAgree body other →
    (∀ octets : Octets, SpecAMQP.Ref.encode other = .ok octets →
      SpecAMQP.Spec.Codec.encodeValue body = .ok octets) ∧
    (∀ failure : SpecAMQP.Ref.EncodeRefusal,
      SpecAMQP.Ref.encode other = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
        SpecAMQP.Spec.Codec.encodeValue body = .error refusal ∧
        refusal.reasonClass = failure.reasonClass)

/-! ## The layer's answer, and the two endpoints -/

/-- One frame layer's answer to a write call: the octets it wrote, or the class of the
refusal that stopped it. A writer's answer is the wire or a refusal, and this is both. -/
inductive WriteAnswer where
  /-- A frame was written, and these are its octets. -/
  | wrote (octets : Octets)
  /-- No frame: the layer refused, and this is the class of its refusal. -/
  | refused (reasonClass : String)

/-- The name the application's write call carries, whose single argument is the frame in the
corpus vocabulary. The interface's `ApiCall` is opaque (`name`, `arguments`), so what a call
*is* is the endpoint's own API, and this is the frame layer's. -/
def writeCallName : String := "write-frame"

/-- The frame a call names, if it names one: a write call whose single argument is a frame in
the corpus vocabulary, read with the same JSON reader the corpus runner parses a line with. A
call that names no frame gets no answer from this layer, which is why the step is `none` for
it. -/
def carrierOf (call : ApiCall) : Option Json :=
  if call.name = writeCallName then
    match call.arguments with
    | [text] => (Json.parse text).toOption
    | _ => none
  else none

/-- The specification's answer to a carrier: none when its own corpus reader refuses the
frame (a corpus defect, which is the harness's business and not the layer's), otherwise its
own writer's answer. -/
def specWriteAnswer (json : Json) : Option (SpecAMQP.Spec.Frame.Frame × WriteAnswer) :=
  match SpecAMQP.Spec.FrameCodec.frameOfJson json with
  | .error _ => none
  | .ok frame =>
    some (frame, match SpecAMQP.Spec.Frame.writeFrame frame with
      | .ok octets => .wrote octets
      | .error refusal => .refused refusal.reasonClass)

/-- The reference's answer to a carrier, the same shape over the reference's own carrier
reader and writer. -/
def refWriteAnswer (json : Json) : Option (SpecAMQP.Ref.Frame.Frame × WriteAnswer) :=
  match SpecAMQP.Ref.Vectors.frameOfJson json with
  | .error _ => none
  | .ok frame =>
    some (frame, match SpecAMQP.Ref.Frame.writeFrame frame with
      | .ok octets => .wrote octets
      | .error refusal => .refused refusal.reasonClass)

/-- An answer as the interface's alphabet carries it: a frame on the wire, or a refusal
reported as its class. A writer's octets are the harness's own `Octets` — an `Array UInt8`,
which both layers write — and the alphabet's wire is a `ByteArray`. -/
def writeOutput (answer : WriteAnswer) : List Output :=
  match answer with
  | .wrote octets => [.frame (ByteArray.mk octets)]
  | .refused reasonClass => [.api ⟨reasonClass, false⟩]

/-- The specification endpoint's state: the frame it built and the answer it gave, or `none`
before the first call. -/
abbrev SpecSendState := Option (SpecAMQP.Spec.Frame.Frame × WriteAnswer)

/-- The reference endpoint's state, the same thing over the reference's frame type. -/
abbrev RefSendState := Option (SpecAMQP.Ref.Frame.Frame × WriteAnswer)

/-- The specification's step. A write call is answered with the specification's own writer's
answer; every other input of the alphabet belongs to another direction or to a timer this
layer does not have, and gets no answer at all. -/
def specSendStep (_ : SpecSendState) (inp : Input) : Option (SpecSendState × List Output) :=
  match inp with
  | .api call =>
    match carrierOf call with
    | none => none
    | some json =>
      match specWriteAnswer json with
      | none => none
      | some answer => some (some answer, writeOutput answer.2)
  | _ => none

/-- The reference's step, the same shape over the reference's carrier reader and writer. -/
def refSendStep (_ : RefSendState) (inp : Input) : Option (RefSendState × List Output) :=
  match inp with
  | .api call =>
    match carrierOf call with
    | none => none
    | some json =>
      match refWriteAnswer json with
      | none => none
      | some answer => some (some answer, writeOutput answer.2)
  | _ => none

/-- The specification as an endpoint: every permitted outcome is its own writer's answer to
the frame the call names, and nothing else, because `choose` is the singleton of the step's
outcome. A writer has no `MAY` here: the artifact's own latitude in this direction — that an
empty frame *may* be sent, and the negotiated maximum frame size — is a latitude about
*whether* to send, which is the caller's, and this layer's writer refuses an empty frame
outright rather than choosing. -/
def specFrameSend : Endpoint SpecSendState where
  init := none
  step := specSendStep
  choose := fun s inp => {out | specSendStep s inp = some out}

/-- The reference as an endpoint. `ConformsVia` never consults the implementation's
`choose`, which is why the field is empty rather than a second set that could drift. -/
def refFrameSend : Endpoint RefSendState where
  init := none
  step := refSendStep
  choose := fun _ _ => ∅

/-- **The relation**, as described at the head of this module. -/
def R' : SpecSendState → RefSendState → Prop
  | none, none => True
  | some (frame, .wrote octets), some (other, .wrote otherOctets) =>
    FramesWriteAgree frame other ∧ octets = otherOctets
  | some (frame, .refused reasonClass), some (other, .refused otherClass) =>
    FramesWriteAgree frame other ∧ reasonClass = otherClass
  | _, _ => False

/-! ## The tie-back: what the endpoint permits is what the layer does -/

/-- The endpoint's permitted outcomes are its own step's outcome, which is what defines
`choose` rather than a coincidence about it. -/
theorem specFrameSend_choose_member (s : SpecSendState) (inp : Input)
    (out : SpecSendState × List Output) :
    out ∈ specFrameSend.choose s inp ↔ specFrameSend.step s inp = some out := Iff.rfl

/-- **The tie-back, in the layer's own vocabulary.** A permitted outcome on a write call is
exactly the specification's own writer's answer, through the specification's own reading of
the carrier: this frame, written to these octets, or refused with this class. Stated against
`Spec.Frame.writeFrame` and `Spec.FrameCodec.frameOfJson` — the layer's writer and its reader
of the corpus vocabulary — rather than against the endpoint's own step, because a `choose`
tied only to its own wrapper is a proof about a relation the specification does not have. -/
theorem specFrameSend_choose_is_the_writer (s : SpecSendState) (call : ApiCall)
    (s' : SpecSendState) (outs : List Output) :
    (s', outs) ∈ specFrameSend.choose s (.api call) ↔
      ∃ json : Json, carrierOf call = some json ∧
        ((∃ (frame : SpecAMQP.Spec.Frame.Frame) (octets : Octets),
            SpecAMQP.Spec.FrameCodec.frameOfJson json = .ok frame ∧
            SpecAMQP.Spec.Frame.writeFrame frame = .ok octets ∧
            s' = some (frame, .wrote octets) ∧ outs = [Output.frame (ByteArray.mk octets)]) ∨
         (∃ (frame : SpecAMQP.Spec.Frame.Frame) (refusal : SpecAMQP.Spec.Frame.Refusal),
            SpecAMQP.Spec.FrameCodec.frameOfJson json = .ok frame ∧
            SpecAMQP.Spec.Frame.writeFrame frame = .error refusal ∧
            s' = some (frame, .refused refusal.reasonClass) ∧
            outs = [Output.api ⟨refusal.reasonClass, false⟩])) := by
  rw [specFrameSend_choose_member]
  unfold specFrameSend specSendStep specWriteAnswer writeOutput
  dsimp only []
  cases hcarrier : carrierOf call with
  | none => grind
  | some json =>
    cases hreader : SpecAMQP.Spec.FrameCodec.frameOfJson json with
    | error message => simp only [hreader]; grind
    | ok frame =>
      cases hwriter : SpecAMQP.Spec.Frame.writeFrame frame with
      | ok octets => simp only [hreader, hwriter]; grind
      | error refusal => simp only [hreader, hwriter]; grind

/-- The endpoint permits nothing on octets arriving: that input is the receive direction,
which the first instance covers, and a writer has no answer for it. An anti-vacuity guard —
with `choose` widened to `Set.univ` this fails. -/
theorem specFrameSend_choose_frame_empty (s : SpecSendState) (bytes : ByteArray) :
    specFrameSend.choose s (.frame bytes) = ∅ := by
  unfold specFrameSend specSendStep
  dsimp only []
  ext out
  simp

/-- And nothing on a tick: the frame layer has no timers. -/
theorem specFrameSend_choose_tick_empty (s : SpecSendState) (tick : Tick) :
    specFrameSend.choose s (.tick tick) = ∅ := by
  unfold specFrameSend specSendStep
  dsimp only []
  ext out
  simp

/-! ## The carrier: the same frame from the same rendering

The two artefacts read a corpus frame with their own reader — `Spec.FrameCodec.frameOfJson`
and `Ref.Vectors.frameOfJson` — which are the same reading of the vocabulary written twice:
the same fields, in the same order, through the same harness helpers (`ofHex`,
`getObjValAs?`), differing only where the two artefacts genuinely differ (their frame type
dispatch, their value reader, their prose). So this is one walk of the reference's reader
against the specification's, with the value layer's reader agreement (`ValueCarrierAgree`)
supplying the body and the type-code agreement supplying the rest. -/

/-- Whatever frame the reference's carrier reader builds from a corpus frame, the
specification's reader builds a frame agreeing with it, or the reference builds none. -/
theorem carriers_matched (carrier : ValueCarrierAgree) (json : Json)
    (other : SpecAMQP.Ref.Frame.Frame)
    (hread : SpecAMQP.Ref.Vectors.frameOfJson json = .ok other) :
    ∃ frame : SpecAMQP.Spec.Frame.Frame,
      SpecAMQP.Spec.FrameCodec.frameOfJson json = .ok frame ∧ FramesWriteAgree frame other := by
  unfold SpecAMQP.Ref.Vectors.frameOfJson at hread
  unfold SpecAMQP.Spec.FrameCodec.frameOfJson
  simp only [Bind.bind, Except.bind] at hread ⊢
  -- the two readers read the same fields in the same order through the same helpers, so
  -- each shared sub-expression is one case split for both of them
  cases hdoff : json.getObjValAs? Nat "doff" with
  | error err => simp [hdoff] at hread
  | ok doff =>
    simp only [hdoff] at hread ⊢
    cases hchan : json.getObjValAs? Nat "channel" with
    | error err => simp [hchan] at hread
    | ok channel =>
      simp only [hchan] at hread ⊢
      cases hty : SpecAMQP.Harness.ofHex
          ((json.getObjValAs? String "type").toOption.getD "") with
      | error err => simp [hty] at hread
      | ok typeOctets =>
        simp only [hty] at hread ⊢
        cases hlist : typeOctets.toList with
        | nil => simp [hlist] at hread
        | cons code rest =>
          simp only [hlist] at hread ⊢
          cases hrest : rest with
          | nil =>
            simp only [hrest] at hread ⊢
            cases hkind : SpecAMQP.Ref.Frame.Kind.ofCode code.toNat with
            | none => simp [hkind] at hread
            | some kind =>
              simp only [hkind] at hread ⊢
              obtain ⟨frameType, hft, hkindEq⟩ := ofCode_matched code.toNat kind hkind
              simp only [hft] at ⊢
              cases hext : SpecAMQP.Harness.ofHex
                  ((json.getObjValAs? String "extended").toOption.getD "") with
              | error err => simp [hext] at hread
              | ok extended =>
                simp only [hext] at hread ⊢
                cases hpay : SpecAMQP.Harness.ofHex
                    ((json.getObjValAs? String "payload").toOption.getD "") with
                | error err => simp [hpay] at hread
                | ok payload =>
                  simp only [hpay] at hread ⊢
                  cases hbody : json.getObjValAs? (Array Json) "body" with
                  | error err => simp [hbody] at hread
                  | ok bodyOctets =>
                    simp only [hbody] at hread ⊢
                    cases hblist : bodyOctets.toList with
                    | nil =>
                      -- the empty frame: a header and nothing else
                      simp only [hblist] at hread ⊢
                      simp only [Except.ok.injEq] at hread
                      subst hread
                      refine ⟨_, rfl, ?_⟩
                      simp only [FramesWriteAgree, OptionBodiesAgree]
                      exact ⟨trivial, hkindEq, trivial, trivial, trivial, trivial⟩
                    | cons valueJson brest =>
                      simp only [hblist] at hread ⊢
                      cases hbrest : brest with
                      | cons extra rest' => simp [hbrest] at hread
                      | nil =>
                        simp only [hbrest] at hread ⊢
                        -- the body: the value layer's reading, which is what this rests on
                        cases hval : SpecAMQP.Ref.Vectors.valueOfJson 64 valueJson with
                        | error err => simp [hval] at hread
                        | ok otherBody =>
                          simp only [hval] at hread ⊢
                          obtain ⟨specBody, hspecVal, hagree⟩ :=
                            carrier valueJson otherBody hval
                          simp only [hspecVal] at ⊢
                          simp only [Except.ok.injEq] at hread
                          subst hread
                          refine ⟨_, rfl, ?_⟩
                          simp only [FramesWriteAgree, OptionBodiesAgree]
                          exact ⟨trivial, hkindEq, trivial, trivial, trivial, hagree⟩
          | cons code' rest' => simp [hrest] at hread

/-! ## The layout's arithmetic, as the two layers spell it

Both layers transcribe the same layout — the same minimum DOFF, the same one-octet DOFF
field, the same two CHANNEL octets, the same four-octet SIZE — and the reference writes them
as its own named constants while the specification spells some of them out. These lemmas say
the two spellings are the same value, and they are proved rather than tested: a layout that
drifted between the artefacts is exactly what this instance exists to catch. -/

theorem ref_minDoff_spelling : SpecAMQP.Ref.Frame.minDoff = SpecAMQP.Spec.Frame.minDoff := rfl

theorem ref_wordOctets_spelling :
    SpecAMQP.Ref.Frame.wordOctets = SpecAMQP.Spec.Frame.doffWord := rfl

theorem ref_headerOctets_spelling :
    SpecAMQP.Ref.Frame.headerOctets = SpecAMQP.Spec.Frame.headerOctets := rfl

theorem ref_maxDoff_spelling :
    SpecAMQP.Ref.Frame.maxDoff = 2 ^ (8 * SpecAMQP.Spec.Frame.doffOctets) - 1 := rfl

theorem ref_maxChannel_spelling :
    SpecAMQP.Ref.Frame.maxChannel = 2 ^ (8 * SpecAMQP.Spec.Frame.channelOctets) - 1 := by
  simp only [SpecAMQP.Ref.Frame.maxChannel, SpecAMQP.Spec.Frame.channelOctets]

theorem ref_maxSize_spelling : SpecAMQP.Ref.Frame.maxSize = SpecAMQP.Spec.Frame.maxSize := by
  simp only [SpecAMQP.Ref.Frame.maxSize, SpecAMQP.Spec.Frame.maxSize]

/-! ## The header both writers emit, octet for octet

A writer's answer *is* the octets, so the two layers' four header fields have to agree
octet for octet and not merely field for field. The specification writes each field through
`beOctets`, big-endian, most significant first; the reference writes literal arrays. The
identities below are what makes them the same octets — and they hold for every value, because
both writers reduce a field to the octets the field can carry and `UInt8.ofNat` reduces
modulo 256 on its own. -/

/-- Writing `n` mod 256 and writing `n` are the same octet, which is what `UInt8.ofNat`
being a modulo-256 reading makes true. -/
theorem u8_ofNat_mod (n : Nat) : UInt8.ofNat (n % 256) = UInt8.ofNat n := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_mod]

/-- The one-octet field of `beOctets`: `DOFF`'s own width. -/
theorem beOctets_one (n : Nat) : SpecAMQP.Spec.Codec.beOctets 1 n = [UInt8.ofNat n] := by
  simp only [SpecAMQP.Spec.Codec.beOctets, SpecAMQP.Spec.Codec.beOctets.go, u8_ofNat_mod,
    List.reverse_cons, List.reverse_nil, List.nil_append]

/-- The two-octet field: `CHANNEL`'s width. -/
theorem beOctets_two (n : Nat) :
    SpecAMQP.Spec.Codec.beOctets 2 n = [UInt8.ofNat (n / 256), UInt8.ofNat n] := by
  simp only [SpecAMQP.Spec.Codec.beOctets, SpecAMQP.Spec.Codec.beOctets.go, u8_ofNat_mod,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]

/-- The four-octet field: `SIZE`'s width, and the one the writer's own arithmetic is
about. -/
theorem beOctets_four (n : Nat) :
    SpecAMQP.Spec.Codec.beOctets 4 n =
      [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256),
        UInt8.ofNat n] := by
  have h1 : (256 : Nat) * 256 = 65536 := by decide
  have h2 : (256 : Nat) * 256 * 256 = 16777216 := by decide
  simp only [SpecAMQP.Spec.Codec.beOctets, SpecAMQP.Spec.Codec.beOctets.go,
    Nat.div_div_eq_div_mul, u8_ofNat_mod, h1, h2, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]

/-- The reference's four-octet writer, in the form the specification's has. -/
theorem u32be_form (n : Nat) :
    SpecAMQP.Ref.u32be n =
      #[UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256),
        UInt8.ofNat n] := by
  simp only [SpecAMQP.Ref.u32be, Nat.toUInt8]

/-- The reference's two-octet writer, the same. -/
theorem u16be_form (n : Nat) :
    SpecAMQP.Ref.u16be n = #[UInt8.ofNat (n / 256), UInt8.ofNat n] := by
  simp only [SpecAMQP.Ref.u16be, Nat.toUInt8]

/-- **The header is the same octets in both layers**: SIZE, DOFF, TYPE and CHANNEL, in the
layout's order, written by the specification through `beOctets` and by the reference as
literal arrays. -/
theorem header_writers_agree (size doff code channel : Nat) :
    ((SpecAMQP.Spec.Codec.beOctets SpecAMQP.Spec.Frame.sizeOctets size ++
        SpecAMQP.Spec.Codec.beOctets 1 doff ++
        SpecAMQP.Spec.Codec.beOctets 1 code ++
        SpecAMQP.Spec.Codec.beOctets SpecAMQP.Spec.Frame.channelOctets channel).toArray)
      = (SpecAMQP.Ref.u32be size ++ #[UInt8.ofNat doff] ++ #[UInt8.ofNat code] ++
          SpecAMQP.Ref.u16be channel) := by
  simp only [SpecAMQP.Spec.Frame.sizeOctets, SpecAMQP.Spec.Frame.channelOctets,
    beOctets_four, beOctets_one, beOctets_two, u32be_form, u16be_form,
    SpecAMQP.Proofs.toArray_append_list]

/-- The frame type's code octet is the same one the specification writes for it, so the TYPE
field agrees when the frame types agree. -/
theorem refKind_code (frameType : SpecAMQP.Spec.Frame.FrameType) :
    (refKind frameType).code = frameType.code := by
  cases frameType <;> rfl

/-! ## What the two layers read out of a body -/

/-- **The declared type a body's descriptor names is the same in both layers** when the bodies
agree as values. Both layers look the descriptor up in the same generated table by the same
predicate — a `ulong` carrying the declared `domain:code`, or the type's symbolic name — so
this is a claim about the relation reaching the lookup, not about the surface. -/
theorem typeOfDescriptor_agree {body : SpecAMQP.Spec.Codec.Value}
    {other : SpecAMQP.Ref.Value} (h : BodiesAgree body other) :
    SpecAMQP.Spec.Frame.typeOfDescriptor body =
      SpecAMQP.Ref.Frame.typeOfDescriptor other := by
  cases body <;> cases other <;>
    simp only [BodiesAgree, SpecAMQP.Spec.Frame.typeOfDescriptor,
      SpecAMQP.Ref.Frame.typeOfDescriptor] at h ⊢ <;>
    (try rw [h]) <;> rfl

/-! ## What the two writers answer -/

/-- **The two writers' answers agree**: whatever the reference's writer answers for its frame,
the specification's writer answers the same for a frame related to it — the same octets, or a
refusal of the same class. This is the frame-layer shape of the claim, and the class rather
than the prose, for the reason the receive direction gives. -/
def WriteAgrees (spec : Except SpecAMQP.Spec.Frame.Refusal Octets)
    (ref : Except SpecAMQP.Ref.Frame.Refusal Octets) : Prop :=
  (∀ octets : Octets, ref = .ok octets → spec = .ok octets) ∧
  (∀ refusal : SpecAMQP.Ref.Frame.Refusal, ref = .error refusal →
    ∃ specRefusal : SpecAMQP.Spec.Frame.Refusal,
      spec = .error specRefusal ∧ specRefusal.reasonClass = refusal.reasonClass)

/-- Both writers wrote the same octets. -/
theorem writeAgrees_ok (octets : Octets) :
    WriteAgrees (.ok octets : Except SpecAMQP.Spec.Frame.Refusal Octets)
      (.ok octets : Except SpecAMQP.Ref.Frame.Refusal Octets) :=
  ⟨fun other h => by simpa using h, fun refusal h => by simp at h⟩

/-- Both writers refused, naming the same class. The classes are what agreement means, and the
prose each layer spells for itself is free to differ. -/
theorem writeAgrees_error (reasonClass specMessage refMessage : String) :
    WriteAgrees
      (.error ⟨reasonClass, specMessage⟩ : Except SpecAMQP.Spec.Frame.Refusal Octets)
      (.error ⟨reasonClass, refMessage⟩ : Except SpecAMQP.Ref.Frame.Refusal Octets) := by
  refine ⟨fun octets h => by simp at h, fun refusal h => ?_⟩
  cases refusal with
  | mk reasonClass' message =>
    simp only [Except.error.injEq, SpecAMQP.Ref.Frame.Refusal.mk.injEq] at h
    exact ⟨⟨reasonClass, specMessage⟩, rfl, h.1⟩

/-! ## The writer: the same octets from related frames -/

/-- **A frame the carrier built holds a carrier-reachable body.** `frameOfJson` reads its body
with `valueOfJson`, so whatever value it puts in the frame is one the corpus reader produced —
which is the reachability `writers_matched` takes as a parameter.

**How to walk a `do`-block like this one.** Each shared read is one `cases` split, in the order the
block performs them, and each failing branch is closed by the bind's own propagation
(`| error err => simp [hread] at h`) — the shape `carriers_matched` uses for the same block. What
does *not* work is casing the one read you want and leaving the enclosing reads as binds: the goal
is then a chain of `match`es whose `simp` cannot propagate an inner `.error` through, so the
failing branch is left unsolved with a nested-match goal. That was this lemma's first attempt —
casing the body read alone, five binds deep, and `simp`/`simp_all` could not close it — and the
fix is to walk the block from its first read. A caller that needs an early read's value therefore
pays for the reads before it, which is the price of the artefact's own top-to-bottom order. -/
theorem carrierReachable_body_of_frameOfJson {json : Json} {other : SpecAMQP.Ref.Frame.Frame}
    (h : SpecAMQP.Ref.Vectors.frameOfJson json = .ok other)
    {obody : SpecAMQP.Ref.Value} (hb : other.body = some obody) : CarrierReachable obody := by
  unfold SpecAMQP.Ref.Vectors.frameOfJson at h
  simp only [Bind.bind, Except.bind] at h
  cases hdoff : json.getObjValAs? Nat "doff" with
  | error err => simp [hdoff] at h
  | ok doff =>
    simp only [hdoff] at h
    cases hchan : json.getObjValAs? Nat "channel" with
    | error err => simp [hchan] at h
    | ok channel =>
      simp only [hchan] at h
      cases hty : SpecAMQP.Harness.ofHex
          ((json.getObjValAs? String "type").toOption.getD "") with
      | error err => simp [hty] at h
      | ok typeOctets =>
        simp only [hty] at h
        cases hlist : typeOctets.toList with
        | nil => simp [hlist] at h
        | cons code rest =>
          simp only [hlist] at h
          cases hrest : rest with
          | cons extra rest' => simp [hrest] at h
          | nil =>
            simp only [hrest] at h
            cases hkind : SpecAMQP.Ref.Frame.Kind.ofCode code.toNat with
            | none => simp [hkind] at h
            | some kind =>
              simp only [hkind] at h
              cases hext : SpecAMQP.Harness.ofHex
                  ((json.getObjValAs? String "extended").toOption.getD "") with
              | error err => simp [hext] at h
              | ok extended =>
                simp only [hext] at h
                cases hpay : SpecAMQP.Harness.ofHex
                    ((json.getObjValAs? String "payload").toOption.getD "") with
                | error err => simp [hpay] at h
                | ok payload =>
                  simp only [hpay] at h
                  cases hbody : json.getObjValAs? (Array Json) "body" with
                  | error err => simp [hbody] at h
                  | ok bodyOctets =>
                    simp only [hbody] at h
                    cases hblist : bodyOctets.toList with
                    | nil =>
                      -- a bodyless frame: the reachability claim has no value to be about
                      simp only [hblist] at h
                      simp only [Except.ok.injEq] at h
                      subst h
                      cases hb
                    | cons valueJson brest =>
                      simp only [hblist] at h
                      cases hbrest : brest with
                      | cons extra rest' => simp [hbrest] at h
                      | nil =>
                        -- one body value: the corpus reader produced it, so it is reachable
                        simp only [hbrest] at h
                        cases hval : SpecAMQP.Ref.Vectors.valueOfJson 64 valueJson with
                        | error err => simp [hval] at h
                        | ok value =>
                          simp only [hval] at h
                          simp only [Except.ok.injEq] at h
                          subst h
                          simp only [Option.some.injEq] at hb
                          subst hb
                          exact carrierReachable_of_valueOfJson hval

/-- The writer law, applied to two frames: the reachability of whatever body the reference frame
holds is a parameter, because this lemma relates *arbitrary* related frames and cannot derive it
for them. The caller — the endpoint proof, where the frame came from `frameOfJson` — supplies it
through `carrierReachable_body_of_frameOfJson`. -/
theorem writers_matched (writers : ValueWriterAgree)
    (frame : SpecAMQP.Spec.Frame.Frame) (other : SpecAMQP.Ref.Frame.Frame)
    (hrel : FramesWriteAgree frame other)
    (reach : ∀ (obody : SpecAMQP.Ref.Value), other.body = some obody → CarrierReachable obody) :
    WriteAgrees (SpecAMQP.Spec.Frame.writeFrame frame)
      (SpecAMQP.Ref.Frame.writeFrame other) := by
  obtain ⟨hdoff, hkind, hchan, hext, hpay, hbodies⟩ := hrel
  cases frame with
  | mk sdoff sframeType schannel sextended sbody spayload =>
  cases other with
  | mk rdoff rkind rchannel rextended rbody rpayload =>
  subst hdoff
  subst hchan
  subst hext
  subst hpay
  subst hkind
  unfold SpecAMQP.Spec.Frame.writeFrame SpecAMQP.Ref.Frame.writeFrame
  simp only [ref_minDoff_spelling, ref_wordOctets_spelling, ref_headerOctets_spelling,
    ref_maxDoff_spelling, ref_maxChannel_spelling, ref_maxSize_spelling,
    SpecAMQP.Spec.Frame.bodyStart, Bind.bind, Except.bind]
  -- the layout's arithmetic, in the order both layers check it
  by_cases h₁ : sdoff < SpecAMQP.Spec.Frame.minDoff
  · simp only [h₁, if_true] at ⊢
    exact writeAgrees_error _ _ _
  · simp only [h₁, if_false] at ⊢
    by_cases h₂ : schannel > 2 ^ (8 * SpecAMQP.Spec.Frame.channelOctets) - 1
    · simp only [h₂, if_true] at ⊢
      exact writeAgrees_error _ _ _
    · simp only [h₂, if_false] at ⊢
      by_cases h₃ : sdoff > 2 ^ (8 * SpecAMQP.Spec.Frame.doffOctets) - 1
      · simp only [h₃, if_true] at ⊢
        exact writeAgrees_error _ _ _
      · simp only [h₃, if_false] at ⊢
        by_cases h₄ : (sextended.size != sdoff * SpecAMQP.Spec.Frame.doffWord -
            SpecAMQP.Spec.Frame.headerOctets) = true
        · simp only [h₄, if_true] at ⊢
          exact writeAgrees_error _ _ _
        · simp only [h₄, Bool.false_eq_true, if_false] at ⊢
          -- the body: the relation fixes its presence and its shape, and a frame layer
          -- reads nothing else out of one
          cases sbody with
          | none =>
            cases rbody with
            | none =>
              simp only [OptionBodiesAgree] at hbodies
              exact writeAgrees_error _ _ _
            | some obody =>
              simp only [OptionBodiesAgree] at hbodies
          | some body =>
            cases rbody with
            | none =>
              simp only [OptionBodiesAgree] at hbodies
            | some obody =>
              simp only [OptionBodiesAgree] at hbodies
              cases body with
              | described descriptor value =>
                cases obody with
                | described oDescriptor oValue =>
                  obtain ⟨hdesc, hval⟩ : BodiesAgree descriptor oDescriptor ∧
                      BodiesAgree value oValue := by
                    simpa only [BodiesAgree] using hbodies
                  -- both layers' role test reads the same declared type
                  have hwatch : SpecAMQP.Spec.Frame.carriesPerformative sframeType descriptor =
                      SpecAMQP.Ref.Frame.isPerformativeFor (refKind sframeType) oDescriptor := by
                    unfold SpecAMQP.Spec.Frame.carriesPerformative
                      SpecAMQP.Ref.Frame.isPerformativeFor
                    rw [typeOfDescriptor_agree hdesc, refKind_role]
                    rfl
                  simp only [hwatch] at ⊢
                  by_cases hrole : (!SpecAMQP.Ref.Frame.isPerformativeFor (refKind sframeType)
                      oDescriptor) = true
                  · simp only [hrole, if_true] at ⊢
                    -- the role test fails: both layers name the same class
                    rw [typeOfDescriptor_agree hdesc] at ⊢
                    cases hl : SpecAMQP.Ref.Frame.typeOfDescriptor oDescriptor <;>
                      simp only [] at ⊢ <;> exact writeAgrees_error _ _ _
                  · simp only [hrole, Bool.false_eq_true, if_false] at ⊢
                    -- the role test passes: the bodies are written by the value layer's law
                    obtain ⟨hwok, hwerr⟩ :=
                      writers (.described descriptor value) (.described oDescriptor oValue)
                        (reach _ rfl) hbodies
                    cases henc : SpecAMQP.Ref.encode (.described oDescriptor oValue) with
                    | error failure =>
                      obtain ⟨specRefusal, hspecEnc, hclass⟩ := hwerr failure henc
                      simp only [hspecEnc, hclass] at ⊢
                      exact writeAgrees_error _ _ _
                    | ok octets =>
                      simp only [hwok octets henc] at ⊢
                      rw [refKind_code sframeType] at ⊢
                      rw [header_writers_agree] at ⊢
                      by_cases hsize : SpecAMQP.Spec.Frame.headerOctets + sextended.size +
                          octets.size + spayload.size ≤ SpecAMQP.Spec.Frame.maxSize
                      · simp only [hsize] at ⊢
                        exact writeAgrees_ok _
                      · simp only [hsize] at ⊢
                        exact writeAgrees_error _ _ _
                | _ =>
                  simp only [BodiesAgree] at hbodies
              | _ =>
                -- the specification refuses a body that is not a described value, and the
                -- relation says the reference's body has the same shape
                cases obody <;> simp only [BodiesAgree] at hbodies ⊢
                exact writeAgrees_error _ _ _

/-! ## The instance -/

/-- **The frame layer's second instance of `Conforms`.** The reference's frame writer is a
simulation of the specification's frame writer on the corpus vocabulary's frames, related by
`R'`, preserving the wire exactly — given the value layer's two agreements, which are what
writing a body rests on and which are named here rather than assumed silently. -/
theorem ref_frame_send_conforms (carriers : ValueCarrierAgree) (writers : ValueWriterAgree) :
    ConformsVia R' specFrameSend refFrameSend := by
  refine ⟨trivial, ?_⟩
  intro s i inp hR out hstep
  -- the reference's step, on each input of the alphabet
  cases inp with
  | tick tick =>
    unfold refFrameSend refSendStep at hstep
    exact absurd hstep (by simp)
  | frame bytes =>
    unfold refFrameSend refSendStep at hstep
    exact absurd hstep (by simp)
  | api call =>
    obtain ⟨refState, refOuts⟩ := out
    unfold refFrameSend refSendStep at hstep
    dsimp only [] at hstep
    cases hcarrier : carrierOf call with
    | none => simp [hcarrier] at hstep
    | some json =>
      simp only [hcarrier] at hstep
      cases hanswer : refWriteAnswer json with
      | none => simp [hanswer] at hstep
      | some answer =>
        obtain ⟨other, wanswer⟩ := answer
        simp only [hanswer, Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨hstate, houts⟩ := hstep
        -- the reference's own frame, and its own writer's answer
        unfold refWriteAnswer at hanswer
        cases href : SpecAMQP.Ref.Vectors.frameOfJson json with
        | error message => simp [href] at hanswer
        | ok refFrame =>
          simp only [href] at hanswer
          -- the carrier agreement gives the specification the same frame, and the writer
          -- agreement gives it the same answer
          obtain ⟨frame, hspecFrame, hfrel⟩ := carriers_matched carriers json refFrame href
          have hwrite := writers_matched writers frame refFrame hfrel
            (fun obody hb => carrierReachable_body_of_frameOfJson href hb)
          cases hw : SpecAMQP.Ref.Frame.writeFrame refFrame with
          | ok octets =>
            simp only [hw, Option.some.injEq, Prod.mk.injEq] at hanswer
            rw [← hanswer.2] at hstate houts
            rw [← hanswer.1] at hstate
            have hspecWrite : SpecAMQP.Spec.Frame.writeFrame frame = .ok octets :=
              hwrite.1 octets hw
            have hspecAnswer : specWriteAnswer json = some (frame, .wrote octets) := by
              unfold specWriteAnswer
              simp only [hspecFrame, hspecWrite]
            refine ⟨some (frame, .wrote octets), writeOutput (.wrote octets), ?_, ?_, ?_⟩
            · rw [specFrameSend_choose_member]
              unfold specFrameSend specSendStep
              dsimp only []
              simp only [hcarrier, hspecAnswer]
            · rw [← hstate]
              exact ⟨hfrel, rfl⟩
            · exact houts.symm
          | error refusal =>
            simp only [hw, Option.some.injEq, Prod.mk.injEq] at hanswer
            rw [← hanswer.2] at hstate houts
            rw [← hanswer.1] at hstate
            obtain ⟨specRefusal, hspecWrite, hclass⟩ := hwrite.2 refusal hw
            have hspecAnswer : specWriteAnswer json =
                some (frame, .refused specRefusal.reasonClass) := by
              unfold specWriteAnswer
              simp only [hspecFrame, hspecWrite]
            refine ⟨some (frame, .refused specRefusal.reasonClass),
              writeOutput (.refused specRefusal.reasonClass), ?_, ?_, ?_⟩
            · rw [specFrameSend_choose_member]
              unfold specFrameSend specSendStep
              dsimp only []
              simp only [hcarrier, hspecAnswer]
            · rw [← hstate]
              exact ⟨hfrel, hclass⟩
            · rw [hclass]
              exact houts.symm

/-- The same claim in the existential form `Conforms` states, built through the interface's
own `conforms_of_conforms_via` so that the instance is the one the interface defines rather
than a lookalike. -/
theorem ref_frame_send_conforms_existential (carriers : ValueCarrierAgree)
    (writers : ValueWriterAgree) : Conforms specFrameSend refFrameSend :=
  conforms_of_conforms_via specFrameSend refFrameSend R' (ref_frame_send_conforms carriers writers)

/-! ## The consequent's status: **undecided**, and the search that says so

This module is where the send direction's status is recorded, and the question it was written to answer
is the negative one: is `¬ Conforms specFrameSend refFrameSend` true — is there a reachable input where
the reference writes and the specification refuses, or the two write different octets, or both refuse
with different classes? The record's answer, and the evidence for it, are these:

* **It was true before patch 3, at the array-body class divergence, and no longer.** `.array 0x00 [null]`
  and `.array 0xE0 [null]` were accepted by both carriers, refused `malformed` by the specification's
  writer (the item is not what the declared row carries) and refused `limit` by the reference's
  `arrayElement` catch-all. Two classes for one observable, on a reachable body: that was the falsity.
  Patch 3 split the catch-all into `unassigned` and `malformed`, and the classes agree.
* **The classing made the negation expressible, and by then the hole it was expressible at had closed.**
  The reference's writer answers a classed `EncodeRefusal` now, so its class is a field rather than
  something recovered by splitting a sentence — which removed the *type* obstruction the earlier record
  named, and is what let `Proofs.ValueLayerLaws` carry (and then withdraw) the value-layer refutation at
  the empty-array hole. That hole was the *shape* divergence: `Ref.encode (.array 0x57 [])` wrote
  `#[0xE0,0x02,0x00,0x57]`, octets the reference's own reader refused, where the specification refused
  `unassigned`. The fix that made the reference consult an array's declared constructor before its
  elements withdrew that refutation, and the family it lived in is a *class agreement* now —
  `Proofs.ValueLayerLaws.unassignedConstructor_class_agrees`, general in the constructor and in the item
  list, is the nearest true statement where the refutation stood.
* **So the question is empirical, and it was asked of the artefacts rather than left untried.** A
  witness is a corpus frame whose body is a described performative carrying a value the two writers part
  on, so the search is over the frames this layer's carrier can build: **80,204 frame-encode inputs**
  through each artefact's own `frameOfJson` and `writeFrame`, compared on class and octets. The families:
  every one of the 256 array element constructors against a **113-item pool** of in-range, out-of-range
  and mismatched shapes (28,928 inputs), and against 43 shapes at one and two elements (22,016); the
  `%x00` descriptor prefix and the `%x40`–`%x45`, `%xC0`/`%xC1`, `%xD0`/`%xD1`, `%xE0`/`%xF0` rows
  against that pool; the materialisation limit at 65,535 / 65,536 / 65,537 elements; nesting depth 30–100
  across the corpus reader's fuel bound; string, symbol and binary lengths 0–300 across the 255/256-octet
  narrow/wide boundary; list and map sizes across the same boundary; `doff` 0–256, `channel` 0–65,536,
  both frame types, and extended/payload combinations; empty, single and multiple bodies; and 16,000
  seeded random values over the corpus grammar. **Identical verdicts from both artefacts on every one**:
  no input where the reference takes a step the specification does not permit, no input where both write
  and the octets differ, no input where both refuse and the classes differ.
* **The one asymmetry the search found is a reader's, and it is the specification's.** Its corpus reader
  accepts a `timestamp` outside `[-2^63, 2^63-1]`, where the reference's reader refuses the value as a
  corpus defect; the specification's own writer then refuses those octets `limit`. That is a reader
  defect on the specification's side (a value its reader produces and its writer will not write) and it
  cannot be used for this direction's negation: an input the reference's carrier refuses gives the
  reference no step, and `Conforms` constrains only the implementation's steps.
* **What would make the negation live again, and what a witness would have to be.** Either writer
  weakened at a member of any family above — the classes coming apart again at the declared-row family,
  or a shape divergence returning to the constructor family — makes the corresponding agreement theorem
  go red, and a *new* family outside the sweep would need its own witness. The shape of such a witness is
  fixed by `carriers_matched` and `writers_matched`: the frame must survive both carriers with related
  bodies, and the divergence must survive `frameOfJson`'s performative test, so it is a described
  performative carrying a value the two writers part on. Until one is exhibited, the honest statement of
  this consequent is **undecided** — false before patch 3, aligned since, and unrefuted now — and the
  search's extent above is the whole of the evidence rather than a claim, which is why it is a number
  with its families named. -/

end SpecAMQP.Proofs
