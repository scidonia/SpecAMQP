import Generated.Oasis.Types
import Spec.Codec

/-!
# The frame layer (Part 1, `amqp:transport/section:framing`)

The frame header is the one part of this specification whose layout is *prose and
ASCII layout rather than a machine-readable declaration*: the pinned artifacts declare
no frame type, no protocol-header type and no frame element, so `lean/Generated/` has
no table to read here. The constants below are therefore hand-transcribed, and this is
the one place in this repository where a hand-written constant is the source of truth
rather than a copy of a generated table — so each one cites the sentence it came from.

The layout, as the artifact draws it:

```text
      +0      +1      +2      +3
      +-----------------------+ -.
    0 |          SIZE         |  |  Frame Header (8 bytes)
      +-----------------------+  |
    4 |    DOFF   |    TYPE   |  |
      +-----------------------+ -'
    8 |          ...          |     Extended Header (DOFF * 4 - 8 bytes)
      +-----------------------+ -.
 4*DOFF |         ...         |     Frame Body (SIZE - DOFF * 4 bytes)
      +-----------------------+ -'
            SIZE bytes
```

with:

* **SIZE**, bytes 0–3, "an unsigned 32-bit integer that MUST contain the total frame
  size of the frame header, extended header, and frame body", and the frame being
  malformed if the size is less than the header's eight octets;
* **DOFF**, byte 4, "an unsigned, 8-bit integer specifying a count of 4-byte words",
  giving the position of the body, where one "less than 2" puts the body inside the
  mandatory eight-octet header;
* **TYPE**, byte 5, where "a type code of 0x00 indicates that the frame is an AMQP
  frame" and "a type code of 0x01 indicates that the frame is a SASL frame";
* **CHANNEL**, bytes 6 and 7, the channel number — which is why "the subsequent bytes
  in the frame header MAY be interpreted differently depending on the type of the
  frame", and a SASL frame carries no meaning in them;
* the body, "defined as a performative followed by an opaque payload", the
  performative encoded "as a described type in the AMQP type system", the remaining
  octets forming "the payload for that frame".

Two things this module deliberately does not do, because neither is the frame layer's
business. It does not check which performative may appear on which channel or in which
state: that dispatch is a picture in the artifact, and it belongs to the state-machine
work. And it does not enforce a negotiated maximum frame size, which requires a
negotiation to have happened. What it does enforce is the layout's own arithmetic, and
what it carries is the extended header, whose treatment "depends on the frame type" —
an AMQP frame's diagram marks it ignored, which is what `decodeFrame` does with it.

Refusals carry the reason-class vocabulary the value layer established: `truncated` when
the buffer is too short (a header that is not eight octets, or a frame that declares more
octets than the buffer holds), `sizeMismatch` when the declared arithmetic contradicts the
octets (`SIZE` below the header, `DOFF` below two, `DOFF*4` past `SIZE`, or a performative
that does not fit in the body the frame declares), `unsupported` for a frame type the
artifact does not assign, `limit` for a `DOFF` the one-octet field cannot carry, and
`malformed` for a body that is not a described type.

The class is a **field** of a refusal, not a token a reader recovers by splitting the
message: the class is the part of a refusal that is interface — the corpus compares classes
between the artefacts, and the reader itself decides whether a value-layer failure was a
truncation by class — and a class read back out of prose by `String.splitOn` is one no
proof can reason about. So `readFrame` and `writeFrame` answer with a `Refusal`, whose
`reasonClass` is the class and whose `message` is the class, a colon, and the prose; and
`decodeFrame` and `encodeFrame` are those two functions rendered as that message, byte for
byte what this module has always reported to a caller.
-/

namespace SpecAMQP.Spec.Frame

open SpecAMQP.Harness (Octets toHex)
open SpecAMQP.Generated.Oasis (TypeDecl types)
open SpecAMQP.Spec.Codec (Value decodeValue encodeValue beOctets typeName)

/-! ## The hand-transcribed layout -/

/-- The frame header's width in octets: "The frame header is a fixed size (8 byte)
structure that precedes each frame."

Source: `amqp-core-transport-v1.0-os.xml#amqp:transport/section:framing`, the framing
layout doc. There is no generated table for this: the layout is prose and ASCII art. -/
def headerOctets : Nat := 8

/-- The width in octets of one four-octet word, the unit DOFF counts in: "The value of
the data offset is an unsigned, 8-bit integer specifying a count of 4-byte words." -/
def doffWord : Nat := 4

/-- The smallest legal DOFF: with an eight-octet header the body cannot begin before
the eighth octet, which is two four-octet words from the frame's start. -/
def minDoff : Nat := 2

/-- The width of the DOFF field in octets, the layout's byte 4: "an unsigned, 8-bit
integer specifying a count of 4-byte words", which is where `DOFF`'s range comes from —
the field counts words, and one octet of them is all the layout gives it. -/
def doffOctets : Nat := 1

/-- The width of the SIZE field in octets, the layout's bytes 0–3. -/
def sizeOctets : Nat := 4

/-- The width of the CHANNEL field in octets, the layout's bytes 6 and 7. -/
def channelOctets : Nat := 2

/-- The largest value the four-octet SIZE field can carry. -/
def maxSize : Nat := 2 ^ 32 - 1

/-- The frame type TYPE `0x00` names: "A type code of 0x00 indicates that the frame is
an AMQP frame." -/
def amqpTypeCode : Nat := 0x00

/-- The frame type TYPE `0x01` names: "A type code of 0x01 indicates that the frame is
a SASL frame." -/
def saslTypeCode : Nat := 0x01

/-- The frame types the artifact assigns. A third type code is not a value this
specification fails to recognise but a frame type it does not assign, which is why
`decodeFrame` refuses it as unsupported rather than unassigned. -/
inductive FrameType where
  | amqp
  | sasl
deriving Repr, BEq, DecidableEq

/-- The TYPE octet a frame type is written as. -/
def FrameType.code : FrameType → Nat
  | .amqp => amqpTypeCode
  | .sasl => saslTypeCode

/-- The frame type a TYPE octet names, or `none` for an octet the artifact does not
assign. -/
def FrameType.ofCode (code : Nat) : Option FrameType :=
  if code = amqpTypeCode then some .amqp
  else if code = saslTypeCode then some .sasl
  else none

def FrameType.name : FrameType → String
  | .amqp => "AMQP"
  | .sasl => "SASL"

/-- The frame role a frame type carries, in the artifact's own `provides` vocabulary:
the nine AMQP performatives provide `frame` and the five SASL ones provide
`sasl-frame`. The layout's own sentence is what makes this a rule rather than a
convention — "The performative MUST be one of those defined in «performatives»" — and
the frame type is what says which of the two sets the frame can carry. -/
def FrameType.role : FrameType → String
  | .amqp => "frame"
  | .sasl => "sasl-frame"

/-- The declared type a wire descriptor names, from the descriptor's own form.

A descriptor is a described value's descriptor: a `ulong` whose octets are the
artifact's `domain:code`, or the type's symbolic name. Both forms are searched for in
the declared surface rather than listed here, so a type the artifacts declare
resolvable without this file changing — and a descriptor that names no declared type
resolves to `none`, which is what makes "one of those defined" checkable.

Only `ulong` and `symbol` descriptors name types: any other shape is not a descriptor
this specification defines. -/
def typeOfDescriptor (descriptor : Value) : Option TypeDecl :=
  match descriptor with
  | .ulong code =>
    types.find? (fun entry =>
      match entry.descriptor with
      | some decl => decl.domain * 2 ^ 32 + decl.code == code
      | none => false)
  | .symbol name =>
    types.find? (fun entry =>
      match entry.descriptor with
      | some decl => decl.name == name
      | none => false)
  | _ => none

/-- Whether a body's descriptor names a performative the frame type can carry. -/
def carriesPerformative (frameType : FrameType) (descriptor : Value) : Bool :=
  match typeOfDescriptor descriptor with
  | some decl => decl.provides.contains frameType.role
  | none => false

/-- One frame, in the shapes the layout gives.

`size` is deliberately absent: SIZE is the octet count of the frame that carries it, so
`decodeFrame` reports it as the count it consumed and `encodeFrame` computes it from
the octets it produces. A frame that carried its own size could disagree with its
octets, and there is no reading of the layout in which the declaration wins.

The extended header is carried as octets rather than interpreted: its "treatment
depends on the frame type", and every type this specification reads ignores it. The
`body` is the frame's performative, which the layout requires to be a described value;
`payload` is the opaque remainder, which "the semantics of the given performative"
gives meaning to and the frame layer therefore does not read. -/
structure Frame where
  /-- The body's position in four-octet words from the frame's start, so the extended
  header occupies `doff * 4 - 8` octets. -/
  doff : Nat
  frameType : FrameType
  /-- The two CHANNEL octets as read. A SASL frame carries no meaning in them, and the
  frame layer keeps them rather than zeroing a field it has no rule for. -/
  channel : Nat
  /-- The extended header octets, `doff * 4 - 8` of them. -/
  extended : Octets
  /-- The body: a performative as a described value, or `none` for the empty frame the
  idle-timeout clauses make a receiver handle ("a frame consisting solely of a frame
  header, with no frame body", and "apart from this use, empty frames have no meaning").
  `Option` rather than a distinguished `Value` because a frame with no body is not a frame
  whose body is unusual: `.null` would be indistinguishable from a malformed body the
  layout refuses, and a unit constructor in `Value` would put a non-AMQP inhabitant into
  the value language the codec and the corpus vocabulary both range over. -/
  body : Option Value
  /-- The opaque octets after the performative. -/
  payload : Octets
deriving Repr

/-- The octet the body begins at, `4 * DOFF`. -/
def bodyStart (doff : Nat) : Nat := doff * doffWord

/-- A big-endian unsigned field at an offset, for buffers already checked long enough to
hold it. -/
def beAt (bytes : Octets) (start width : Nat) : Nat :=
  (bytes.extract start (start + width)).foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- A refusal: the reason class this layer names, and the message a caller sees.

The class is a field rather than a token a reader recovers from the message, because the
class is the part of a refusal that is interface — the corpus compares classes between the
artefacts, and this reader decides whether a value-layer failure was a truncation by class
— and a class read back out of prose by `String.splitOn` is one the kernel cannot reason
about. The message travels with it so that every caller and every vector still sees byte
for byte what this module reported before the class became a field. -/
structure Refusal where
  /-- The reason class this refusal names. -/
  reasonClass : String
  /-- The message a caller sees: the class, a colon, and the prose. -/
  message : String
deriving Repr, DecidableEq

/-- A refusal whose class this layer named itself. The message is spelled exactly as a
message has always been spelled here: the class, a colon, a space, and the prose. -/
def refusal (reasonClass prose : String) : Refusal :=
  ⟨reasonClass, SpecAMQP.Spec.Codec.refusalMessage reasonClass prose⟩

/-! ## The layout's arithmetic, in one place, and the frame's extent

`readFrame` below reports the octets it consumed — but only where it *accepted* a frame. A caller that has
to advance a stream is in the other position: it reads whatever sizes the transport returns and must know
when it holds a whole frame and when it must wait, which is a question about the frame's *extent* and not
about the reader's answer, and one the reader cannot answer at all before the frame is complete. What that
caller needs is the layout's own arithmetic, so it is stated here once — the two fields the declaration is
made of, whether the declaration is self-consistent, and the extent the frame therefore occupies.

`readFrame` stays the authority on what a buffer *means*: its checks, their order and the refusal each
raises are its own, because a caller has to be told which defect it read. What holds the two together is
not convention but a theorem: `declarationConsistent_eq_true_iff` identifies the predicate with the
reader's three consistency checks, and `Proofs.CoreLaws` proves the reader's answer and the frame's extent
agree wherever the reader accepts.
-/

/-- The frame's declared size: the `SIZE` field, "an unsigned 32-bit integer that MUST contain the total
frame size of the frame header, extended header, and frame body", read big-endian where the layout puts
it. The reader reads its fields through this definition and `declaredDoff`, so the offsets and widths
exist once. -/
def declaredSize (bytes : Octets) : Nat := beAt bytes 0 sizeOctets

/-- The frame's declared body offset: the `DOFF` field, "an unsigned, 8-bit integer specifying a count of
4-byte words", so the body begins at four times its value. -/
def declaredDoff (bytes : Octets) : Nat := beAt bytes 4 doffOctets

/-- Whether the frame's declaration is self-consistent: a `SIZE` that can carry the eight-octet header, a
`DOFF` that puts the body after it, and a body that starts inside the frame.

Those three are exactly the reader's consistency checks — `SIZE` below the header, `DOFF` below its
minimum, a body start past `SIZE` — and `declarationConsistent_eq_true_iff` proves the identification
rather than asserting it, so a caller that decides when to wait and the reader that decides what a buffer
means cannot drift apart without a failing theorem. -/
def declarationConsistent (bytes : Octets) : Bool :=
  !(declaredSize bytes < headerOctets) && !(declaredDoff bytes < minDoff) &&
    !(bodyStart (declaredDoff bytes) > declaredSize bytes)

/-- **How many octets the next frame occupies.**

Where the declaration is self-consistent a frame occupies exactly the `SIZE` it declares, which is the
arithmetic the layout itself states; where it is not, the declaration contradicts itself and the octets
that carried the contradiction — the header — are all that can be attributed to the frame. Octets of a
*following* frame are never attributed to this one.

The buffer's length deliberately does not enter. This is the frame's extent, not the reader's progress: a
stream caller compares the buffer it holds against this number to decide whether the whole frame is in
hand, and that comparison — the waiting rule — is the caller's own
(`Impl.Stream.nextUnitLength` is where it lives, together with the connection layer's question of whether
a header or a frame is due). -/
def frameExtent (bytes : Octets) : Nat :=
  if declarationConsistent bytes then declaredSize bytes else headerOctets

/-- **The three checks, as one predicate.** A caller that wants the reader's consistency checks can ask
for them here rather than spelling them again: the predicate is true exactly where none of the three
holds. -/
theorem declarationConsistent_eq_true_iff (bytes : Octets) :
    declarationConsistent bytes = true ↔
      ¬ declaredSize bytes < headerOctets ∧ ¬ declaredDoff bytes < minDoff ∧
        ¬ bodyStart (declaredDoff bytes) > declaredSize bytes := by
  unfold declarationConsistent
  simp [and_assoc]

/-- **A frame's extent is never shorter than a frame header.** This is the law a stream loop's
termination rests on: advancing by the extent always consumes octets, so a caller that loops on extents
makes progress. -/
theorem headerOctets_le_frameExtent (bytes : Octets) : headerOctets ≤ frameExtent bytes := by
  unfold frameExtent
  by_cases h : declarationConsistent bytes
  · rw [if_pos h]
    exact Nat.le_of_not_lt ((declarationConsistent_eq_true_iff bytes).mp h).1
  · rw [if_neg h]
    exact Nat.le_refl _

/-- Where the declaration is self-consistent, the extent is the declared `SIZE` — the layout's own
reading, and the count the reader reports when it accepts. -/
theorem frameExtent_eq_declaredSize {bytes : Octets} (h : declarationConsistent bytes = true) :
    frameExtent bytes = declaredSize bytes := by
  unfold frameExtent
  rw [if_pos h]

/-- Where it is not, the extent is the header: the octets that carried the contradiction. -/
theorem frameExtent_eq_headerOctets {bytes : Octets} (h : declarationConsistent bytes = false) :
    frameExtent bytes = headerOctets := by
  unfold frameExtent
  rw [if_neg (by rw [h]; simp)]

/-- Read one frame from the front of a buffer, reporting the octets it consumed as the
SIZE it declares, so a buffer may hold a following frame.

The order of the checks is the order the layout itself forces: the header must be
present before its fields can be read, the declared arithmetic must be self-consistent
before anything is sliced by it, the buffer must hold the frame the header declares,
and only then is the body read — as a described value, followed by the payload the
remaining octets of the frame hold.

The body is read from the body's start to the *end of the buffer* rather than to the
end of the frame, and the octets it consumed are then compared with what the frame
declares. That is what makes a performative which runs past its own frame's SIZE a
`sizeMismatch` — the declaration contradicts the octets present — instead of the
`truncated` a shorter buffer produces, and the two are different defects.

This is the layer's reader, and its refusal carries the reason class as a field; the
message a caller sees is `decodeFrame` below, which renders that class. -/
def readFrame (bytes : Octets) : Except Refusal (Frame × Nat) := do
  if bytes.size < headerOctets then
    .error (refusal "truncated" s!"a frame header is {headerOctets} octets and the \
      buffer holds {bytes.size}")
  else
    let size := declaredSize bytes
    let doff := declaredDoff bytes
    let typeCode := beAt bytes 5 1
    let channel := beAt bytes 6 channelOctets
    if size < headerOctets then
      .error (refusal "sizeMismatch" s!"SIZE {size} is below the {headerOctets}-octet \
        frame header")
    else if doff < minDoff then
      .error (refusal "sizeMismatch" s!"DOFF {doff} puts the body inside the header: \
        the smallest legal DOFF is {minDoff}")
    else if bodyStart doff > size then
      .error (refusal "sizeMismatch" s!"DOFF {doff} puts the body at octet \
        {bodyStart doff} of a {size}-octet frame")
    else if bytes.size < size then
      .error (refusal "truncated" s!"SIZE declares {size} octets and the buffer holds \
        {bytes.size}")
    else
      match FrameType.ofCode typeCode with
      | none =>
        .error (refusal "unsupported" s!"frame type \
          0x{toHex #[UInt8.ofNat typeCode]} is not a frame type this specification \
          assigns")
      | some frameType => do
        let start := bodyStart doff
        let extended := bytes.extract headerOctets start
        if size = headerOctets ∧ doff = minDoff then
          -- the empty frame: a frame header and nothing else. The test is the frame's own
          -- window — SIZE equal to the header's octets with DOFF at its minimum — and never
          -- a body read: the body region below runs to the end of the *buffer*, so an empty
          -- frame ahead of another would otherwise be read against the next frame's octets.
          .ok (⟨doff, frameType, channel, extended, none, #[]⟩, size)
        else
          let region := bytes.extract start bytes.size
          match decodeValue region with
          | .error failure =>
            -- the class is a field of the value layer's refusal: the frame layer reads it, and never
            -- recovers it by splitting the rendered message
            if failure.reasonClass == "truncated" then
              .error (refusal "sizeMismatch" s!"the performative at octet {start} does \
                not complete within the {size} octets SIZE declares: {failure.message}")
            else .error ⟨failure.reasonClass, failure.message⟩
          | .ok (body, consumed) =>
            if start + consumed > size then
              .error (refusal "sizeMismatch" s!"the performative at octet {start} ends \
                at octet {start + consumed} of a {size}-octet frame")
            else
              match body with
              | .described descriptor _ =>
                match typeOfDescriptor descriptor with
                | none =>
                  .error (refusal "unsupported" s!"the frame body's descriptor names no \
                    type the declared surface defines, so it is not a performative")
                | some decl =>
                  if decl.provides.contains frameType.role then
                    .ok (⟨doff, frameType, channel, extended, some body,
                      bytes.extract (start + consumed) size⟩, size)
                  else
                    .error (refusal "unsupported" s!"the frame body's performative is \
                      {decl.name}, whose declared roles are {decl.provides}, which does not \
                      include the {frameType.role} role a {frameType.name} frame carries")
              | other =>
                .error (refusal "malformed" s!"the frame body starts with \
                  {typeName other}, and a frame's performative is encoded as a described \
                  type")

/-- **Acceptance implies a self-consistent declaration.** A reader that reads a frame has passed all
three consistency checks, which is exactly the predicate above — so the frame branch of a stream caller,
which asks the predicate, is asking a question the reader agrees with on the branch where the reader
succeeds.

The converse is deliberately *not* claimed, and the difference is the reader's business rather than the
window's: a self-consistent declaration can still be refused for what the frame carries (a type the
artifact does not assign, a body that is not a described value, a performative that runs past its own
`SIZE`), and none of that changes how far the frame extends. -/
theorem readFrame_ok_declarationConsistent {bytes : Octets} {frame : Frame} {consumed : Nat}
    (h : readFrame bytes = .ok (frame, consumed)) : declarationConsistent bytes = true := by
  unfold readFrame at h
  simp only [] at h
  all_goals (repeat' split at h)
  all_goals first
    | (rw [declarationConsistent_eq_true_iff]; exact ⟨by assumption, by assumption, by assumption⟩)
    | (exact absurd h (by intro he; cases he))

/-- The reader as a caller sees it: `readFrame`'s refusal rendered as its message. The
class it names is the field `readFrame` carries, so a reader of this form and a proof about
`readFrame` cannot disagree about a class. -/
def decodeFrame (bytes : Octets) : Except String (Frame × Nat) :=
  (readFrame bytes).mapError Refusal.message

/-- The two forms of the reader accept exactly the same frames: rendering a refusal to its
message turns no answer into a different one, so a claim about `decodeFrame`'s accepted
frame is a claim about `readFrame`'s, and a proof may work in whichever form it needs. -/
theorem decodeFrame_eq_ok_iff (bytes : Octets) (frame : Frame) (consumed : Nat) :
    decodeFrame bytes = .ok (frame, consumed) ↔ readFrame bytes = .ok (frame, consumed) := by
  cases h : readFrame bytes <;> simp [decodeFrame, h, Except.mapError]

/-- Write one frame, computing the SIZE it declares from the octets it writes.

SIZE is not carried by the value being encoded, so it cannot disagree with the octets:
the writer adds up the header, the extended header, the performative and the payload,
and refuses when the total does not fit the four octets the layout gives it. DOFF is
carried, because the extended header's width is what decides it, and a DOFF whose words
do not describe the extended header actually present is refused rather than silently
recomputed.

A DOFF the one-octet field cannot hold is refused too, and refused before the extended
header's width is checked: writing it with `beOctets 1` would keep its low octet and drop
the rest, which is a different frame than the one asked for — and one this module's own
reader would then refuse, since the byte it read would put the body somewhere else. The
writer's domain is meant to sit inside what the reader accepts.

This is the layer's writer, and its refusal carries the reason class as a field; the
message a caller sees is `encodeFrame` below, which renders that class. -/
def writeFrame (frame : Frame) : Except Refusal Octets := do
  if frame.doff < minDoff then
    .error (refusal "sizeMismatch" s!"DOFF {frame.doff} puts the body inside the \
      header: the smallest legal DOFF is {minDoff}")
  else if frame.channel > 2 ^ (8 * channelOctets) - 1 then
    .error (refusal "malformed" s!"channel {frame.channel} does not fit the \
      {channelOctets} CHANNEL octets")
  else if frame.doff > 2 ^ (8 * doffOctets) - 1 then
    .error (refusal "limit" s!"DOFF {frame.doff} does not fit the {doffOctets} octet the \
      layout gives the field: the largest DOFF is {2 ^ (8 * doffOctets) - 1}")
  else if frame.extended.size != bodyStart frame.doff - headerOctets then
    .error (refusal "sizeMismatch" s!"DOFF {frame.doff} declares \
      {bodyStart frame.doff - headerOctets} extended octets and the frame carries \
      {frame.extended.size}")
  else
    match frame.body with
    | none =>
      -- Sending an empty frame is a MAY, so refusing to write one is conforming; the
      -- receiver's obligation is in the decoder above, not here.
      .error (refusal "unsupported" "the frame carries no body: an empty frame is how a \
        peer with nothing to send defeats an idle timeout, and this writer does not send \
        one")
    | some body =>
      match body with
      | .described descriptor _ =>
        if !carriesPerformative frame.frameType descriptor then
          match typeOfDescriptor descriptor with
          | none =>
            .error (refusal "unsupported" "the frame body's descriptor names no type the \
              declared surface defines, so it is not a performative")
          | some decl =>
            .error (refusal "unsupported" s!"the frame body's performative is {decl.name}, \
              whose declared roles are {decl.provides}, which does not include the \
              {frame.frameType.role} role a {frame.frameType.name} frame carries")
        else do
          let octets ←
            match encodeValue body with
            | .ok octets => .ok octets
            | .error failure => .error ⟨failure.reasonClass, failure.message⟩
          let size := headerOctets + frame.extended.size + octets.size + frame.payload.size
          if size ≤ maxSize then
            return (beOctets sizeOctets size ++ beOctets 1 frame.doff ++
              beOctets 1 frame.frameType.code ++ beOctets channelOctets frame.channel
              ).toArray ++ frame.extended ++ octets ++ frame.payload
          else
            .error (refusal "sizeMismatch" s!"SIZE cannot carry {size} octets in its \
              {sizeOctets} octets")
      | other =>
        .error (refusal "malformed" s!"the frame body is {typeName other}, and a frame's \
          performative is encoded as a described type")

/-- The writer as a caller sees it: `writeFrame`'s refusal rendered as its message. -/
def encodeFrame (frame : Frame) : Except String Octets :=
  (writeFrame frame).mapError Refusal.message

/-- The two forms of the writer accept exactly the same frames, for the same reason. -/
theorem encodeFrame_eq_ok_iff (frame : Frame) (bytes : Octets) :
    encodeFrame frame = .ok bytes ↔ writeFrame frame = .ok bytes := by
  cases h : writeFrame frame <;> simp [encodeFrame, h, Except.mapError]

end SpecAMQP.Spec.Frame
