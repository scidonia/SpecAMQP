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

Refusals carry the reason-class vocabulary the value layer established, as the leading
token of the message: `truncated` when the buffer is too short (a header that is not
eight octets, or a frame that declares more octets than the buffer holds),
`sizeMismatch` when the declared arithmetic contradicts the octets (`SIZE` below the
header, `DOFF` below two, `DOFF*4` past `SIZE`, or a performative that does not fit in
the body the frame declares), `unsupported` for a frame type the artifact does not
assign, and `malformed` for a body that is not a described type.
-/

namespace SpecAMQP.Spec.Frame

open SpecAMQP.Harness (Octets toHex)
open SpecAMQP.Generated.Oasis (TypeDecl types)
open SpecAMQP.Spec.Codec (Value decodeValue encodeValue beOctets refusal typeName)

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
  /-- The performative. -/
  body : Value
  /-- The opaque octets after the performative. -/
  payload : Octets
deriving Repr

/-- The octet the body begins at, `4 * DOFF`. -/
def bodyStart (doff : Nat) : Nat := doff * doffWord

/-- A big-endian unsigned field at an offset, for buffers already checked long enough to
hold it. -/
def beAt (bytes : Octets) (start width : Nat) : Nat :=
  (bytes.extract start (start + width)).foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- The reason class a message leads with, so that a refusal raised by the value layer
can be recognised without parsing its prose. -/
def reasonClassOf (message : String) : String :=
  (message.splitOn ":").head?.getD ""

/-- Decode one frame from the front of a buffer, reporting the octets it consumed as the
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
`truncated` a shorter buffer produces, and the two are different defects. -/
def decodeFrame (bytes : Octets) : Except String (Frame × Nat) := do
  if bytes.size < headerOctets then
    .error (refusal "truncated" s!"a frame header is {headerOctets} octets and the \
      buffer holds {bytes.size}")
  else
    let size := beAt bytes 0 sizeOctets
    let doff := beAt bytes 4 1
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
        let region := bytes.extract start bytes.size
        match decodeValue region with
        | .error e =>
          if reasonClassOf e == "truncated" then
            .error (refusal "sizeMismatch" s!"the performative at octet {start} does \
              not complete within the {size} octets SIZE declares: {e}")
          else .error e
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
                  .ok (⟨doff, frameType, channel, extended, body,
                    bytes.extract (start + consumed) size⟩, size)
                else
                  .error (refusal "unsupported" s!"the frame body's performative is \
                    {decl.name}, whose declared roles are {decl.provides}, which does not \
                    include the {frameType.role} role a {frameType.name} frame carries")
            | other =>
              .error (refusal "malformed" s!"the frame body starts with \
                {typeName other}, and a frame's performative is encoded as a described \
                type")

/-- Encode one frame, computing the SIZE it declares from the octets it writes.

SIZE is not carried by the value being encoded, so it cannot disagree with the octets:
the writer adds up the header, the extended header, the performative and the payload,
and refuses when the total does not fit the four octets the layout gives it. DOFF is
carried, because the extended header's width is what decides it, and a DOFF whose words
do not describe the extended header actually present is refused rather than silently
recomputed. -/
def encodeFrame (frame : Frame) : Except String Octets := do
  if frame.doff < minDoff then
    .error (refusal "sizeMismatch" s!"DOFF {frame.doff} puts the body inside the \
      header: the smallest legal DOFF is {minDoff}")
  else if frame.channel > 2 ^ (8 * channelOctets) - 1 then
    .error (refusal "malformed" s!"channel {frame.channel} does not fit the \
      {channelOctets} CHANNEL octets")
  else if frame.extended.size != bodyStart frame.doff - headerOctets then
    .error (refusal "sizeMismatch" s!"DOFF {frame.doff} declares \
      {bodyStart frame.doff - headerOctets} extended octets and the frame carries \
      {frame.extended.size}")
  else
    match frame.body with
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
        let body ← encodeValue frame.body
        let size := headerOctets + frame.extended.size + body.size + frame.payload.size
        if size ≤ maxSize then
          return (beOctets sizeOctets size ++ beOctets 1 frame.doff ++
            beOctets 1 frame.frameType.code ++ beOctets channelOctets frame.channel
            ).toArray ++ frame.extended ++ body ++ frame.payload
        else
          .error (refusal "sizeMismatch" s!"SIZE cannot carry {size} octets in its \
            {sizeOctets} octets")
    | other =>
      .error (refusal "malformed" s!"the frame body is {typeName other}, and a frame's \
        performative is encoded as a described type")

end SpecAMQP.Spec.Frame
