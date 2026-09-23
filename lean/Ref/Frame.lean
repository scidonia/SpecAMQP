import Generated.Oasis.Types
import Ref.Value

/-!
# The reference implementation of the frame layer

Written from Part 1's framing section — its layout, and its SIZE, DOFF, TYPE and
CHANNEL sentences, with the body "defined as a performative followed by an opaque
payload" whose performative is "encoded as a described type" — and independently of
`Spec.Frame`: the two share no definition, so their agreement over the frame corpus is
evidence about the layout rather than a tautology.

The constants below are transcribed here for the same reason they are transcribed
there: the artifacts declare no frame type, no protocol-header type and no frame
element, so `lean/Generated/` has no table this layer could read.

Refusals name their reason class as the leading token of the detail, in the vocabulary
the value layer established, because the differential contract compares classes between
the artefacts. A failure raised by the value layer is rendered by variant rather than by
parsing its prose.

The class is a **field** of a refusal, not a token a reader recovers by splitting the
message: the class is the part of a refusal that is interface — the corpus compares classes
between the artefacts, and this reader decides whether a value-layer failure was a
truncation by class — and a class read back out of prose by `String.splitOn` is one no
proof can reason about. So `readFrame` and `writeFrame` answer with a `Refusal`, whose
`reasonClass` is the class and whose `message` is the class, a colon, and the prose; and
`decodeFrame` and `encodeFrame` are those two functions rendered as that message, byte for
byte what this module has always reported to a caller.

Two things this layer does not do, both because they are not the frame layer's: it does
not check which performative may appear in which state or on which channel (that
dispatch is a picture, and belongs to the state machine), and it does not enforce a
negotiated maximum frame size, which needs a negotiation to have happened.
-/

namespace SpecAMQP.Ref.Frame

open SpecAMQP.Generated.Oasis (TypeDecl types)

/-! ## The layout, as Part 1 states it -/

/-- "The frame header is a fixed size (8 byte) structure that precedes each frame." -/
def headerOctets : Nat := 8

/-- "The value of the data offset is an unsigned, 8-bit integer specifying a count of
4-byte words." -/
def wordOctets : Nat := 4

/-- A DOFF "less than 2" would put the body inside the mandatory eight-octet header. -/
def minDoff : Nat := 2

/-- Bytes 6 and 7 of an AMQP frame contain the channel number. -/
def channelOctets : Nat := 2

/-- DOFF is byte 4 of the header: "an unsigned, 8-bit integer specifying a count of
4-byte words", so one octet of words is all the field has. -/
def doffOctets : Nat := 1

/-- The largest DOFF the one-octet field carries. -/
def maxDoff : Nat := 2 ^ (8 * doffOctets) - 1

/-- The largest channel number the two CHANNEL octets carry. -/
def maxChannel : Nat := 65535

/-- The largest count the four-octet SIZE field carries. -/
def maxSize : Nat := 4294967295

/-- "A type code of 0x00 indicates that the frame is an AMQP frame." -/
def amqpType : Nat := 0

/-- "A type code of 0x01 indicates that the frame is a SASL frame." -/
def saslType : Nat := 1

/-- The frame types this specification assigns; any other type code is unsupported
rather than unassigned, because the artifact assigns frame types and does not assign
this one. -/
inductive Kind where
  | amqp
  | sasl
deriving Repr, BEq, DecidableEq

namespace Kind

def code : Kind → Nat
  | .amqp => amqpType
  | .sasl => saslType

def ofCode (code : Nat) : Option Kind :=
  if code = amqpType then some .amqp
  else if code = saslType then some .sasl
  else none

def name : Kind → String
  | .amqp => "AMQP"
  | .sasl => "SASL"

/-- The role a frame type's performatives carry, in the artifact's `provides`
vocabulary: `frame` for an AMQP frame, `sasl-frame` for a SASL one. The layout requires
the performative to be "one of those defined", and the frame type is what says which
set that is. -/
def role : Kind → String
  | .amqp => "frame"
  | .sasl => "sasl-frame"

end Kind

/-- The declared type a descriptor names, searched for in the generated table.

A descriptor is a `ulong` carrying the artifact's `domain:code`, or the type's symbolic
name; both forms are looked up rather than listed, so this cannot disagree with the
surface the rest of the repository reads. -/
def typeOfDescriptor (descriptor : Value) : Option TypeDecl :=
  match descriptor with
  | .ulong code =>
    types.find? (fun entry =>
      match entry.descriptor with
      | some decl => decl.domain * 2 ^ 32 + decl.code == code.toNat
      | none => false)
  | .symbol name =>
    types.find? (fun entry =>
      match entry.descriptor with
      | some decl => decl.name == name
      | none => false)
  | _ => none

/-- Whether a body's descriptor names a performative the frame type carries. -/
def isPerformativeFor (kind : Kind) (descriptor : Value) : Bool :=
  match typeOfDescriptor descriptor with
  | some decl => decl.provides.contains kind.role
  | none => false

/-- One frame. SIZE is not a field: it counts the octets of the frame that carries it,
so the reader reports it as what it consumed and the writer derives it from what it
writes. -/
structure Frame where
  /-- The body's start in four-octet words, so `doff * 4 - 8` octets of extended
  header precede it. -/
  doff : Nat
  kind : Kind
  /-- The CHANNEL octets as read. A SASL frame carries no meaning in them. -/
  channel : Nat
  /-- The extended header, whose treatment depends on the frame type; every type read
  here ignores it. -/
  extended : Octets
  /-- The body: a performative as a described type, or `none` for the empty frame the
  idle-timeout clauses require a receiver to handle. The two are told apart here rather
  than by a distinguished value, because a bodyless frame is not a frame with an unusual
  body: `.null` would be a body the layout refuses, and a unit `Value` would be an
  inhabitant of the value language that no octet can produce. -/
  body : Option Value
  /-- The opaque octets the performative's semantics give meaning to. -/
  payload : Octets
deriving Repr

/-! ## Octets and refusals -/

/-- A big-endian unsigned field of a buffer already known to hold it. -/
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

/-- A refusal: the reason class, then what happened. -/
def refusal (reasonClass prose : String) : Refusal :=
  ⟨reasonClass, s!"{reasonClass}: {prose}"⟩

/-- A value-layer failure as this layer reports it: the class the value layer's own variant
names — carried as a field, so this layer never recovers it by splitting the message — and the
message this layer spells for it. -/
def valueFailure (error : DecodeError) : Refusal :=
  match error with
  | .truncated context => refusal "truncated" context
  | .unassigned octet =>
    refusal "unassigned" s!"octet {octet.toNat} is not an encoding the constructor \
      grammar assigns"
  | .unsupported octet =>
    refusal "unsupported" s!"octet {octet.toNat} is a legal constructor this \
      implementation does not read"
  | .sizeMismatch context declared observed =>
    refusal "sizeMismatch" s!"a {context} declares {declared} octet(s) after its size \
      field and measures {observed}"
  | .malformed reason => refusal "malformed" reason
  | .limit context => refusal "limit" context

/-- The reason class a rendered refusal leads with. -/
def classOf (message : String) : String := (message.splitOn ":").head?.getD ""

/-! ## Reading and writing -/

/-- Read the frame at the front of a buffer, reporting the octets it consumed as the
SIZE it declares.

The header is read first, then the declared arithmetic is checked for self-consistency,
then the buffer is checked to hold the frame it declares, and only then is the body
read — from the body's start to the *end of the buffer*, so that a performative which
runs past its own frame's SIZE becomes a size contradiction rather than a buffer
truncation. The two are different defects and the corpus distinguishes them.

This is the layer's reader, and its refusal carries the reason class as a field; the
message a caller sees is `decodeFrame` below, which renders that class. -/
def readFrame (bytes : Octets) : Except Refusal (Frame × Nat) :=
  if bytes.size < headerOctets then
    .error (refusal "truncated" s!"a frame header is {headerOctets} octets and only \
      {bytes.size} are present")
  else
    let size := beAt bytes 0 4
    let doff := beAt bytes 4 1
    let typeCode := beAt bytes 5 1
    let channel := beAt bytes 6 channelOctets
    if size < headerOctets then
      .error (refusal "sizeMismatch" s!"SIZE {size} is smaller than the \
        {headerOctets}-octet frame header")
    else if doff < minDoff then
      .error (refusal "sizeMismatch" s!"DOFF {doff} is below the minimum {minDoff}, \
        which would put the body inside the header")
    else if doff * wordOctets > size then
      .error (refusal "sizeMismatch" s!"DOFF {doff} starts the body at octet \
        {doff * wordOctets}, past the {size} octets SIZE declares")
    else if size > bytes.size then
      .error (refusal "truncated" s!"SIZE declares {size} octets and only {bytes.size} \
        are present")
    else
      match Kind.ofCode typeCode with
      | none =>
        .error (refusal "unsupported" s!"frame type {typeCode} is not a frame type this \
          specification assigns")
      | some kind =>
        let start := doff * wordOctets
        if size = headerOctets ∧ doff = minDoff then
          -- the empty frame: the frame's own window is SIZE's whole extent with DOFF at its
          -- minimum, so this is a frame header and nothing else. Deciding it here rather
          -- than after a body read is what keeps the coalesced case right: the region below
          -- runs to the end of the buffer, so an empty frame ahead of another would
          -- otherwise be read as that frame's octets.
          .ok (⟨doff, kind, channel, bytes.extract headerOctets start, none, #[]⟩, size)
        else
        match decode (bytes.extract start bytes.size) with
        | .error e =>
          let rendered := valueFailure e
          if rendered.reasonClass = "truncated" then
            .error (refusal "sizeMismatch" s!"the performative at octet {start} does not \
              fit in the {size} octets SIZE declares")
          else .error rendered
        | .ok (body, used) =>
          if start + used > size then
            .error (refusal "sizeMismatch" s!"the performative at octet {start} runs to \
              octet {start + used}, past the {size} octets SIZE declares")
          else
            match body with
            | .described descriptor _ =>
              match typeOfDescriptor descriptor with
              | none =>
                .error (refusal "unsupported" "the frame body's descriptor names no type \
                  the declared surface defines, so it is not a performative")
              | some decl =>
                if decl.provides.contains kind.role then
                  .ok (⟨doff, kind, channel, bytes.extract headerOctets start, some body,
                    bytes.extract (start + used) size⟩, size)
                else
                  .error (refusal "unsupported" s!"the frame body's performative is \
                    {decl.name}, whose declared roles are {decl.provides}, which does not \
                    include the {kind.role} role a {kind.name} frame carries")
            | _ =>
              .error (refusal "malformed" "the frame body does not start with a \
                described type, so it is not a performative")

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

/-- Write a frame, deriving the SIZE it declares from the octets it writes.

DOFF is carried rather than derived, and an inconsistent one is refused: a DOFF that
does not describe the extended header actually present would declare a body start the
octets do not have. A DOFF the one-octet field cannot hold is refused as well — writing
it would keep the low octet and drop the rest, which is a different frame than the one
asked for, and one this module's own reader would refuse.

This is the layer's writer, and its refusal carries the reason class as a field; the
message a caller sees is `encodeFrame` below, which renders that class. -/
def writeFrame (frame : Frame) : Except Refusal Octets :=
  if frame.doff < minDoff then
    .error (refusal "sizeMismatch" s!"DOFF {frame.doff} is below the minimum {minDoff}")
  else if frame.channel > maxChannel then
    .error (refusal "malformed" s!"channel {frame.channel} does not fit the \
      {channelOctets} CHANNEL octets")
  else if frame.doff > maxDoff then
    .error (refusal "limit" s!"DOFF {frame.doff} does not fit the {doffOctets} octet the \
      layout gives the field: the largest DOFF is {maxDoff}")
  else if frame.extended.size != frame.doff * wordOctets - headerOctets then
    .error (refusal "sizeMismatch" s!"DOFF {frame.doff} implies \
      {frame.doff * wordOctets - headerOctets} extended octets and the frame carries \
      {frame.extended.size}")
  else
    match frame.body with
    | none =>
      -- Sending an empty frame is a MAY, so refusing to write one is conforming: the
      -- receiver's obligation lives in the decoder above.
      .error (refusal "unsupported" "the frame carries no body: an empty frame is how a \
        peer with nothing to send defeats an idle timeout, and this writer does not send \
        one")
    | some (body@(.described descriptor _)) =>
      if !isPerformativeFor frame.kind descriptor then
        match typeOfDescriptor descriptor with
        | none =>
          .error (refusal "unsupported" "the frame body's descriptor names no type the \
            declared surface defines, so it is not a performative")
        | some decl =>
          .error (refusal "unsupported" s!"the frame body's performative is {decl.name}, \
            whose declared roles are {decl.provides}, which does not include the \
            {frame.kind.role} role a {frame.kind.name} frame carries")
      else
        match encode body with
        | .error e => .error ⟨classOf e, e⟩
        | .ok body =>
          let size := headerOctets + frame.extended.size + body.size + frame.payload.size
          if size ≤ maxSize then
            .ok (u32be size ++ #[UInt8.ofNat frame.doff] ++
              #[UInt8.ofNat frame.kind.code] ++ u16be frame.channel ++ frame.extended ++
              body ++ frame.payload)
          else
            .error (refusal "sizeMismatch" s!"SIZE cannot carry {size} octets in \
              {4} octets")
    | some _ =>
      .error (refusal "malformed" "the frame body is not a described type, so it is not \
        a performative")

/-- The writer as a caller sees it: `writeFrame`'s refusal rendered as its message. -/
def encodeFrame (frame : Frame) : Except String Octets :=
  (writeFrame frame).mapError Refusal.message

/-- The two forms of the writer accept exactly the same frames, for the same reason. -/
theorem encodeFrame_eq_ok_iff (frame : Frame) (bytes : Octets) :
    encodeFrame frame = .ok bytes ↔ writeFrame frame = .ok bytes := by
  cases h : writeFrame frame <;> simp [encodeFrame, h, Except.mapError]

end SpecAMQP.Ref.Frame
