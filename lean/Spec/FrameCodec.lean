import Harness.Runner
import Spec.Frame

/-!
# The specification's frame layer as a corpus codec

`Spec.Frame` reads and writes frames; this file is the translation between its `Frame`
and the frame vocabulary of `tests/contracts/frame-vector.schema.json`, which is the
vocabulary the shared runner compares in — never between the two artefacts' frame
types, which would need a third thing to trust.

Nothing here decides anything about frames. A field the vocabulary omits is read as the
layout's smallest case (`extended` empty, `payload` empty), a field it carries is passed
through, and `size` is the octet count the frame consumed rather than a field of the
frame: the layout fixes SIZE as the count of the octets that carry it.
-/

namespace SpecAMQP.Spec.FrameCodec

open Lean
open SpecAMQP.Harness (FrameCodec toHex ofHex)
open SpecAMQP.Spec.Codec (Value toJson valueOfJson)
open SpecAMQP.Spec.Frame (Frame FrameType decodeFrame encodeFrame)

/-- A frame in the corpus vocabulary: the layout's fields, the body as the one
described value the layout requires, and the payload as opaque octets. -/
def frameToJson (frame : Frame) (consumed : Nat) : Json :=
  Json.mkObj [("size", consumed),
              ("doff", frame.doff),
              ("type", toHex #[UInt8.ofNat frame.frameType.code]),
              ("channel", frame.channel),
              ("extended", toHex frame.extended),
              ("body", Json.arr #[toJson frame.body]),
              ("payload", toHex frame.payload)]

/-- A corpus frame read as a frame. `extended` and `payload` are optional in the
vocabulary and absent means empty; `body` is the one performative the layout allows, so
a body of any other length is a corpus defect rather than a frame to guess at. -/
def frameOfJson (json : Json) : Except String Frame := do
  let text (key : String) : String := (json.getObjValAs? String key).toOption.getD ""
  let doff ← json.getObjValAs? Nat "doff"
  let channel ← json.getObjValAs? Nat "channel"
  let frameType ←
    match (← ofHex (text "type")).toList with
    | [code] =>
      match FrameType.ofCode code.toNat with
      | some frameType => .ok frameType
      | none =>
        .error s!"frame type 0x{toHex #[code]} is not a frame type this specification \
          assigns"
    | _ => .error "a frame's TYPE field is one octet"
  let extended ← ofHex (text "extended")
  let payload ← ofHex (text "payload")
  match (← json.getObjValAs? (Array Json) "body").toList with
  | [valueJson] =>
    .ok ⟨doff, frameType, channel, extended, (← valueOfJson 64 valueJson), payload⟩
  | _ => .error "a frame's body is one performative"

/-- The specification's frame layer behind the corpus interface. -/
def specFrameCodec : FrameCodec where
  name := "specification"
  decode := fun bytes =>
    match decodeFrame bytes with
    | .ok (frame, consumed) => .ok (frameToJson frame consumed, consumed)
    | .error e => .error e
  encode := fun json => do
    let frame ← frameOfJson json
    encodeFrame frame

end SpecAMQP.Spec.FrameCodec
