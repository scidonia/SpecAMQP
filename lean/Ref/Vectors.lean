import Harness.Runner
import Ref.Value

/-!
# The reference implementation, as a corpus codec

Everything this file does is translate between the reference implementation's own
value type and the corpus vocabulary. Running vectors, comparing expectations and
reporting verdicts belong to `Harness.Runner`, which is shared with the
specification: a shared harness is not a shared implementation, and keeping the
runner common is what makes a disagreement between the two artefacts a
disagreement about the wire format rather than about the harness.
-/

namespace SpecAMQP.Ref.Vectors

open Lean
open SpecAMQP.Harness

/-- An unsigned field of a given width, with the range checked rather than
truncated: a vector that asks for `uint 4294967296` is a corpus defect, not a
value to wrap. -/
def unsignedOf (json : Json) (bound : Nat) : Except String Nat := do
  let n ← json.getObjValAs? Nat "value"
  if n ≤ bound then return n else .error s!"value {n} does not fit in this width"

/-- A signed field of a given width, on the same terms. -/
def signedOf (json : Json) (width : Nat) : Except String Int := do
  let n ← json.getObjValAs? Int "value"
  let lo := -((2 : Int) ^ (width - 1))
  let hi := (2 : Int) ^ (width - 1) - 1
  if lo ≤ n && n ≤ hi then return n
  else .error s!"value {n} does not fit in a {width}-bit signed field"

/-- A fixed-width opaque payload, whose width the encoding fixes. Float, double,
the three decimals and uuid take their payload as hex rather than as a number:
the specification fixes the framing of those encodings, so a vector that names the
wrong number of octets is a corpus defect and fails here rather than being padded
or truncated. -/
def fixedHex (json : Json) (octets : Nat) : Except String Octets := do
  let bytes ← ofHex (← json.getObjValAs? String "hex")
  if bytes.size == octets then return bytes
  else .error s!"expected {octets} octets, got {bytes.size}"

/-- An integer field read from a named key and range-checked rather than truncated. -/
def boundedField (json : Json) (key : String) (lo hi : Int) : Except String Int := do
  let n ← json.getObjValAs? Int key
  if lo ≤ n && n ≤ hi then return n
  else .error s!"{key} {n} is outside {lo}..{hi}"

/-- The corpus's value vocabulary, read into this implementation's values.

`fuel` bounds the nesting depth so the reader stays total: a corpus line nested
deeper than a handful of levels is malformed for our purposes, and the alternative
— a partial function — would make the executable's behaviour undefined exactly
where a corpus defect lives. -/
def valueOfJson (fuel : Nat) (json : Json) : Except String Value :=
  match fuel with
  | 0 => .error "value nested too deeply"
  | fuel + 1 => do
    let kind ← json.getObjValAs? String "type"
    match kind with
    | "null" => .ok .null
    | "boolean" => .ok (.boolean (← json.getObjValAs? Bool "value"))
    | "ubyte" => return (.ubyte (← unsignedOf json 255).toUInt8)
    | "ushort" => return (.ushort (← unsignedOf json 65535).toUInt16)
    | "uint" => return (.uint (← unsignedOf json 4294967295).toUInt32)
    | "ulong" => return (.ulong (← unsignedOf json 18446744073709551615).toUInt64)
    | "byte" => let n ← signedOf json 8
                return (.byte (Int8.ofBitVec (BitVec.ofNat 8 (n % 256).toNat)))
    | "short" => let n ← signedOf json 16
                 return (.short (Int16.ofBitVec (BitVec.ofNat 16 (n % 65536).toNat)))
    | "int" => let n ← signedOf json 32
               return (.int (Int32.ofBitVec (BitVec.ofNat 32 (n % 4294967296).toNat)))
    | "long" => let n ← signedOf json 64
                return (.long (Int64.ofBitVec (BitVec.ofNat 64 (n % 18446744073709551616).toNat)))
    | "char" =>
      let n ← boundedField json "codepoint" 0 1114111
      return (.char n.toNat.toUInt32)
    | "timestamp" =>
      let n ← boundedField json "milliseconds" (-(2 ^ 63)) (2 ^ 63 - 1)
      return (.timestamp (Int64.ofBitVec (BitVec.ofNat 64 (n % 18446744073709551616).toNat)))
    | "float" => return (.float (← fixedHex json 4))
    | "double" => return (.double (← fixedHex json 8))
    | "decimal32" => return (.decimal32 (← fixedHex json 4))
    | "decimal64" => return (.decimal64 (← fixedHex json 8))
    | "decimal128" => return (.decimal128 (← fixedHex json 16))
    | "uuid" => return (.uuid (← fixedHex json 16))
    | "string" => .ok (.string (← json.getObjValAs? String "text"))
    | "symbol" => .ok (.symbol (← json.getObjValAs? String "text"))
    | "binary" => return (.binary (← ofHex (← json.getObjValAs? String "hex")).toList)
    | "list" =>
      let items ← json.getObjValAs? (Array Json) "items"
      let values ← items.toList.mapM (valueOfJson fuel)
      return (.list values)
    | "map" =>
      -- A pair is a two-element array of values, in wire order: the corpus spells
      -- a map as its pairs so that order, which Part 1 makes semantically
      -- significant, cannot be lost in a JSON object.
      let raw ← json.getObjValAs? (Array Json) "pairs"
      let pairs ← raw.toList.mapM (fun pair => do
        let items ← pair.getArr?
        match items.toList with
        | [key, value] => return (← valueOfJson fuel key, ← valueOfJson fuel value)
        | _ => .error "a map pair is exactly two values")
      return (.map pairs)
    | "array" =>
      let ctor ← ofHex (← json.getObjValAs? String "constructor")
      let items ← json.getObjValAs? (Array Json) "items"
      let values ← items.toList.mapM (valueOfJson fuel)
      match ctor.toList with
      | [c] => return (.array c values)
      | _ => .error "an array constructor is one octet"
    | "described" =>
      let descriptor ← valueOfJson fuel (← json.getObjVal? "descriptor")
      let value ← valueOfJson fuel (← json.getObjVal? "value")
      return (.described descriptor value)
    | other => .error s!"unknown value type '{other}'"

/-!
This implementation's values, written in the corpus's vocabulary, so a verdict
report names what it actually saw.

A `mutual` block with `sizeOf` measures, because a map's pair sequence is the one
place where the recursion is not into an immediate subterm: `jsonOfPair` takes a
pair apart, so the pair itself carries the measure.
-/

mutual

/-- This implementation's values, written in the corpus's vocabulary so a verdict
report names what it actually saw. -/
def jsonOfValue : Value → Json
  | .null => Json.mkObj [("type", "null")]
  | .boolean b => Json.mkObj [("type", "boolean"), ("value", b)]
  | .ubyte n => Json.mkObj [("type", "ubyte"), ("value", n.toNat)]
  | .ushort n => Json.mkObj [("type", "ushort"), ("value", n.toNat)]
  | .uint n => Json.mkObj [("type", "uint"), ("value", n.toNat)]
  | .ulong n => Json.mkObj [("type", "ulong"), ("value", n.toNat)]
  | .byte n => Json.mkObj [("type", "byte"), ("value", n.toInt)]
  | .short n => Json.mkObj [("type", "short"), ("value", n.toInt)]
  | .int n => Json.mkObj [("type", "int"), ("value", n.toInt)]
  | .long n => Json.mkObj [("type", "long"), ("value", n.toInt)]
  | .char n => Json.mkObj [("type", "char"), ("codepoint", n.toNat)]
  | .timestamp ms => Json.mkObj [("type", "timestamp"), ("milliseconds", ms.toInt)]
  | .float b => Json.mkObj [("type", "float"), ("hex", toHex b)]
  | .double b => Json.mkObj [("type", "double"), ("hex", toHex b)]
  | .decimal32 b => Json.mkObj [("type", "decimal32"), ("hex", toHex b)]
  | .decimal64 b => Json.mkObj [("type", "decimal64"), ("hex", toHex b)]
  | .decimal128 b => Json.mkObj [("type", "decimal128"), ("hex", toHex b)]
  | .uuid b => Json.mkObj [("type", "uuid"), ("hex", toHex b)]
  | .string s => Json.mkObj [("type", "string"), ("text", s)]
  | .symbol s => Json.mkObj [("type", "symbol"), ("text", s)]
  | .binary b => Json.mkObj [("type", "binary"), ("hex", toHex b.toArray)]
  | .list items => Json.mkObj [("type", "list"), ("items", Json.arr (items.map jsonOfValue).toArray)]
  | .map pairs =>
    Json.mkObj [("type", "map"), ("pairs", Json.arr (pairs.map jsonOfPair).toArray)]
  | .array constructor items =>
    Json.mkObj [("type", "array"), ("constructor", toHex #[constructor]),
                ("items", Json.arr (items.map jsonOfValue).toArray)]
  | .described descriptor value =>
    Json.mkObj [("type", "described"), ("descriptor", jsonOfValue descriptor),
                ("value", jsonOfValue value)]
termination_by value => sizeOf value

/-- One map pair as the corpus's two-element array, keeping the order the wire
carried: a corpus that lost it could not test that a reader preserves it. -/
def jsonOfPair : Value × Value → Json
  | (key, value) => Json.arr #[jsonOfValue key, jsonOfValue value]
termination_by pair => sizeOf pair

end

/-- The reference implementation behind the corpus interface. -/
def refCodec : Codec where
  name := "reference"
  decode := fun bytes =>
    match decode bytes with
    | .ok (value, consumed) => .ok (jsonOfValue value, consumed)
    | .error e => .error s!"{repr e}"
  encode := fun json => do
    let value ← valueOfJson 64 json
    return encode value

end SpecAMQP.Ref.Vectors
