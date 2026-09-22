import Lean.Data.Json
import Ref.Value

/-!
# Running the reference implementation over a vector corpus

Vectors are NDJSON, one per line, authored from the OASIS clauses or from recorded
exchanges — never produced by running this implementation, which would make the
corpus prove only that the implementation equals itself.

Three kinds, matching `tests/contracts/value-vector.schema.json`:

* `decode` — the bytes must decode to the stated value, consuming all of them;
  with `"canonical": true` the value must re-encode to exactly those bytes;
* `encode` — the value must encode to exactly the stated bytes;
* `reject` — the bytes must fail to decode, with the named error condition.

Value representation in JSON, the corpus's own vocabulary rather than this
implementation's types: `null`, `boolean`, `ubyte`, `ushort`, `uint`, `ulong`,
`byte`, `short`, `int`, `long`, `string`, `symbol`, `binary`, `list`, `array`
(with its constructor octet), and `described`.
-/

namespace SpecAMQP.Ref.Vectors

open Lean

/-- Hex digits to octets. -/
def hexDigit (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (UInt8.ofNat (n - 48))
  else if 97 ≤ n && n ≤ 102 then some (UInt8.ofNat (n - 87))
  else if 65 ≤ n && n ≤ 70 then some (UInt8.ofNat (n - 55))
  else none

def ofHex (s : String) : Except String Octets := do
  let digits ← s.toList.mapM (fun c =>
    match hexDigit c with
    | some d => .ok d
    | none => .error s!"not a hex digit: '{c}'")
  if digits.length % 2 != 0 then
    .error "odd number of hex digits"
  let rec pair (ds : List UInt8) (acc : Octets) : Octets :=
    match ds with
    | [] => acc
    | d1 :: d2 :: rest => pair rest (acc.push (d1 * 16 + d2))
    | _ => acc
  .ok (pair digits #[])

def toHex (bytes : Octets) : String :=
  let digit (n : Nat) : Char :=
    if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList (bytes.toList.flatMap (fun b => [digit (b.toNat / 16), digit (b.toNat % 16)]))

/-- A short hex rendering for a failure message, so a mismatch on a large payload
reports where it diverges rather than printing kilobytes. -/
def toHexBrief (bytes : Octets) (limit : Nat := 48) : String :=
  let brief := toHex (bytes.extract 0 (min limit bytes.size))
  if bytes.size > limit then brief ++ s!"… ({bytes.size} octets)" else brief

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
    | "string" => .ok (.string (← json.getObjValAs? String "text"))
    | "symbol" => .ok (.symbol (← json.getObjValAs? String "text"))
    | "binary" => return (.binary (← ofHex (← json.getObjValAs? String "hex")).toList)
    | "list" =>
      let items ← json.getObjValAs? (Array Json) "items"
      let values ← items.toList.mapM (valueOfJson fuel)
      return (.list values)
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

/-- This implementation's values, written in the corpus's vocabulary so a verdict
report names what it actually saw. -/
def jsonOfValue (value : Value) : Json :=
  match value with
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
  | .string s => Json.mkObj [("type", "string"), ("text", s)]
  | .symbol s => Json.mkObj [("type", "symbol"), ("text", s)]
  | .binary b => Json.mkObj [("type", "binary"), ("hex", toHex b.toArray)]
  | .list items => Json.mkObj [("type", "list"), ("items", Json.arr (items.map jsonOfValue).toArray)]
  | .array constructor items =>
    Json.mkObj [("type", "array"), ("constructor", toHex #[constructor]),
                ("items", Json.arr (items.map jsonOfValue).toArray)]
  | .described descriptor value =>
    Json.mkObj [("type", "described"), ("descriptor", jsonOfValue descriptor),
                ("value", jsonOfValue value)]

/-- The verdict for one vector. -/
structure Verdict where
  vector : String
  kind : String
  ok : Bool
  detail : String
deriving Repr

def verdictJson (v : Verdict) : Json :=
  Json.mkObj [("vector", v.vector), ("kind", v.kind), ("status", if v.ok then "pass" else "fail"),
              ("detail", v.detail)]

def runVector (json : Json) : Except String Verdict := do
  let id ← json.getObjValAs? String "vector"
  let kind ← json.getObjValAs? String "kind"
  let bytes ← ofHex (← json.getObjValAs? String "bytes")
  match kind with
  | "decode" =>
    let expected ← valueOfJson 64 (← json.getObjVal? "value")
    let canonical := (json.getObjValAs? Bool "canonical").toOption.getD false
    match decode bytes with
    | .error e =>
      return ⟨id, kind, false, s!"expected a value, got decode error {repr e}"⟩
    | .ok (value, consumed) =>
      if consumed != bytes.size then
        return ⟨id, kind, false, s!"consumed {consumed} of {bytes.size} octets"⟩
      else if value != expected then
        return ⟨id, kind, false,
          s!"decoded {jsonOfValue value |>.compress}, expected {jsonOfValue expected |>.compress}"⟩
      else if canonical then
        let re := encode value
        if re != bytes then
          return ⟨id, kind, false,
            s!"re-encodes to {toHexBrief re}, not {toHexBrief bytes}"⟩
        else
          return ⟨id, kind, true, "decoded and re-encoded to the same octets"⟩
      else
        return ⟨id, kind, true, "decoded"⟩
  | "encode" =>
    let value ← valueOfJson 64 (← json.getObjVal? "value")
    let produced := encode value
    if produced == bytes then
      return ⟨id, kind, true, "encoded to the expected octets"⟩
    else
      return ⟨id, kind, false,
        s!"encoded to {toHexBrief produced}, expected {toHexBrief bytes}"⟩
  | "reject" =>
    let condition ← (← json.getObjVal? "expectError").getObjValAs? String "condition"
    match decode bytes with
    | .error _ => return ⟨id, kind, true, s!"rejected with {condition}"⟩
    | .ok (value, _) =>
      return ⟨id, kind, false, s!"expected rejection, decoded {jsonOfValue value |>.compress}"⟩
  | "property" =>
    -- A law rather than an expectation, so the input domain can be closed instead
    -- of sampled: no answer is written down for the bytes, only a constraint on
    -- what may happen to the value they decode to.
    let property ← json.getObjValAs? String "property"
    match property with
    | "decode-stable" =>
      match decode bytes with
      | .error _ => return ⟨id, kind, true, "no value claimed for these octets"⟩
      | .ok (value, _) =>
        match decode (encode value) with
        | .error e => return ⟨id, kind, false, s!"re-encoding lost the value: {repr e}"⟩
        | .ok (again, _) =>
          if again == value then
            return ⟨id, kind, true, "re-encoding decoded to the same value"⟩
          else
            return ⟨id, kind, false,
              s!"re-encoding decoded to {jsonOfValue again |>.compress}"⟩
    | other => .error s!"unknown property '{other}'"
  | other => .error s!"unknown vector kind '{other}'"

/-- Run every line, returning the verdicts and whether all of them passed. -/
def runCorpus (text : String) : Except String (List Verdict × Bool) := do
  let mut verdicts : List Verdict := []
  let mut allOk := true
  for (line, index) in text.splitOn "\n" |>.zipIdx do
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    match Json.parse trimmed with
    | .error e => .error s!"line {index + 1}: not valid JSON: {e}"
    | .ok json =>
      match runVector json with
      | .error e => .error s!"line {index + 1}: {e}"
      | .ok verdict =>
        verdicts := verdict :: verdicts        -- prepend, then reverse once: a corpus
        if !verdict.ok then allOk := false     -- of tens of thousands is not a place
  return (verdicts.reverse, allOk)             -- for quadratic list append

end SpecAMQP.Ref.Vectors
