import Harness.Codec

/-!
# The corpus runner

One runner, used by both artefacts: a vector's expectation is checked against the
codec it is handed, so a disagreement between two artefacts is a disagreement about
the wire format rather than about a harness. Comparisons happen in the corpus
vocabulary — never between the artefacts' internal representations, which would
need a third artefact to map and another thing to trust.
-/

namespace SpecAMQP.Harness

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

/-- The octets a vector carries. Read only where a vector's kind requires them: an
encode vector that expects a refusal carries none, because what it pins is that the
value cannot be written at all, and its `bytes` would have to be the octets a
conforming writer must not produce. -/
def octetsOf (json : Json) : Except String Octets := do
  return (← ofHex (← json.getObjValAs? String "bytes"))

/-- The reason class a codec message leads with — `truncated`, `unassigned`,
`unsupported`, `sizeMismatch`, `malformed` or `limit` — or `none` for a message that
names none of them. The differential contract reads the same token from the verdict,
so a refusal nobody can name is a failure rather than a detail. -/
def reasonClassOf (detail : String) : Option String :=
  let head := (detail.splitOn ":").head?.getD "" |>.trimAscii.toString
  if ["truncated", "unassigned", "unsupported", "sizeMismatch", "malformed", "limit"].contains head
  then some head
  else none

def runVector (codec : Codec) (json : Json) : Except String Verdict := do
  let id ← json.getObjValAs? String "vector"
  let kind ← json.getObjValAs? String "kind"
  match kind with
  | "decode" =>
    let bytes ← octetsOf json
    let expected ← json.getObjVal? "value"
    let canonical := (json.getObjValAs? Bool "canonical").toOption.getD false
    match codec.decode bytes with
    | .error e =>
      return ⟨id, kind, false, s!"expected a value, got decode error {e}"⟩
    | .ok (value, consumed) =>
      if consumed != bytes.size then
        return ⟨id, kind, false, s!"consumed {consumed} of {bytes.size} octets"⟩
      else if value != expected then
        return ⟨id, kind, false,
          s!"decoded {value.compress}, expected {expected.compress}"⟩
      else if canonical then
        match codec.encode value with
        | .error e => return ⟨id, kind, false, s!"could not re-encode: {e}"⟩
        | .ok re =>
          if re != bytes then
            return ⟨id, kind, false,
              s!"re-encodes to {toHexBrief re}, not {toHexBrief bytes}"⟩
          else
            return ⟨id, kind, true, "decoded and re-encoded to the same octets"⟩
      else
        return ⟨id, kind, true, "decoded"⟩
  | "encode" =>
    let value ← json.getObjVal? "value"
    match json.getObjVal? "expectError" with
    | .ok expected =>
      -- An `expectError` on an encode vector means the encoder must refuse this value.
      -- This is how an encode-direction refusal is expressed, and it matters because a
      -- writer's domain has to sit inside what its reader accepts: one that emitted
      -- octets it then refused to read back would be inconsistent with its own reader.
      -- The refusal's class must be the one the vector pins.
      let pinned := (expected.getObjValAs? String "reason").toOption
      match codec.encode value with
      | .error reason =>
        if pinned.isNone || reasonClassOf reason == pinned then
          return ⟨id, kind, true, s!"refused, as the vector expects: {reason}"⟩
        else
          return ⟨id, kind, false,
            s!"refused with {reason}, which does not name {pinned.getD ""}"⟩
      | .ok produced =>
        return ⟨id, kind, false, s!"expected a refusal, encoded to {toHexBrief produced}"⟩
    | .error _ =>
      let bytes ← octetsOf json
      match codec.encode value with
      | .error e => return ⟨id, kind, false, s!"could not encode: {e}"⟩
      | .ok produced =>
        if produced == bytes then
          return ⟨id, kind, true, "encoded to the expected octets"⟩
        else
          return ⟨id, kind, false,
            s!"encoded to {toHexBrief produced}, expected {toHexBrief bytes}"⟩
  | "reject" =>
    -- The codec's own message is the detail, and it leads with its reason class
    -- (`truncated: …`, `limit: …`): the *implementation's* reason is the observable
    -- the differential contract compares, and a harness that replaced it with the
    -- vector's protocol condition would make every refusal look alike.
    let bytes ← octetsOf json
    match codec.decode bytes with
    | .error reason => return ⟨id, kind, true, reason⟩
    | .ok (value, _) =>
      return ⟨id, kind, false, s!"expected rejection, decoded {value.compress}"⟩
  | "property" =>
    -- A law rather than an expectation, so the input domain can be closed instead
    -- of sampled: no answer is written down for the bytes, only a constraint on
    -- what may happen to the value they decode to.
    let bytes ← octetsOf json
    let property ← json.getObjValAs? String "property"
    match property with
    | "decode-stable" =>
      match codec.decode bytes with
      | .error _ => return ⟨id, kind, true, "no value claimed for these octets"⟩
      | .ok (value, _) =>
        match codec.encode value with
        | .error e => return ⟨id, kind, false, s!"could not re-encode: {e}"⟩
        | .ok re =>
          match codec.decode re with
          | .error e => return ⟨id, kind, false, s!"re-encoding lost the value: {e}"⟩
          | .ok (again, _) =>
            if again == value then
              return ⟨id, kind, true, "re-encoding decoded to the same value"⟩
            else
              return ⟨id, kind, false, s!"re-encoding decoded to {again.compress}"⟩
    | other => .error s!"unknown property '{other}'"
  | other => .error s!"unknown vector kind '{other}'"

/-- Run every line, returning the verdicts and whether all of them passed. -/
def runCorpus (codec : Codec) (text : String) : Except String (List Verdict × Bool) := do
  let mut verdicts : List Verdict := []
  let mut allOk := true
  for (line, index) in text.splitOn "\n" |>.zipIdx do
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    match Json.parse trimmed with
    | .error e => .error s!"line {index + 1}: not valid JSON: {e}"
    | .ok json =>
      match runVector codec json with
      | .error e => .error s!"line {index + 1}: {e}"
      | .ok verdict =>
        verdicts := verdict :: verdicts        -- prepend, then reverse once: a corpus
        if !verdict.ok then allOk := false     -- of tens of thousands is not a place
  return (verdicts.reverse, allOk)             -- for quadratic list append

end SpecAMQP.Harness
