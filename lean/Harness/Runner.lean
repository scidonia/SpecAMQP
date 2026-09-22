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

/-- The interface a frame corpus needs from an artefact's frame layer, on the same
terms as `Codec`: octets to a frame in the corpus vocabulary and back, so the
comparison happens in the vocabulary rather than between two artefacts' frame types. -/
structure FrameCodec where
  name : String
  /-- Octets to a corpus frame, and how many octets the frame consumed. -/
  decode : Octets → Except String (Json × Nat)
  /-- A corpus frame back to octets. -/
  encode : Json → Except String Octets

/-- The frame codec a value-only runner carries: frame vectors fail loudly instead of
being read as values, which is what a caller with no frame layer needs to hear. -/
def noFrameCodec : FrameCodec where
  name := "none"
  decode := fun _ => .error "this runner carries no frame codec"
  encode := fun _ => .error "this runner carries no frame codec"

/-- A frame object with its optional fields made explicit, so two frames are compared
as frames rather than as JSON objects that happen to differ in which absent fields they
mention. `size` is deliberately not part of the comparison: it is the octet count the
frame consumed, which the runner checks against the vector's own `size` where the
vector carries one. -/
def frameObject (json : Json) : Json :=
  let text (key : String) : String := (json.getObjValAs? String key).toOption.getD ""
  Json.mkObj [("doff", (json.getObjValAs? Nat "doff").toOption.getD 0),
              ("type", text "type"),
              ("channel", (json.getObjValAs? Nat "channel").toOption.getD 0),
              ("extended", text "extended"),
              ("body", (json.getObjVal? "body").toOption.getD (Json.arr #[])),
              ("payload", text "payload")]

/-- Run one vector with both codecs: the value vocabulary and the frame vocabulary,
each kind dispatched to the layer that owns it. -/
def runVectorWith (codec : Codec) (frames : FrameCodec) (json : Json) : Except String Verdict := do
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
  | "frame-decode" =>
    let bytes ← octetsOf json
    let expected ← json.getObjVal? "frame"
    match frames.decode bytes with
    | .error e => return ⟨id, kind, false, s!"expected a frame, got {e}"⟩
    | .ok (frame, consumed) =>
      let declared := (expected.getObjValAs? Nat "size").toOption
      if declared.isSome && declared != some consumed then
        return ⟨id, kind, false,
          s!"consumed {consumed} octets, and the vector declares SIZE {declared.getD 0}"⟩
      else if frameObject frame != frameObject expected then
        return ⟨id, kind, false,
          s!"decoded {frame.compress}, expected {expected.compress}"⟩
      else
        return ⟨id, kind, true, s!"decoded a frame consuming {consumed} octets"⟩
  | "frame-encode" =>
    let expected ← json.getObjVal? "frame"
    match frames.encode expected with
    | .error e => return ⟨id, kind, false, s!"could not encode: {e}"⟩
    | .ok produced =>
      let bytes ← octetsOf json
      let declared := (expected.getObjValAs? Nat "size").toOption
      if produced != bytes then
        return ⟨id, kind, false,
          s!"encoded to {toHexBrief produced}, expected {toHexBrief bytes}"⟩
      else if declared.isSome && declared != some produced.size then
        return ⟨id, kind, false,
          s!"the vector declares SIZE {declared.getD 0} and the frame is {produced.size} octets"⟩
      else
        return ⟨id, kind, true, "encoded to the expected octets"⟩
  | "frame-reject" =>
    let bytes ← octetsOf json
    match frames.decode bytes with
    | .error reason => return ⟨id, kind, true, reason⟩
    | .ok (frame, _) => return ⟨id, kind, false, s!"expected a refusal, decoded {frame.compress}"⟩
  | other => .error s!"unknown vector kind '{other}'"

/-- Run one vector against the value vocabulary alone, which is what a caller with no
frame layer means by a corpus. -/
def runVector (codec : Codec) (json : Json) : Except String Verdict :=
  runVectorWith codec noFrameCodec json

/-- Run every line with both codecs, returning the verdicts and whether all of them
passed. -/
def runCorpusWith (codec : Codec) (frames : FrameCodec) (text : String) :
    Except String (List Verdict × Bool) := do
  let mut verdicts : List Verdict := []
  let mut allOk := true
  for (line, index) in text.splitOn "\n" |>.zipIdx do
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    match Json.parse trimmed with
    | .error e => .error s!"line {index + 1}: not valid JSON: {e}"
    | .ok json =>
      match runVectorWith codec frames json with
      | .error e => .error s!"line {index + 1}: {e}"
      | .ok verdict =>
        verdicts := verdict :: verdicts        -- prepend, then reverse once: a corpus
        if !verdict.ok then allOk := false     -- of tens of thousands is not a place
  return (verdicts.reverse, allOk)             -- for quadratic list append

/-- Run every line of a value corpus. -/
def runCorpus (codec : Codec) (text : String) : Except String (List Verdict × Bool) :=
  runCorpusWith codec noFrameCodec text

end SpecAMQP.Harness
