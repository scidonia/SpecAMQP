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
`unsupported`, `sizeMismatch`, `malformed`, `limit` or `illegalState` — or `none` for a
message that names none of them. The differential contract reads the same token from
the verdict, so a refusal nobody can name is a failure rather than a detail. The last
class is the exchange corpus's: octets that are perfectly well formed and the *moment*
that is wrong — sending `open` twice, or a frame in a state whose legal sends are `-` —
which is a failure neither the encoder nor the decoder can see on its own. -/
def reasonClassOf (detail : String) : Option String :=
  let head := (detail.splitOn ":").head?.getD "" |>.trimAscii.toString
  if ["truncated", "unassigned", "unsupported", "sizeMismatch", "malformed", "limit",
      "illegalState",
      -- The four failure codes the security artifact declares for `sasl-code`, appended
      -- because they are the only observable a failed authentication has: the artifact
      -- names no condition for it, so a code that did not reach this vocabulary would be
      -- read, reported and compared by nothing. Read from `Generated.Oasis.Choices`
      -- (`amqp:security/section:sasl/type:sasl-code`), never typed.
      "auth", "sys", "sys-perm", "sys-temp"].contains head
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

/-- One step of an exchange vector, as a request to the peer: which way it goes, the
octets the vector carries, and the frame as a structure where the vector writes one.

The expectation is deliberately absent. A peer is asked what it does with a step and
the runner compares the answer, so a connection layer cannot be shaped by what the
corpus expects of it — which is the same reason the codec comparisons happen in the
corpus vocabulary rather than between two artefacts' internal types. -/
structure ExchangeStep where
  /-- `true` when the peer is asked to send this step, `false` when octets arrive. -/
  send : Bool
  /-- The octets the vector carries: on every receive, and on a send whose encoding is
  what the corpus pins. -/
  bytes : Option Octets
  /-- The frame as a structure, on a send the vector writes that way. -/
  value : Option Json

/-- What a peer did with one step, in the corpus vocabulary: whether it took the step,
the octets a send wrote, the state it is left in, and — on a refusal — the protocol
condition and the class-prefixed detail. -/
structure StepOutcome where
  admitted : Bool
  /-- The octets a send wrote. A peer that writes nothing on a send it admitted has
  not produced the frame, which is a failure rather than an empty success. -/
  bytes : Option Octets
  /-- The state after the step, in the connection state table's own names. -/
  state : String
  /-- A refusal's protocol condition, from the generated choice table. -/
  condition : Option String
  /-- The class-prefixed detail: the reason class, then what happened. -/
  detail : String
deriving Repr

/-- An artefact's connection layer behind the corpus interface, on the same terms as
`Codec` and `FrameCodec`. The peer's own state is its own type — the codec translates
into the corpus vocabulary at the boundary and nothing else crosses it — and a state
name the peer's type does not have fails here rather than being read as some default. -/
structure ExchangeCodec where
  name : String
  /-- The peer's own state. -/
  St : Type
  /-- The state a name from the corpus denotes. -/
  start : String → Except String St
  /-- Apply one step, returning what the peer did and where it now is. -/
  step : St → ExchangeStep → Except String (StepOutcome × St)

/-- The connection layer a codec-only runner carries: exchange vectors fail loudly
instead of being read as frames, which is what a caller with no connection layer needs
to hear. -/
def noExchangeCodec : ExchangeCodec where
  name := "none"
  St := Unit
  start := fun _ => .error "this runner carries no connection layer"
  step := fun _ _ => .error "this runner carries no connection layer"

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
    --
    -- And when the vector *pins* a class, only that class is a pass. That comparison
    -- was missing here until a boundary corpus needed it: the field was stated in the
    -- corpus and dropped by the runner, so two artefacts refusing the same buffer with
    -- different classes both reported `pass` and the divergence the field exists to
    -- expose read as agreement. The `encode` path above has compared it since it was
    -- written; this one now does too, so a pinned class means what it says.
    let bytes ← octetsOf json
    let pinned : Option String :=
      match json.getObjVal? "expectError" with
      | .ok expectation => (expectation.getObjValAs? String "reason").toOption
      | .error _ => none
    match codec.decode bytes with
    | .error reason =>
      if pinned.isNone || reasonClassOf reason == pinned then
        return ⟨id, kind, true, reason⟩
      else
        return ⟨id, kind, false,
          s!"refused as {reasonClassOf reason |>.getD "no class"}, and the vector names \
            {pinned.getD ""}: {reason}"⟩
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
    match json.getObjVal? "expectError" with
    | .ok expectation =>
      -- The frame path's encode-direction refusal, on the value path's rule: an
      -- `expectError` on a write means the *encoder* must refuse this value, so the
      -- vector carries no `bytes` — there is no expected encoding, and the octets a
      -- conforming writer must not produce are not something a vector can write down.
      -- The verdict passes when the refusal's class is the one the vector pins, and
      -- reports the octets that were produced when the encoder succeeded instead.
      let pinned := (expectation.getObjValAs? String "reason").toOption
      match frames.encode expected with
      | .error reason =>
        if pinned.isNone || reasonClassOf reason == pinned then
          return ⟨id, kind, true, s!"refused, as the vector expects: {reason}"⟩
        else
          return ⟨id, kind, false,
            s!"refused with {reason}, which does not name {pinned.getD ""}"⟩
      | .ok produced =>
        return ⟨id, kind, false, s!"expected a refusal, encoded to {toHexBrief produced}"⟩
    | .error _ =>
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

/-- One exchange step as a request to the peer: the direction, the octets where the
vector carries them, and the frame as a structure where it writes one. A receive that
carries no octets is a corpus defect, because there is nothing to deliver. -/
def exchangeStepOf (json : Json) : Except String ExchangeStep := do
  let direction ← json.getObjValAs? String "direction"
  let send ←
    match direction with
    | "send" => pure true
    | "receive" => pure false
    | other => .error s!"a step's direction is `send` or `receive`, not '{other}'"
  let bytes ←
    match (json.getObjVal? "bytes").toOption with
    | some _ => some <$> octetsOf json
    | none => pure none
  if !send && bytes.isNone then
    .error "a receive step carries the octets it delivers"
  return ⟨send, bytes, (json.getObjVal? "value").toOption⟩

/-- The layer a state name belongs to: the prefix the schema requires, up to the first
colon. Two layers reuse state names — `DISCARDING` is in the connection's table and in
the session's — so the prefix is what keeps a name unambiguous. -/
def layerOfName (name : String) : String :=
  (name.splitOn ":").head?.getD ""

/-- The state a layer was last left in, or `none` where that layer has not been named
yet: an omitted `state` is compared against its own layer's previous name, never against
the other layer's, which is what makes one exchange able to walk the connection and then
a session. -/
def rememberedState? (names : List (String × String)) (layer : String) : Option String :=
  (names.find? (fun entry => entry.1 == layer)).map (fun entry => entry.2)

/-- Remember a state name under its layer, replacing that layer's previous name. -/
def rememberState (names : List (String × String)) (name : String) : List (String × String) :=
  (layerOfName name, name) :: names.filter (fun entry => entry.1 != layerOfName name)

/-- One step's verdict, compared in the corpus vocabulary.

* an `admitted` step requires the peer to take it, to write exactly the octets the
  vector carries when those are given and the step is a send, and to be in the state the
  vector names — or, when it names none, the state its own layer was last left in, since
  a step that says nothing about the state is a step that leaves it alone;
* a `refused` step requires the peer to refuse it with the named condition and the named
  reason class.

The state is checked for both statuses, because a refusal is a step the connection or
the session answered: a refused frame is answered with a close or an end, which is a
state the corpus can pin, and pretending it left the peer where it was would make the
table's DISCARDING rows unobservable. A layer that has never been named and a step that
names no state is a corpus defect rather than a pass, since there is nothing to compare
against and silence is not agreement. -/
def checkExchangeStep (id : String) (index : Nat) (step : ExchangeStep) (expect : Json)
    (names : List (String × String)) (outcome : StepOutcome) : Verdict :=
  let name := s!"{id}#{index + 1}"
  let wanted := (expect.getObjValAs? String "status").toOption.getD ""
  let failed (detail : String) : Verdict := ⟨name, "exchange", false, detail⟩
  let expectedState? :=
    match (expect.getObjValAs? String "state").toOption with
    | some named => some named
    | none => rememberedState? names (layerOfName outcome.state)
  let passed (detail : String) : Verdict :=
    match expectedState? with
    | none =>
      failed s!"{detail}, and neither the vector nor an earlier step names the \
        {layerOfName outcome.state} layer's state for it to be compared against"
    | some expected =>
      if outcome.state == expected then ⟨name, "exchange", true, detail⟩
      else failed s!"{detail}, but the peer is in {outcome.state} where the vector names \
        {expected}"
  if wanted == "admitted" then
    if !outcome.admitted then
      failed s!"the peer refused the step: {outcome.detail}"
    else match step.bytes with
      | some expected =>
        if step.send then
          match outcome.bytes with
          | some produced =>
            if produced == expected then passed s!"admitted; wrote {toHexBrief produced}"
            else failed s!"wrote {toHexBrief produced}, expected {toHexBrief expected}"
          | none => failed "the peer admitted the send and wrote nothing"
        else
          passed s!"admitted; received {toHexBrief expected}"
      | none => passed s!"admitted; {outcome.detail}"
  else if wanted == "refused" then
    if outcome.admitted then failed s!"the peer admitted the step: {outcome.detail}"
    else
      let expectedCondition := (expect.getObjValAs? String "condition").toOption.getD ""
      let expectedReason := (expect.getObjValAs? String "reason").toOption.getD ""
      let condition := outcome.condition.getD ""
      let reason := (reasonClassOf outcome.detail).getD ""
      if condition != expectedCondition then
        failed s!"refused with condition {condition}, and the vector names \
          {expectedCondition}: {outcome.detail}"
      else if reason != expectedReason then
        failed s!"refused as {reason}, and the vector names {expectedReason}: \
          {outcome.detail}"
      else
        passed s!"refused with {expectedCondition} and {reason}: {outcome.detail}"
  else failed s!"an expectation's status is `admitted` or `refused`, not '{wanted}'"

/-- Run one exchange vector: the start state, the steps in order, and one verdict per
step.

The peer's state is carried between steps by the codec, so a corpus says "this frame,
now" rather than restating the machine; the runner's own view of the state is the *name*
the corpus uses, remembered per layer, which is what lets one exchange walk the
connection and then a session without the two layers' names colliding. -/
def runExchange (codec : ExchangeCodec) (json : Json) : Except String (List Verdict) := do
  let id ← json.getObjValAs? String "vector"
  let startName ← json.getObjValAs? String "start"
  let steps ← json.getObjValAs? (Array Json) "steps"
  if steps.size < 2 then
    .error "an exchange is a sequence of steps, not a single one"
  let mut state ← codec.start startName
  let mut names := rememberState [] startName
  let mut verdicts : List Verdict := []
  for (stepJson, index) in steps.toList.zipIdx do
    let step ← exchangeStepOf stepJson
    let expect ← stepJson.getObjVal? "expect"
    let (outcome, next) ← codec.step state step
    verdicts := checkExchangeStep id index step expect names outcome :: verdicts
    state := next
    names := rememberState names outcome.state
  return verdicts.reverse

/-! ## The message layer's corpus interface

The Part 3 layer's boundary is different from the frame layer's in one way that matters to
the vocabulary: a section or a delivery state can be *well formed and refused*, and the
refusal names a protocol condition. The frame layer's `FrameCodec` returns a bare `String`
detail because its own refusals all carry one condition; a message refusal carries the
condition the corpus compares, so the pair travels together. -/

/-- A refusal in the corpus vocabulary: the protocol condition, from the generated choice
table, and the detail, which leads with a reason class the runner reads. -/
structure Refusal where
  condition : String
  detail : String
deriving Repr

/-- The interface a message corpus needs from an artefact's Part 3 layer, on the same terms
as `Codec` and `FrameCodec`: a section and a message in the corpus vocabulary, so the
comparison happens in the vocabulary rather than between two artefacts' section types.

`policy` is the endpoint's own knowledge, made an explicit input rather than a hidden
decision: the annotations text mandates a detach for an annotation key the receiver does
not understand, so "which keys does this endpoint implement" has to come from outside the
decoder, and both artefacts must be handed the same answer to be comparable. -/
structure MessageCodec where
  name : String
  /-- One section from octets, under the endpoint's policy, and how many octets it consumed. -/
  decodeSection : Json → Octets → Except Refusal (Json × Nat)
  /-- One section back to octets. -/
  encodeSection : Json → Except String Octets
  /-- A whole payload's sections, in the order they appear. -/
  decodeMessage : Json → Octets → Except Refusal (List Json)
  /-- A whole payload's sections back to octets. -/
  encodeMessage : Json → Except String Octets

/-- The message layer a runner with no Part 3 layer carries: message vectors fail loudly
instead of being read as frames. -/
def noMessageCodec : MessageCodec where
  name := "none"
  decodeSection := fun _ _ => .error ⟨"", "this runner carries no message layer"⟩
  encodeSection := fun _ => .error "this runner carries no message layer"
  decodeMessage := fun _ _ => .error ⟨"", "this runner carries no message layer"⟩
  encodeMessage := fun _ => .error "this runner carries no message layer"

/-- What applying one delivery state to a delivery did, in the corpus vocabulary:
whether the state was applied, the delivery's state and settlement afterwards, the
delivery-count and resume point it now carries, whether its message may be delivered to
this link again, and — on a refusal — the condition and the class-led detail.

Every one of these is an observable the corpus compares, because each is a quantity the
artifact's rules move: a machine that recorded a state and not the count it increments,
or a resume point it no longer reports once the delivery is terminal, would be
indistinguishable from a correct one if only the state's name were reported. -/
structure DeliveryOutcome where
  admitted : Bool
  state : String
  deliveryCount : Nat
  settled : Bool
  sectionNumber : Option Nat
  sectionOffset : Option Nat
  redeliveryAllowed : Bool
  condition : Option String
  detail : String
deriving Repr

/-- An artefact's delivery-state machine behind the corpus interface, on the same terms as
`ExchangeCodec`: the peer's own state is its own type, and the codec translates at the
boundary and nothing else. -/
structure DeliveryCodec where
  name : String
  /-- The delivery machine's own state. -/
  St : Type
  /-- The machine a state name from the corpus denotes. -/
  start : String → Except String St
  /-- Apply one delivery step to the machine. The step is the corpus's step object: its
  `apply` carries the delivery state as a corpus value, and its `settled` states whether
  the state is settled. -/
  apply : St → Json → Except String (DeliveryOutcome × St)

/-- The delivery layer a runner with no outcome machine carries. -/
def noDeliveryCodec : DeliveryCodec where
  name := "none"
  St := Unit
  start := fun _ => .error "this runner carries no delivery state machine"
  apply := fun _ _ => .error "this runner carries no delivery state machine"

/-- The codecs one artefact brings to a corpus. Naming them together is what lets one
runner dispatch every kind to the layer that owns it, and what makes an artefact's
coverage of the vocabulary a stated fact rather than an implied one. -/
structure Artefact where
  name : String
  values : Codec
  frames : FrameCodec
  exchanges : ExchangeCodec
  messages : MessageCodec
  deliveries : DeliveryCodec

/-- The policy a vector hands the message layer: the annotation keys this endpoint
implements, absent meaning none. -/
def policyOf (json : Json) : Json :=
  (json.getObjVal? "policy").toOption.getD (Json.mkObj [])

/-- The verdict for a vector that expected a refusal and got a value. -/
def unexpectedValue (id kind what : String) : Verdict :=
  ⟨id, kind, false, s!"expected a refusal, {what}"⟩

/-- The verdict for a refusal, compared on *both* its condition and its reason class. The
message layer is where a well-formed section can be refused, so two artefacts that refuse
for different reasons, or under different conditions, have not agreed about the artifact —
and a comparison that looked only at "it failed" would accept either. -/
def checkRefusal (id kind : String) (json : Json) (reason : Refusal) : Except String Verdict := do
  let expect ← json.getObjVal? "expectError"
  let expectedCondition := (expect.getObjValAs? String "condition").toOption.getD ""
  let expectedReason := (expect.getObjValAs? String "reason").toOption.getD ""
  let observed := (reasonClassOf reason.detail).getD ""
  if reason.condition != expectedCondition then
    return ⟨id, kind, false,
      s!"refused with condition {reason.condition}, and the vector names {expectedCondition}: \
        {reason.detail}"⟩
  else if observed != expectedReason then
    return ⟨id, kind, false,
      s!"refused as {observed}, and the vector names {expectedReason}: {reason.detail}"⟩
  else
    return ⟨id, kind, true, s!"refused with {expectedCondition} and {observed}: {reason.detail}"⟩

/-- A `section-decode` vector: the section must be the one the vector writes, every octet
must be consumed, and `canonical` additionally requires re-encoding to the same octets. -/
def checkSectionDecode (codec : MessageCodec) (id kind : String) (json policy : Json)
    (bytes : Octets) : Except String Verdict := do
  let expected ← json.getObjVal? "section"
  let canonical := (json.getObjValAs? Bool "canonical").toOption.getD false
  match codec.decodeSection policy bytes with
  | .error reason =>
    return ⟨id, kind, false, s!"expected a section, got {reason.condition} {reason.detail}"⟩
  | .ok (decoded, consumed) =>
    if consumed != bytes.size then
      return ⟨id, kind, false, s!"consumed {consumed} of {bytes.size} octets"⟩
    else if decoded != expected then
      return ⟨id, kind, false, s!"decoded {decoded.compress}, expected {expected.compress}"⟩
    else if canonical then
      match codec.encodeSection decoded with
      | .error e => return ⟨id, kind, false, s!"could not re-encode: {e}"⟩
      | .ok re =>
        if re != bytes then
          return ⟨id, kind, false,
            s!"re-encodes to {toHexBrief re}, not {toHexBrief bytes}"⟩
        else return ⟨id, kind, true, "decoded and re-encoded to the same octets"⟩
    else return ⟨id, kind, true, "decoded"⟩

/-- A `section-encode` vector: the writer must produce the vector's octets. -/
def checkSectionEncode (codec : MessageCodec) (id kind : String) (json : Json) :
    Except String Verdict := do
  let expected ← json.getObjVal? "section"
  let bytes ← octetsOf json
  match codec.encodeSection expected with
  | .error e => return ⟨id, kind, false, s!"could not encode: {e}"⟩
  | .ok produced =>
    if produced == bytes then return ⟨id, kind, true, "encoded to the expected octets"⟩
    else
      return ⟨id, kind, false,
        s!"encoded to {toHexBrief produced}, expected {toHexBrief bytes}"⟩

/-- A `message-decode` vector, on the terms `section-decode` sets for one section: the
section list must be the one the vector writes, every octet consumed, and `canonical`
requiring the same octets back. -/
def checkMessageDecode (codec : MessageCodec) (id kind : String) (json policy : Json)
    (bytes : Octets) : Except String Verdict := do
  let expected ← json.getObjValAs? (Array Json) "sections"
  let canonical := (json.getObjValAs? Bool "canonical").toOption.getD false
  match codec.decodeMessage policy bytes with
  | .error reason =>
    return ⟨id, kind, false, s!"expected sections, got {reason.condition} {reason.detail}"⟩
  | .ok sections =>
    if sections.toArray != expected then
      return ⟨id, kind, false,
        s!"decoded {(Json.arr sections.toArray).compress}, expected \
          {(Json.arr expected).compress}"⟩
    else if canonical then
      match codec.encodeMessage (Json.arr sections.toArray) with
      | .error e => return ⟨id, kind, false, s!"could not re-encode: {e}"⟩
      | .ok re =>
        if re != bytes then
          return ⟨id, kind, false,
            s!"re-encodes to {toHexBrief re}, not {toHexBrief bytes}"⟩
        else return ⟨id, kind, true, "decoded and re-encoded to the same octets"⟩
    else return ⟨id, kind, true, s!"decoded {sections.length} section(s)"⟩

/-- A `message-encode` vector: the writer must produce the vector's octets. -/
def checkMessageEncode (codec : MessageCodec) (id kind : String) (json : Json) :
    Except String Verdict := do
  let sections ← json.getObjVal? "sections"
  let bytes ← octetsOf json
  match codec.encodeMessage sections with
  | .error e => return ⟨id, kind, false, s!"could not encode: {e}"⟩
  | .ok produced =>
    if produced == bytes then return ⟨id, kind, true, "encoded to the expected octets"⟩
    else
      return ⟨id, kind, false,
        s!"encoded to {toHexBrief produced}, expected {toHexBrief bytes}"⟩

/-- One message vector's expectation against a codec: the kinds are the message layer's
own, and each is checked above on the terms its direction sets. -/
def runMessageVector (codec : MessageCodec) (json : Json) : Except String Verdict := do
  let id ← json.getObjValAs? String "vector"
  let kind ← json.getObjValAs? String "kind"
  let policy := policyOf json
  match kind with
  | "section-decode" =>
    checkSectionDecode codec id kind json policy (← octetsOf json)
  | "section-encode" => checkSectionEncode codec id kind json
  | "section-reject" =>
    match codec.decodeSection policy (← octetsOf json) with
    | .error reason => checkRefusal id kind json reason
    | .ok _ => return unexpectedValue id kind "decoded the section"
  | "message-decode" =>
    checkMessageDecode codec id kind json policy (← octetsOf json)
  | "message-encode" => checkMessageEncode codec id kind json
  | "message-reject" =>
    match codec.decodeMessage policy (← octetsOf json) with
    | .error reason => checkRefusal id kind json reason
    | .ok _ => return unexpectedValue id kind "decoded the message"
  | other => .error s!"unknown vector kind '{other}'"

/-- One delivery step's verdict, compared in the corpus vocabulary. The step writes the
state to apply and whether it is settled; the expectation names the status, the state
afterwards and every quantity the rules move, so a machine that applied the state but
mis-counted the delivery, or kept a resume point past the point the delivery can be
resumed, fails here rather than passing on the state's name alone. -/
def checkDeliveryStep (id : String) (index : Nat) (expect : Json)
    (outcome : DeliveryOutcome) : Verdict :=
  let name := s!"{id}#{index + 1}"
  let failed (detail : String) : Verdict := ⟨name, "delivery", false, detail⟩
  let wanted := (expect.getObjValAs? String "status").toOption.getD ""
  let quantity (key : String) (observed : Nat) : Except String Unit :=
    match (expect.getObjValAs? Nat key).toOption with
    | some expected =>
      if observed == expected then .ok ()
      else .error s!"the {key} is {observed}, and the vector names {expected}"
    | none => .ok ()
  let compare : Except String Unit := do
    quantity "delivery-count" outcome.deliveryCount
    match (expect.getObjValAs? Bool "settled").toOption with
    | some expected =>
      if outcome.settled == expected then .ok ()
      else .error s!"settled is {outcome.settled}, and the vector names {expected}"
    | none => .ok ()
    match (expect.getObjValAs? Bool "redelivery-allowed").toOption with
    | some expected =>
      if outcome.redeliveryAllowed == expected then .ok ()
      else .error s!"redelivery-allowed is {outcome.redeliveryAllowed}, and the vector names {expected}"
    | none => .ok ()
    match (expect.getObjValAs? Nat "section-number").toOption with
    | some expected =>
      match outcome.sectionNumber with
      | some observed =>
        if observed == expected then .ok ()
        else .error s!"the section-number is {observed}, and the vector names {expected}"
      | none => .error "the resume point is not reported, and the vector names one"
    | none => .ok ()
    match (expect.getObjValAs? Nat "section-offset").toOption with
    | some expected =>
      match outcome.sectionOffset with
      | some observed =>
        if observed == expected then .ok ()
        else .error s!"the section-offset is {observed}, and the vector names {expected}"
      | none => .error "the resume point is not reported, and the vector names one"
    | none => .ok ()
  let stateMatches : Except String Unit :=
    if outcome.state == (expect.getObjValAs? String "state").toOption.getD "" then .ok ()
    else .error s!"the delivery is in {outcome.state}, and the vector names \
      {(expect.getObjValAs? String "state").toOption.getD ""}"
  let observed : Except String Unit := do
    compare
    stateMatches
  if wanted == "admitted" then
    if !outcome.admitted then failed s!"the delivery refused the state: {outcome.detail}"
    else match observed with
      | .error detail => failed detail
      | .ok () => ⟨name, "delivery", true, s!"applied; {outcome.detail}"⟩
  else if wanted == "refused" then
    if outcome.admitted then failed s!"the delivery applied the state: {outcome.detail}"
    else
      let expectedCondition := (expect.getObjValAs? String "condition").toOption.getD ""
      let expectedReason := (expect.getObjValAs? String "reason").toOption.getD ""
      let observedReason := (reasonClassOf outcome.detail).getD ""
      if outcome.condition.getD "" != expectedCondition then
        failed s!"refused with condition {outcome.condition.getD ""}, and the vector names \
          {expectedCondition}: {outcome.detail}"
      else if observedReason != expectedReason then
        failed s!"refused as {observedReason}, and the vector names {expectedReason}: \
          {outcome.detail}"
      else match observed with
        | .error detail => failed detail
        | .ok () =>
          ⟨name, "delivery", true, s!"refused with {expectedCondition} and {observedReason}"⟩
  else failed s!"an expectation's status is `admitted` or `refused`, not '{wanted}'"

/-- Run one delivery vector: the start state, then the states applied to it in order, one
verdict per step. The machine is carried between steps by the codec, so a corpus says
"this state, now" rather than restating the machine — and the observable quantities are
compared at every step, which is what makes a state machine a sequence of measurements
rather than a sequence of names. -/
def runDelivery (codec : DeliveryCodec) (json : Json) : Except String (List Verdict) := do
  let id ← json.getObjValAs? String "vector"
  let startName ← json.getObjValAs? String "start"
  let steps ← json.getObjValAs? (Array Json) "steps"
  if steps.isEmpty then .error "a delivery vector applies at least one state"
  let mut state ← codec.start startName
  let mut verdicts : List Verdict := []
  for (stepJson, index) in steps.toList.zipIdx do
    let expect ← stepJson.getObjVal? "expect"
    let (outcome, next) ← codec.apply state stepJson
    verdicts := checkDeliveryStep id index expect outcome :: verdicts
    state := next
  return verdicts.reverse

/-- Run one line: a delivery or an exchange yields one verdict per step, a message-layer
kind yields one verdict, and every remaining kind yields the single verdict its codec
comparison produces. -/
def runLineWith (art : Artefact) (json : Json) : Except String (List Verdict) :=
  match (json.getObjValAs? String "kind").toOption with
  | some "exchange" => runExchange art.exchanges json
  | some "delivery" => runDelivery art.deliveries json
  | some "section-decode" | some "section-encode" | some "section-reject"
  | some "message-decode" | some "message-encode" | some "message-reject" =>
    return [← runMessageVector art.messages json]
  | _ => do
    let verdict ← runVectorWith art.values art.frames json
    return [verdict]

/-- Run every line with one artefact's codecs, returning the verdicts and whether all of
them passed. -/
def runCorpusArtefact (art : Artefact) (text : String) : Except String (List Verdict × Bool) := do
  let mut verdicts : List Verdict := []
  let mut allOk := true
  for (line, index) in text.splitOn "\n" |>.zipIdx do
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    match Json.parse trimmed with
    | .error e => .error s!"line {index + 1}: not valid JSON: {e}"
    | .ok json =>
      match runLineWith art json with
      | .error e => .error s!"line {index + 1}: {e}"
      | .ok lineVerdicts =>
        for verdict in lineVerdicts do
          verdicts := verdict :: verdicts      -- prepend, then reverse once: a corpus
          if !verdict.ok then allOk := false   -- of tens of thousands is not a place
  return (verdicts.reverse, allOk)             -- for quadratic list append

/-- Run every line of a value corpus with an artefact that carries only a value codec,
which is what a corpus of type-system vectors needs. -/
def runCorpus (codec : Codec) (text : String) : Except String (List Verdict × Bool) :=
  runCorpusArtefact
    { name := codec.name, values := codec, frames := noFrameCodec,
      exchanges := noExchangeCodec, messages := noMessageCodec,
      deliveries := noDeliveryCodec } text

end SpecAMQP.Harness
