import Generated.Oasis.Choices
import Generated.Oasis.Constants
import Generated.Oasis.Fields
import Generated.Oasis.Types
import Ref.Frame

/-!
# The reference implementation of the connection layer

Written from Part 2's connection lifecycle — the Connection State Table (picture 24),
the Connection State Diagram (picture 23), the Frame Dispatch Table (picture 10), the
Protocol Header Layout (picture 11) and the security section's SASL exchange — and
independently of `Spec.Connection`: the two share no definition, so their agreement
over the exchange corpus is evidence about the artifact rather than a tautology. This
is a second reading of the same four pictures and the same clauses, and where the
specification transcribes the table as two columns of *classes*, this one writes each
row out as a record of what it admits.

Three readings decide the behaviour, on the same terms as the specification's:

* the table's `**` column is not its `*` column: `**` admits only frames "known a priori
  to conform to the peer's capabilities and limitations", which before the partner's
  `open` arrives means the a priori limits — MIN-MAX-FRAME-SIZE octets and channel 0;
* every refusal carries the one connection-error the artifact raises for a wire-level
  failure, read from the generated choice table, with the cause as the reason class;
* the SASL layer's dialogue runs on the header exchange's START/HDR_SENT/HDR_EXCH path
  and, once its outcome succeeds, the peers exchange protocol headers again for AMQP.

What it does not do: it does not build the `close` frame a refused frame obliges, and
it does not enforce the `open`'s mandatory fields.
-/

namespace SpecAMQP.Ref.Connection

open SpecAMQP.Generated.Oasis
  (ChoiceDecl FieldDecl TypeDecl choices constantValue? errorConditionsOf fieldsOf types)

/-! ## The protocol header, as the layout picture draws it -/

/-- A protocol header: the protocol id octet and the three version octets. The id is a
number here rather than an enumeration, because the layout gives it one octet and the
only question the artifact asks about it is which protocol it names. -/
structure Header where
  protocolId : Nat
  major : Nat
  minor : Nat
  revision : Nat
deriving Repr, BEq, DecidableEq

/-- The protocol id AMQP itself is negotiated under. -/
def amqpId : Nat := 0

/-- The protocol id the SASL security layer is negotiated under. -/
def saslId : Nat := 3

/-- The protocol ids this implementation speaks. Protocol id two (TLS) is assigned by
the artifact and not spoken here. -/
def speaksId (protocolId : Nat) : Bool := protocolId == amqpId || protocolId == saslId

/-- The protocol id's name, for a diagnostic. -/
def idName (protocolId : Nat) : String :=
  if protocolId == amqpId then "AMQP"
  else if protocolId == saslId then "SASL"
  else if protocolId == 2 then "TLS"
  else s!"protocol id {protocolId}"

/-- A `<definition>` constant as a number, by name. -/
def constantNumber (name : String) : Option Nat :=
  (constantValue? name).bind (fun text => text.toNat?)

/-- The version the artifact states for a protocol id, read from the generated constant
table: MAJOR/MINOR/REVISION for AMQP and SASL-MAJOR/SASL-MINOR/SASL-REVISION for SASL. -/
def statedVersion (protocolId : Nat) : Option (Nat × Nat × Nat) :=
  if protocolId == amqpId then
    match constantNumber "MAJOR", constantNumber "MINOR", constantNumber "REVISION" with
    | some a, some b, some c => some (a, b, c)
    | _, _, _ => none
  else if protocolId == saslId then
    match constantNumber "SASL-MAJOR", constantNumber "SASL-MINOR",
          constantNumber "SASL-REVISION" with
    | some a, some b, some c => some (a, b, c)
    | _, _, _ => none
  else none

/-- The header this implementation would send for a protocol id it speaks. -/
def ownHeader (protocolId : Nat) : Option Header :=
  match statedVersion protocolId with
  | some (a, b, c) => some ⟨protocolId, a, b, c⟩
  | none => none

/-- The protocol header's width: "In total this is an 8-octet sequence." -/
def headerWidth : Nat := 8

/-- The header's magic: the layout's four octets, the ASCII letters AMQP. -/
def magic : Octets := #[0x41, 0x4D, 0x51, 0x50]

/-- A big-endian field of a buffer already known to hold it. -/
def field (bytes : Octets) (offset width : Nat) : Nat :=
  (bytes.extract offset (offset + width)).foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The header's octets. -/
def Header.octets (header : Header) : Octets :=
  magic ++ #[UInt8.ofNat (header.protocolId % 256), UInt8.ofNat (header.major % 256),
             UInt8.ofNat (header.minor % 256), UInt8.ofNat (header.revision % 256)]

/-- Whether a buffer starts the way a header does. -/
def looksLikeHeader (bytes : Octets) : Bool :=
  bytes.size ≥ 4 && bytes.extract 0 4 == magic

/-! ## The state table (picture 24) -/

/-- The fourteen states of the table. -/
inductive State where
  | start
  | rcvHdr
  | sndHdr
  | bothHdr
  | rcvOpen
  | sndOpen
  | pipeOpen
  | pipeClose
  | pipeOc
  | open
  | rcvClose
  | sndClose
  | discard
  | done
deriving Repr, BEq, DecidableEq

/-- The table's names, which are the vocabulary the corpus uses. -/
def State.label : State → String
  | .start => "START"
  | .rcvHdr => "HDR_RCVD"
  | .sndHdr => "HDR_SENT"
  | .bothHdr => "HDR_EXCH"
  | .rcvOpen => "OPEN_RCVD"
  | .sndOpen => "OPEN_SENT"
  | .pipeOpen => "OPEN_PIPE"
  | .pipeClose => "CLOSE_PIPE"
  | .pipeOc => "OC_PIPE"
  | .open => "OPENED"
  | .rcvClose => "CLOSE_RCVD"
  | .sndClose => "CLOSE_SENT"
  | .discard => "DISCARDING"
  | .done => "END"

/-- The states the table names, for a lookup by name. -/
def State.labels : List State :=
  [.start, .rcvHdr, .sndHdr, .bothHdr, .rcvOpen, .sndOpen, .pipeOpen, .pipeClose,
   .pipeOc, .open, .rcvClose, .sndClose, .discard, .done]

/-- The state a table name denotes. -/
def State.lookup (name : String) : Option State :=
  State.labels.find? (fun state => state.label == name)

/-- The connection action the table's third column names. -/
inductive Action where
  | shutWrite
  | shutRead
  | shutAll
deriving Repr, BEq, DecidableEq

/-- The action's name, as the table writes it. -/
def Action.label : Action → String
  | .shutWrite => "TCP Close for Write"
  | .shutRead => "TCP Close for Read"
  | .shutAll => "TCP Close"

/-- One row of the table: which of the column's cases it admits on each side, and the
action that follows.

The two send cases that admit *frames* are kept apart, because they are what the table's
`*` and `**` marks mean: `frames` is any frame, and `expected` is any frame known a
priori to conform to the partner's capabilities and limitations — which, before the
partner's `open`, is the a priori limit rather than whatever the partner will later
allow. -/
structure Row where
  /-- The column is HDR: the protocol header, and nothing else. -/
  sendsHeader : Bool
  /-- The column is OPEN: the open performative, and nothing else. -/
  sendsOpen : Bool
  /-- The column is `*`: any frame. -/
  sendsAny : Bool
  /-- The column is `**`: any frame known a priori to conform. -/
  sendsExpected : Bool
  receivesHeader : Bool
  receivesOpen : Bool
  /-- The receive column is `*`: any frame. -/
  receivesAny : Bool
  action : Option Action

/-- The table, row by row, in the order the artifact lists it. -/
def row : State → Row
  | .start =>
    ⟨true, false, false, false, true, false, false, none⟩
  | .rcvHdr =>
    ⟨true, false, false, false, false, true, false, none⟩
  | .sndHdr =>
    ⟨false, true, false, false, true, false, false, none⟩
  | .bothHdr =>
    ⟨false, true, false, false, false, true, false, none⟩
  | .rcvOpen =>
    ⟨false, true, false, false, false, false, true, none⟩
  | .sndOpen =>
    ⟨false, false, false, true, false, true, false, none⟩
  | .pipeOpen =>
    ⟨false, false, false, true, true, false, false, none⟩
  | .pipeClose =>
    ⟨false, false, false, false, false, true, false, some .shutWrite⟩
  | .pipeOc =>
    ⟨false, false, false, false, true, false, false, some .shutWrite⟩
  | .open =>
    ⟨false, false, true, false, false, false, true, none⟩
  | .rcvClose =>
    ⟨false, false, true, false, false, false, false, some .shutRead⟩
  | .sndClose =>
    ⟨false, false, false, false, false, false, true, some .shutWrite⟩
  | .discard =>
    ⟨false, false, false, false, false, false, true, some .shutWrite⟩
  | .done =>
    ⟨false, false, false, false, false, false, false, some .shutAll⟩

/-- What a step offers, from the connection layer's point of view. -/
inductive Kind where
  | header
  | open
  | close
  | relayed
  | saslFrame
deriving Repr, BEq, DecidableEq

/-- Whether a frame may be sent from a state: the `open` is admitted only by the OPEN
column, and the column's frame cases admit a frame that is not the peer's own `open`.

That exclusion is a reading rather than a transcription. What the artifact says is that the
first frame in each direction contains an `open`, which implies at most one without
forbidding a second; it states no rule about a second `open` at all. The register records
the rule together with the sweep that measured its scope — every permissive cell, both
directions — in `ledger/ambiguities/second-open-refusal.json`. -/
def maySend (state : State) (kind : Kind) : Bool :=
  let r := row state
  match kind with
  | .header => r.sendsHeader
  | .open => r.sendsOpen
  | .saslFrame => false
  | .close | .relayed => r.sendsAny || r.sendsExpected

/-- Whether a frame may be received in a state, on the same terms and with the same
citation for the second-`open` exclusion. -/
def mayReceive (state : State) (kind : Kind) : Bool :=
  let r := row state
  match kind with
  | .header => false
  | .open => r.receivesOpen
  | .saslFrame => false
  | .close | .relayed => r.receivesAny

/-! ## Refusals -/

/-- A refusal: the condition, the reason class, the prose, where it leaves the peer,
and the octets the peer writes while refusing. -/
structure Refusal where
  condition : String
  reasonClass : String
  text : String
  place : Option State
  reply : List Octets

/-- The condition the artifact raises for a wire-level failure: the only connection-error
its clauses raise, out of the generated choice table. -/
def wireCondition : String :=
  match (errorConditionsOf "connection-error").find? (fun c => c.name == "framing-error") with
  | some c => c.value
  | none => "no framing-error in the connection-error choice"

/-- A refusal of one class. -/
def refuse (reasonClass text : String) : Refusal :=
  ⟨wireCondition, reasonClass, text, none, []⟩

/-- A refusal under a named condition, for the refusals that are not wire-level failures:
the condition says which of the artifact's rules the frame broke. -/
def refuseWith (condition reasonClass text : String) : Refusal :=
  ⟨condition, reasonClass, text, none, []⟩

/-- The condition for a frame that is well formed and arrives in a state that does not
permit it: the `amqp-error` family's `illegal-state`, whose definition is "The peer sent a
frame that is not permitted in the current state". The wire condition is a different
failure — "a valid frame header cannot be formed from the incoming byte stream" — and a
peer acts on which one it is told, so the two are kept apart. -/
def stateCondition : String :=
  match (errorConditionsOf "amqp-error").find? (fun c => c.name == "illegal-state") with
  | some c => c.value
  | none => "no illegal-state in the amqp-error choice"

/-- The rendered detail: what the corpus and the differential comparison read, class
first. -/
def Refusal.detail (refusal : Refusal) : String :=
  s!"{refusal.reasonClass}: {refusal.text}"

/-! ## The endpoint -/

/-- The limits one side declares: the largest frame it accepts and the highest channel
number it accepts. -/
structure Bounds where
  frames : Nat
  channels : Nat
deriving Repr, BEq, DecidableEq

/-- The largest frame both peers must accept, from the artifact's constant. -/
def minMaxFrameSize : Nat := (constantNumber "MIN-MAX-FRAME-SIZE").getD 0

/-- What holds before any explicit negotiation: MIN-MAX-FRAME-SIZE octets and channel 0. -/
def Bounds.aPriori : Bounds := ⟨minMaxFrameSize, 0⟩

/-- Where the SASL dialogue stands. -/
inductive Sasl where
  | idle
  | wantsMechanisms
  | wantsInit
  | wantsOutcome
deriving Repr, BEq, DecidableEq

/-- One peer's state: the table's state, the protocol id whose header exchange this is,
the SASL dialogue's stage, which end of it this peer is, the mechanisms on offer, and
the two sides' bounds. -/
structure Peer where
  state : State
  protocolId : Nat
  sasl : Sasl
  announcedBy : Option Bool
  offered : List String
  own : Bounds
  partner : Bounds
deriving Repr

/-- A peer that has exchanged nothing: the AMQP layer, from START. -/
def Peer.new : Peer :=
  ⟨.start, amqpId, .idle, none, [], Bounds.aPriori, Bounds.aPriori⟩

/-! ## Reading the frames -/

/-- The anchor path of a declared type, by name, so nothing here writes an
`amqp:`-shaped symbol. -/
def anchorOf (typeName : String) : Option String :=
  (types.find? (fun t => t.name == typeName)).map (fun t => t.path)

/-- A declared field, by name. -/
def declaredField (typeName fieldName : String) : Option FieldDecl :=
  match anchorOf typeName with
  | none => none
  | some path => (fieldsOf path).find? (fun f => f.name == fieldName)

/-- A field's declared default as a number. -/
def declaredDefault (typeName fieldName : String) : Option Nat :=
  match declaredField typeName fieldName with
  | some f => f.defaultValue.bind (fun text => text.toNat?)
  | none => none

/-- A choice's declared value, by the type that declares it. -/
def declaredChoice (typeName choiceName : String) : Option String :=
  match anchorOf typeName with
  | none => none
  | some path =>
    (choices.find? (fun c => c.ownerPath == path && c.name == choiceName)).map
      (fun c => c.value)

/-- The condition for a performative whose field breaks a rule the declared surface
states: the `amqp-error` family's `invalid-field`, read from the generated choice table
rather than typed. -/
def invalidFieldCondition : String :=
  (declaredChoice "amqp-error" "invalid-field").getD "no invalid-field in the choice table"

/-- The type a described value carries, by its descriptor. -/
def bodyType (body : Value) : Option TypeDecl :=
  match body with
  | .described descriptor _ =>
    match descriptor with
    | .ulong code =>
      types.find? (fun t => match t.descriptor with
        | some d => d.domain * 2 ^ 32 + d.code == code.toNat
        | none => false)
    | .symbol name =>
      -- The artifact gives a descriptor two forms — a code and a declared name — and a peer that
      -- does not know the code can still name the type, so a describe-by-name body is well formed.
      -- The name to match is the *descriptor's* declared name (`amqp:open:list`), which is what the
      -- declared surface records in `descriptor.name`; a bare type name is not a descriptor name and
      -- matching it resolves only bodies no conforming writer produces.
      types.find? (fun t => match t.descriptor with
        | some d => d.name == name
        | none => false)
    | _ => none
  | _ => none

/-- The kind a frame body is, from the declared type its descriptor names. -/
def kindOfBody (body : Value) : Kind :=
  match bodyType body with
  | none => .relayed
  | some t =>
    if t.name == "open" then .open
    else if t.name == "close" then .close
    else if t.provides.contains "sasl-frame" then .saslFrame
    else .relayed

/-- A SASL performative's name, from the declared type its descriptor names. -/
def saslName (body : Value) : String :=
  match bodyType body with
  | some t => t.name
  | none => ""

/-- A performative's field values in wire order. -/
def fieldList (body : Value) : List Value :=
  match body with
  | .described _ (.list items) => items
  | _ => []

/-- One field's value, by the declared index; a list that stops short leaves the
remaining fields null. -/
def valueOfField (typeName fieldName : String) (body : Value) : Option Value :=
  match declaredField typeName fieldName with
  | some f => if f.index == 0 then none else (fieldList body)[f.index - 1]?
  | none => none

/-- The mandatory fields of a performative that it does not carry: the rule is the
artifact's — a field the declared surface marks mandatory is one the performative must
set — and the list comes from the generated field table rather than from memory, so a
field the artifact makes mandatory cannot be caught by one layer and missed by another.
No field is named here. -/
def missingMandatory (typeName : String) (body : Value) : List String :=
  match anchorOf typeName with
  | none => []
  | some path =>
    (fieldsOf path).filterMap (fun (field : FieldDecl) =>
      if !field.mandatory then none
      else
        match valueOfField typeName field.name body with
        | some .null | none => some field.name
        | some _ => none)

/-- The declared surface's mandatory-field rule for a named performative: a performative
that does not carry a field the artifact marks mandatory is not the performative its
descriptor names, and the refusal is the one the AMQP path already raises for `open` and
`close` — the artifact's own `invalid-field`, with the list read from the generated field
table rather than written here.

The rule is enforced in the SASL layer for the same reason it is enforced in the AMQP
one: a `sasl-challenge` with no `challenge` and a `sasl-response` with no `response` were
taken as the performatives they name, a `sasl-outcome` with no `code` silently became a
failure, and a `sasl-init` with no `mechanism` was refused as an *unoffered mechanism*
under the wire-level condition — a misattributed failure rather than a weaker check.

Keyed by the performative's declared type name, which each arm knows before it calls
this: the arm's own name guard has already refused every frame that is not the one the
dialogue is waiting for. -/
def refuseUnlessComplete (typeName : String) (body : Value) : Except Refusal Unit :=
  let absent := missingMandatory typeName body
  if absent.isEmpty then .ok ()
  else
    .error (refuseWith invalidFieldCondition "malformed" s!"the {typeName} performative \
      does not carry {absent}, and the declared surface marks it mandatory")

/-- The refusal a failed SASL dialogue raises: no condition, because the artifact obliges the
peer to close and names an "authentication-failure close-code" that no value of the generated
`connection-error` choice carries, so there is no condition to report and none is invented;
and the reason class is the code's own declared name from the `sasl-code` choice, because the
four failures are distinct values for distinct causes. The place is END in both directions.

Written as a named constructor rather than read from the table because it *is* the reading:
the artifact declares no condition for a failed authentication. -/
def saslFailure (reasonClass prose : String) : Refusal :=
  { condition := "", reasonClass := reasonClass, text := s!"{reasonClass}: {prose}",
    place := some State.done, reply := [] }

/-- A value's number, whichever integer width carried it. -/
def numberOf : Value → Option Nat
  | .ubyte n => some n.toNat
  | .ushort n => some n.toNat
  | .uint n => some n.toNat
  | .ulong n => some n.toNat
  | _ => none

/-- A `binary` value's payload: the one form whose payload is a byte string, and the form a
field declared `binary` — like `delivery-tag` — carries. -/
def octetsOf : Value → Option (List UInt8)
  | .binary b => some b
  | _ => none

/-- The symbols a `multiple` field carries: one symbol is the one-element wire form. -/
def symbolList : Value → List String
  | .symbol s => [s]
  | .list items =>
    items.filterMap (fun i => match i with | .symbol s => some s | _ => none)
  | .array _ items =>
    items.filterMap (fun i => match i with | .symbol s => some s | _ => none)
  | _ => []

/-- The primitive a declared type resolves to, following a restricted type to its source:
a field's value must be of the declared type, not merely a number. -/
def primitiveOfDeclared (typeName : String) : Option String :=
  let rec follow (name : String) (fuel : Nat) : Option String :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match types.find? (fun t => t.name == name) with
      | none => none
      | some declaration =>
        match declaration.typeClass, declaration.source with
        | .restricted, some source => follow source fuel
        | _, _ => some declaration.name
  follow typeName 8

/-- A value's primitive name, which is the vocabulary the declared types use. -/
def primitiveName : Value → String
  | .null => "null" | .boolean _ => "boolean"
  | .ubyte _ => "ubyte" | .ushort _ => "ushort" | .uint _ => "uint" | .ulong _ => "ulong"
  | .byte _ => "byte" | .short _ => "short" | .int _ => "int" | .long _ => "long"
  | .char _ => "char" | .timestamp _ => "timestamp"
  | .float _ => "float" | .double _ => "double"
  | .decimal32 _ => "decimal32" | .decimal64 _ => "decimal64" | .decimal128 _ => "decimal128"
  | .uuid _ => "uuid" | .binary _ => "binary" | .string _ => "string" | .symbol _ => "symbol"
  | .list _ => "list" | .map _ => "map" | .array _ _ => "array" | .described _ _ => "described"

/-- An integer field, refusing a value whose type is not the declared one — the check that
stops a `channel-max` declared a `ushort` from being installed when it arrives as a
`ulong`. -/
def integerField (typeName fieldName : String) (body : Value) :
    Except Refusal Nat :=
  match valueOfField typeName fieldName body with
  | none | some .null =>
    match declaredDefault typeName fieldName with
    | some n => .ok n
    | none =>
      .error (refuseWith invalidFieldCondition "malformed"
        s!"{typeName}.{fieldName} is unset and the declared \
          surface gives it no default")
  | some v =>
    match numberOf v with
    | some n =>
      match primitiveOfDeclared (match declaredField typeName fieldName with
                                 | some field => field.typeName
                                 | none => "") with
      | some declared =>
        if primitiveName v == declared then .ok n
        else
          .error (refuseWith invalidFieldCondition "malformed"
            s!"{typeName}.{fieldName} is declared a {declared} and this one is a \
              {primitiveName v}")
      | none => .ok n
    | none =>
      .error (refuseWith invalidFieldCondition "malformed"
        s!"{typeName}.{fieldName} is not an integer, and the \
          artifact declares it one")

/-- The bounds an `open` declares. -/
def openBounds (body : Value) : Except Refusal Bounds := do
  let frames ← integerField "open" "max-frame-size" body
  let channels ← integerField "open" "channel-max" body
  return ⟨frames, channels⟩

/-- The code a successful SASL outcome carries, from the `sasl-code` choice table. -/
def successCode : Option Nat :=
  (declaredChoice "sasl-code" "ok").bind (fun text => text.toNat?)

/-- The name the `sasl-code` choice declares for an outcome code, or `none` for a value it
does not declare: the five values are read from the generated choice table rather than
written here. The four failure codes are distinct values for distinct causes, so an outcome
that reported them all as "not ok" would have read the field and kept only a boolean. -/
def declaredCodeName (code : Nat) : Option String :=
  match anchorOf "sasl-code" with
  | none => none
  | some path =>
    (choices.find?
      (fun c => c.ownerPath == path && c.value.toNat? == some code)).map (fun c => c.name)

/-- The names the `sasl-code` choice declares, in the table's order, for a diagnostic. -/
def declaredCodeNames : List String :=
  match anchorOf "sasl-code" with
  | none => []
  | some path => (choices.filter (fun c => c.ownerPath == path)).map (fun c => c.name)

/-- Whether a declared field is set: present and not null. -/
def declaredFieldSet (typeName fieldName : String) (body : Value) : Bool :=
  match valueOfField typeName fieldName body with
  | some .null | none => false
  | some _ => true

/-! ## Applying a step -/

/-- Where a refusal leaves the peer: a refused send writes nothing and moves nothing; a
refused receive is answered by closing, which in the AMQP layer is the error-triggered
close the table calls DISCARDING, and in the SASL layer — where no AMQP close can be
written because the layer is not established — is the transport being cut; and a
violation on a connection that has already ended leaves it ended. -/
def placeRefusal (peer : Peer) (outbound : Bool) (r : Refusal) : Refusal :=
  match r.place with
  | some _ => r
  | none =>
    if outbound then r
    else if peer.state == State.done then { r with place := some State.done }
    else if peer.protocolId == saslId then { r with place := some State.done }
    else { r with place := some State.discard }

/-- The bounds a frame's size and channel are measured against: the partner's for a
send, this peer's own for a receive, and — for a send from a `**` row — the a priori
bounds, because that column admits only what is known a priori to conform. -/
def boundsFor (peer : Peer) (outbound : Bool) : Bounds :=
  if outbound then
    if (row peer.state).sendsExpected then Bounds.aPriori else peer.partner
  else peer.own

/-- The failure a header negotiation raises, with the reply the section mandates and
the close the diagram draws to END. -/
def headerRefusal (protocolId : Nat) (r : Refusal) : Except Refusal Refusal :=
  match ownHeader protocolId with
  | some header => .ok { r with place := some State.done, reply := [header.octets] }
  | none =>
    .error (refuse "unsupported" s!"the artifact states no version for {idName protocolId}")

/-- The header at the front of a buffer, or the negotiation's refusal: width, magic,
protocol id, version. -/
def readHeader (bytes : Octets) : Except Refusal Header :=
  if bytes.size < headerWidth then
    .error (refuse "truncated" s!"a protocol header is {headerWidth} octets and only \
      {bytes.size} are present")
  else if bytes.extract 0 4 != magic then
    .error (refuse "malformed" s!"these octets do not begin with the ASCII letters AMQP")
  else
    let protocolId := field bytes 4 1
    if !speaksId protocolId then
      .error (refuse "unsupported" s!"{idName protocolId} is not a protocol this peer \
        speaks")
    else
      let header : Header := ⟨protocolId, field bytes 5 1, field bytes 6 1, field bytes 7 1⟩
      match statedVersion protocolId with
      | some (a, b, c) =>
        if header.major == a && header.minor == b && header.revision == c then .ok header
        else
          .error (refuse "unsupported" s!"the header names {idName protocolId} version \
            {header.major}.{header.minor}.{header.revision}, and this peer speaks \
            {a}.{b}.{c}")
      | none =>
        .error (refuse "unsupported" s!"the artifact states no version for \
          {idName protocolId}")

/-- A refusal the frame layer raised: its reason class, and what it said after it. -/
def fromFrame (message : String) : Refusal :=
  let parts := message.splitOn ":"
  ⟨wireCondition, (parts.head?.getD "").trimAscii.toString,
   (String.intercalate ":" (parts.drop 1)).trimAscii.toString, none, []⟩

/-- A peer whose header exchange has completed in the SASL layer is in that layer's
dialogue, waiting for the server's mechanisms. -/
def inDialogue (peer : Peer) : Peer :=
  if peer.protocolId == saslId && peer.state == .bothHdr && peer.sasl == .idle then
    { peer with sasl := .wantsMechanisms }
  else peer

/-- One protocol header, offered or received. -/
def takeHeader (peer : Peer) (outbound : Bool) (header : Header) : Except Refusal Peer := do
  if !speaksId header.protocolId then
    .error (refuse "unsupported" s!"{idName header.protocolId} is not a protocol this \
      peer speaks")
  if outbound then
    if !(row peer.state).sendsHeader then
      .error (refuseWith stateCondition "illegalState" s!"{peer.state.label} may not send a protocol \
        header: the table's legal sends for that state are not HDR")
    -- The mirror of the receive-side mismatch check below: a peer that has already received a
    -- header has chosen this exchange's layer, so a header it sends must name that layer.
    -- Without it a peer could switch layers by *sending* a header instead of refusing one.
    -- The refusal moves nothing, as every refused send does, so this peer can still send the
    -- header of the layer the exchange is in; the receive side ends the connection because the
    -- unacceptable header has already crossed.
    if peer.state != .start && header.protocolId != peer.protocolId then
      .error (refuse "unsupported" s!"the header names {idName header.protocolId} while \
        this exchange is {idName peer.protocolId}: a peer does not send the header it would \
        refuse to receive")
    let next := if peer.state == .start then State.sndHdr else State.bothHdr
    return inDialogue { peer with state := next, protocolId := header.protocolId }
  else
    if !(row peer.state).receivesHeader then
      .error (refuseWith stateCondition "illegalState" s!"{peer.state.label} may not receive a protocol \
        header: its receive column excludes HDR")
    if peer.state != .start && header.protocolId != peer.protocolId then
      .error { refuse "unsupported" s!"the header names {idName header.protocolId} while \
        this exchange is {idName peer.protocolId}: the headers do not match, and both \
        peers close" with place := some .done }
    let next :=
      match peer.state with
      | .start => State.rcvHdr
      | .sndHdr => State.bothHdr
      | .pipeOpen => State.sndOpen
      | .pipeOc => State.pipeClose
      | other => other
    return inDialogue { peer with state := next, protocolId := header.protocolId }

/-- One SASL performative. -/
def takeSasl (peer : Peer) (outbound : Bool) (size : Nat) (body : Value) :
    Except Refusal Peer := do
  if size > minMaxFrameSize then
    .error (refuse "limit" s!"a SASL frame is at most {minMaxFrameSize} octets and this \
      one is {size}")
  let name := saslName body
  match peer.sasl with
  | .wantsMechanisms =>
    if name != "sasl-mechanisms" then
      .error (refuseWith stateCondition "illegalState" "the SASL dialogue is waiting for the partner's \
        sasl-mechanisms frame")
    refuseUnlessComplete "sasl-mechanisms" body
    let offered :=
      symbolList ((valueOfField "sasl-mechanisms" "sasl-server-mechanisms" body).getD .null)
    if offered.length == 0 then
      .error (refuseWith invalidFieldCondition "malformed" "a sasl-mechanisms frame \
        announces no mechanism, and the artifact states that the list cannot be null or \
        empty")
    let advanced := { peer with sasl := Sasl.wantsInit, offered := offered, announcedBy := some outbound }
    return advanced
  | .wantsInit =>
    if name != "sasl-init" then
      .error (refuseWith stateCondition "illegalState" "the SASL dialogue is waiting for the sasl-init \
        that chooses one of the mechanisms")
    -- Before the mechanism is read: an init that carries no `mechanism` at all is not an init
    -- that names an unoffered mechanism, and the two are different failures.
    refuseUnlessComplete "sasl-init" body
    let mechanism :=
      match valueOfField "sasl-init" "mechanism" body with
      | some (.symbol s) => s
      | _ => ""
    if peer.announcedBy == some outbound then
      .error (refuseWith stateCondition "illegalState" "the peer that announced the mechanisms is the SASL \
        server, and the init belongs to its partner")
    if !peer.offered.contains mechanism then
      .error (refuse "unsupported" s!"{mechanism} is not a mechanism the partner \
        announced: {peer.offered}")
    return { peer with sasl := .wantsOutcome }
  | .wantsOutcome =>
    -- the SASL Exchange picture gives each of these one direction: the server challenges
    -- and sends the outcome, the client responds
    let server := peer.announcedBy == some true
    if name == "sasl-challenge" then
      if outbound != server then
        .error (refuseWith stateCondition "illegalState" "the sasl-challenge is the SASL server's to send")
      refuseUnlessComplete "sasl-challenge" body
      return peer
    if name == "sasl-response" then
      if outbound == server then
        .error (refuseWith stateCondition "illegalState" "the sasl-response is the SASL client's to send")
      refuseUnlessComplete "sasl-response" body
      return peer
    if name != "sasl-outcome" then
      .error (refuseWith stateCondition "illegalState" "the SASL dialogue is waiting for the outcome")
    if outbound != server then
      .error (refuseWith stateCondition "illegalState" "the sasl-outcome is the SASL server's to send")
    refuseUnlessComplete "sasl-outcome" body
    let code ← integerField "sasl-outcome" "code" body
    if !(declaredCodeName code).isSome then
      .error (refuseWith invalidFieldCondition "malformed" s!"the sasl-outcome's code is \
        {code}, and the sasl-code choice declares {declaredCodeNames}")
    if code == successCode then
      -- The security layer is established, and the peers MUST exchange protocol headers
      -- again: for the AMQP layer, from the beginning.
      return Peer.new
    else
      -- "If the authentication is unsuccessful, this field is not set."
      if declaredFieldSet "sasl-outcome" "additional-data" body then
        .error (refuseWith invalidFieldCondition "malformed" s!"the sasl-outcome reports \
          {(declaredCodeName code).getD "an undeclared code"}, which is not a success, and \
          sets additional-data: the artifact states that the field is not set when the \
          authentication is unsuccessful")
      -- Authentication failed. The close-code the artifact names for this has no value in the
      -- choice table, so the refusal carries no condition — a condition picked because the
      -- table has a row of that shape would be one the artifact never named for a failed
      -- dialogue. The reason class is the code's own declared name, from the `sasl-code`
      -- choice: the four failures are four distinct values for four distinct causes, and
      -- reporting them all as "not ok" would read the field and keep only a boolean.
      Except.error (saslFailure ((declaredCodeName code).getD
        "a code the sasl-code choice does not declare")
        "the sasl-outcome reports that the SASL dialog did not succeed, and the security \
          layer is not established")
  | .idle =>
    .error (refuseWith stateCondition "illegalState" "the SASL layer's dialogue has not begun")

/-- The kind's name, for a diagnostic. -/
def kindName : Kind → String
  | .header => "protocol header"
  | .open => "open"
  | .close => "close"
  | .relayed => "relayed"
  | .saslFrame => "SASL"

/-- The peer a permitted frame leaves.

Only `open` and `close` move the state: everything else the dispatch table hands on, so
the connection's state does not change because a session frame passed. A row the
diagram draws no arrow for — an `open` received in HDR_RCVD — leaves the state and takes
the knowledge the frame carried, which is the rule the `*` rows need anyway. -/
def placed (peer : Peer) (outbound : Bool) (kind : Kind) (declared : Bounds) : Peer :=
  match kind with
  | .open =>
    if outbound then
      match peer.state with
      | .sndHdr => { peer with state := .pipeOpen, own := declared }
      | .bothHdr => { peer with state := .sndOpen, own := declared }
      | .rcvOpen => { peer with state := .open, own := declared }
      | _ => { peer with own := declared }
    else
      match peer.state with
      | .bothHdr => { peer with state := .rcvOpen, partner := declared }
      | .sndOpen => { peer with state := .open, partner := declared }
      | .pipeClose => { peer with state := .sndClose, partner := declared }
      | _ => { peer with partner := declared }
  | .close =>
    if outbound then
      match peer.state with
      | .sndOpen => { peer with state := .pipeClose }
      | .pipeOpen => { peer with state := .pipeOc }
      | .rcvClose => { peer with state := .done }
      | _ => { peer with state := .sndClose }
    else
      match peer.state with
      | .sndClose => { peer with state := .done }
      | .discard => { peer with state := .done }
      | _ => { peer with state := .rcvClose }
  | _ => peer

/-- One frame of the AMQP layer. -/
def takeFrame (peer : Peer) (outbound : Bool) (channel size : Nat) (body : Value) :
    Except Refusal Peer := do
  let kind := kindOfBody body
  if kind == .saslFrame then
    .error (refuseWith stateCondition "illegalState" "a SASL performative belongs to the SASL layer's \
      dialogue, and this is the AMQP layer's exchange")
  let allowed := if outbound then maySend peer.state kind else mayReceive peer.state kind
  if !allowed then
    .error (refuseWith stateCondition "illegalState" s!"{peer.state.label} does not admit a \
      {kindName kind} frame on the {if outbound then "send" else "receive"} side")
  if kind == .open && channel != 0 then
    .error (refuse "illegalState" s!"the open frame can only be sent on channel 0, and \
      this one is on channel {channel}")
  -- The declared surface's mandatory rule, for the two performatives this layer reads
  -- itself: a performative missing a field the generated table marks mandatory is not
  -- the performative its descriptor names, and the refusal leaves the peer where it
  -- stood, because nothing about the frame was accepted.
  let absent :=
    match kind with
    | .open => missingMandatory "open" body
    | .close => missingMandatory "close" body
    | _ => []
  if !absent.isEmpty then
    .error (refuseWith invalidFieldCondition "malformed"
      s!"the {kindName kind} performative does not carry {absent}, which the declared \
        surface marks mandatory")
  let bounds := boundsFor peer outbound
  if size > bounds.frames then
    .error (refuse "limit" s!"{size} octets exceeds the largest frame \
      {if outbound then "the partner accepts" else "this peer accepts"}, {bounds.frames}")
  if channel > bounds.channels then
    .error (refuse "limit" s!"channel {channel} is above the highest channel number \
      {bounds.channels} {if outbound then "the partner allows" else "this peer allows"}")
  let declared ← if kind == .open then openBounds body else pure Bounds.aPriori
  return placed peer outbound kind declared

/-- One item offered to the connection layer: a chosen frame, or octets that arrived,
which the state decides how to read. -/
inductive Offer where
  | header (header : Header)
  | /-- A frame to deliver: its decoded body, or `none` for the empty frame, which has
    no performative to answer. -/
    frame (channel : Nat) (octets : Octets) (body : Option Value)
  | arrives (octets : Octets)

/-- An empty frame, answered by the layer this peer is in and by the row the table gives its state.

The same eight octets mean two different things and the artifact says which. In the AMQP layer
an empty frame is the traffic a peer sends to keep a connection alive — "it MAY send an empty
frame, i.e., a frame consisting solely of a frame header, with no frame body" — so the peer is
left as it was.

That licence is the row's to give rather than the frame's to claim. An empty frame is a frame,
and a row's receive column is what admits one — `receivesAny` and nothing less. A row whose
receive column is blank admits no frame at all, and a row reading `receivesOpen` or
`receivesHeader` admits the open or the protocol header it names, which a frame with no body is
not: it carries no performative. So the row is asked before the peer is left as it was, with
the same `mayReceive` the frame step asks of a kind, and where the row admits no frame the
refusal is the one the table's existing refusals use — `amqp:illegal-state` with the class
`illegalState`, which is what the corpus's END refusals (`exchange-frame-in-end-refused`, whose
receive step is `refused_close_in_end`) pin for a frame arriving where the table admits none.

Once protocol id three has been negotiated the security section states the opposite rule about
the same frame: a SASL frame's body "MUST contain exactly one AMQP type, whose type encoding
MUST have provides=\"sasl-frame\"", and "receipt of an empty frame is an irrecoverable error".
So it is refused wherever in the dialogue it arrives, because the rule is about the frame and
not about the dialogue's position.

The SASL refusal is a wire-level one — the condition the artifact assigns to a frame whose
octets break its framing rules — and its class is the one the frame reader names when a body is
not a described performative, which is what an absent body is the limiting case of. It leaves
the peer at END: an error the section calls irrecoverable is not answered with an AMQP close,
and in this layer there is no established connection to close. -/
def emptyFrame (peer : Peer) : Except Refusal Peer :=
  if peer.protocolId == saslId then
    .error (refuse "malformed" "the SASL frame carries no body, and the security section \
      requires a SASL frame's body to hold exactly one AMQP type providing sasl-frame: an \
      empty frame is an irrecoverable error")
  else if !mayReceive peer.state .relayed then
    .error (refuseWith stateCondition "illegalState" s!"{peer.state.label} does not admit a \
      frame with no body: its receive column admits no frame")
  else .ok peer

/-- Apply one offer. A frame that arrives is read here, because whether the octets are a
header or a frame is what the state's receive column settles. -/
def apply (peer : Peer) (outbound : Bool) (offer : Offer) : Except Refusal Peer :=
  let step :=
    match offer with
    | .header header => takeHeader peer outbound header
    | .frame channel octets body =>
      match body with
      -- an empty frame: which layer it was offered to and which row the peer's state has
      -- decide its reading, since it is traffic in the AMQP layer only where the receive
      -- column admits a frame, and an irrecoverable error in the SASL one
      | none => emptyFrame peer
      | some body =>
        if peer.protocolId == saslId then takeSasl peer outbound octets.size body
        else takeFrame peer outbound channel octets.size body
    | .arrives octets =>
      if outbound then
        .error (refuse "illegalState" "a send carries a frame the encoder has already \
          written, not octets")
      else if (row peer.state).receivesHeader then
        match readHeader octets with
        | .ok header => takeHeader peer false header
        | .error r =>
          match headerRefusal peer.protocolId r with
          | .ok fixed => .error fixed
          | .error missing => .error missing
      else if looksLikeHeader octets then
        .error (refuse "illegalState" s!"a protocol header is not a frame of this layer, \
          and {peer.state.label}'s receive column excludes HDR")
      else
        match Ref.Frame.readFrame octets with
        | .error failure =>
          -- the class is the frame layer's own field, so this layer never recovers one by
          -- splitting prose: `fromFrame` still renders the text a caller sees, and the class
          -- travels beside it rather than out of it.
          .error { fromFrame failure.message with reasonClass := failure.reasonClass }
        | .ok (frame, used) =>
          match frame.body with
          -- the same input as the send route above, and the same rule: the layer, and the
          -- state's receive column inside the AMQP layer, decide
          | none => emptyFrame peer
          | some body =>
            if peer.protocolId == saslId then takeSasl peer false used body
            else takeFrame peer false frame.channel used body
  match step with
  | .ok next => .ok next
  | .error r => .error (placeRefusal peer outbound r)

end SpecAMQP.Ref.Connection
