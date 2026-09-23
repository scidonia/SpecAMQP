import Generated.Oasis.Choices
import Generated.Oasis.Constants
import Generated.Oasis.Fields
import Generated.Oasis.Types
import Spec.Frame

/-!
# The connection layer (Part 2: version negotiation, the connection lifecycle, SASL)

The connection lifecycle is the part of Part 2 whose tables are *pictures*: the
Connection State Table (picture 24) gives fourteen states with the frames each permits
to be sent, the frames each permits to be received, and the connection action that
follows; the Connection State Diagram (picture 23) gives the transitions between them;
the Frame Dispatch Table (picture 10) says which endpoint handles which frame; and the
Protocol Header Layout (picture 11, and picture 3 for SASL) gives the header's octets.
Nothing in `lean/Generated/` carries any of it, so the transcription here is the source
of truth rather than a copy of a generated table, and each declaration cites what it
transcribed.

Three readings are worth stating before the code, because they are decisions rather
than transcriptions:

* **The table's `*` and `**` are different columns and stay different.** `*` is any
  frame; `**` is any frame *known a priori to conform to the peer's capabilities and
  limitations*. The artifact says what those a priori limits are — "prior to any
  explicit negotiation, the maximum frame size is MIN-MAX-FRAME-SIZE and the maximum
  channel number is 0" — so a frame the partner's `open` will later permit is not
  thereby permitted before it arrives. Collapsing the two columns would lose the only
  place in the table where the peer's capabilities constrain what may be sent.
* **A refusal is the artifact's condition with the cause in the reason class.** The
  version-negotiation section requires a peer to close the connection for a header it
  cannot accept and names no condition for it; the ambiguity register adopts the one
  connection-error the artifact does use for wire-level failures, which is read from
  the generated choice table here, and the specific cause — octets that are not a
  header, a protocol id or version this peer does not speak, a frame in a state whose
  legal sends are `-` — is the leading token of the detail.
* **The security layer's dialogue sits on top of the header exchange, not beside it.**
  With protocol id three the header exchange is the table's own START/HDR_SENT/HDR_EXCH
  path; in HDR_EXCH with the SASL layer the security section's sequence applies (the
  server announces its mechanisms, the partner chooses one and initiates, the outcome
  closes the dialogue); and a successful outcome establishes the layer, after which the
  peers exchange protocol headers again — this time for the AMQP layer — and then open.

What this module deliberately does not do: it does not build the `close` frame a
refused frame obliges the peer to write (the state table records that the peer has
closed, and the refusal carries the condition that close would name), it does not
decide session-layer legality for the frames the dispatch table intercepts, and it does
not enforce the mandatory-field rule for the `open`'s fields (the frame layer's own
contract carries that).
-/

namespace SpecAMQP.Spec.Connection

open SpecAMQP.Generated.Oasis
  (ChoiceDecl FieldDecl TypeDecl choices constantValue? errorConditionsOf fieldsOf types)
open SpecAMQP.Harness (Octets toHex)
open SpecAMQP.Spec.Codec (Value)

/-! ## The protocol header -/

/-- The protocol id octet, the layout's fifth: which protocol the peers are
negotiating, before any version is compared. Zero is AMQP, two is TLS and three is
SASL. -/
inductive ProtocolId where
  | amqp
  | tls
  | sasl
deriving Repr, BEq, DecidableEq

/-- The octet a protocol id is written as. The three values are assigned by the
artifacts rather than by a table: the transport section states zero, the TLS section
two and the SASL section three. -/
def ProtocolId.code : ProtocolId → Nat
  | .amqp => 0
  | .tls => 2
  | .sasl => 3

/-- The protocol id's name, as the artifacts spell it. -/
def ProtocolId.name : ProtocolId → String
  | .amqp => "AMQP"
  | .tls => "TLS"
  | .sasl => "SASL"

/-- The protocol id an octet names, or `none` for one no artifact assigns. -/
def ProtocolId.ofCode (code : Nat) : Option ProtocolId :=
  if code = ProtocolId.amqp.code then some .amqp
  else if code = ProtocolId.tls.code then some .tls
  else if code = ProtocolId.sasl.code then some .sasl
  else none

/-- The version octets a protocol header carries. -/
structure Version where
  major : Nat
  minor : Nat
  revision : Nat
deriving Repr, BEq, DecidableEq

/-- A `<definition>` constant as a number, read by name: a revision of the artifact
that changes a version constant moves this layer rather than leaving it true by
accident. -/
def constantNat (name : String) : Option Nat :=
  (constantValue? name).bind (fun text => text.toNat?)

/-- Three named constants as a version, or `none` if the table does not carry them
all. -/
def versionOf (major minor revision : String) : Option Version :=
  match constantNat major, constantNat minor, constantNat revision with
  | some a, some b, some c => some ⟨a, b, c⟩
  | _, _, _ => none

/-- The layer a protocol id selects: the two this specification formalizes. TLS is a
protocol id the artifact assigns and this peer does not speak, so the layer is an
`Option` rather than a fourth constructor. -/
inductive Layer where
  | amqp
  | sasl
deriving Repr, BEq, DecidableEq

/-- The protocol id a layer's header carries. -/
def Layer.protocolId : Layer → ProtocolId
  | .amqp => .amqp
  | .sasl => .sasl

/-- The layer's name, as the artifacts spell it. -/
def Layer.name : Layer → String
  | .amqp => "AMQP"
  | .sasl => "SASL"

/-- The version the artifacts state for a layer: MAJOR/MINOR/REVISION for AMQP and
SASL-MAJOR/SASL-MINOR/SASL-REVISION for SASL, both read from the generated constant
table rather than typed. -/
def Layer.version : Layer → Option Version
  | .amqp => versionOf "MAJOR" "MINOR" "REVISION"
  | .sasl => versionOf "SASL-MAJOR" "SASL-MINOR" "SASL-REVISION"

/-- The layer a protocol id selects, or `none` for a protocol id this peer does not
speak. -/
def ProtocolId.layer? : ProtocolId → Option Layer
  | .amqp => some .amqp
  | .sasl => some .sasl
  | .tls => none

/-- The protocol header's fixed width: "In total this is an 8-octet sequence." -/
def headerOctets : Nat := 8

/-- The header's magic octets: the protocol header layout picture's four octets, the
upper case ASCII letters AMQP. -/
def magic : Octets := #[0x41, 0x4D, 0x51, 0x50]

/-- One octet of a header field, with the wrap made explicit: the layout gives each
version octet one octet, so a version that did not fit would be a transcription defect
rather than a value to truncate in silence. -/
def octet (n : Nat) : UInt8 := UInt8.ofNat (n % 256)

/-- A protocol header: the protocol id and the three version octets. -/
structure ProtocolHeader where
  protocolId : ProtocolId
  version : Version
deriving Repr, BEq, DecidableEq

/-- The header's octets, as the layout draws them. -/
def ProtocolHeader.octets (header : ProtocolHeader) : Octets :=
  magic ++ #[octet header.protocolId.code, octet header.version.major,
             octet header.version.minor, octet header.version.revision]

/-- A big-endian unsigned field of a buffer already known to hold it. -/
def beAt (bytes : Octets) (start width : Nat) : Nat :=
  (bytes.extract start (start + width)).foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- Whether a buffer begins the way a protocol header does. The connection layer asks
this only to tell a header apart from a frame in a state where a frame is what belongs;
a buffer that begins with the magic but is too short to be a header is left to the
decoder, which reports it as truncated. -/
def headerShaped (bytes : Octets) : Bool :=
  bytes.size ≥ 4 && bytes.extract 0 4 == magic

/-! ## The connection state table (picture 24) -/

/-- The table's fourteen states, in the table's own names. -/
inductive State where
  | start
  | hdrRcvd
  | hdrSent
  | hdrExch
  | openRcvd
  | openSent
  | openPipe
  | closePipe
  | ocPipe
  | opened
  | closeRcvd
  | closeSent
  | discarding
  | end
deriving Repr, BEq, DecidableEq

/-- Every state, in the table's order. -/
def State.all : List State :=
  [.start, .hdrRcvd, .hdrSent, .hdrExch, .openRcvd, .openSent, .openPipe, .closePipe,
   .ocPipe, .opened, .closeRcvd, .closeSent, .discarding, .end]

/-- The state's name, exactly as the table writes it. -/
def State.name : State → String
  | .start => "START"
  | .hdrRcvd => "HDR_RCVD"
  | .hdrSent => "HDR_SENT"
  | .hdrExch => "HDR_EXCH"
  | .openRcvd => "OPEN_RCVD"
  | .openSent => "OPEN_SENT"
  | .openPipe => "OPEN_PIPE"
  | .closePipe => "CLOSE_PIPE"
  | .ocPipe => "OC_PIPE"
  | .opened => "OPENED"
  | .closeRcvd => "CLOSE_RCVD"
  | .closeSent => "CLOSE_SENT"
  | .discarding => "DISCARDING"
  | .end => "END"

/-- The state a name denotes, or `none` for a name the table does not have. -/
def State.ofName (name : String) : Option State :=
  State.all.find? (fun state => state.name == name)

/-- The table's "Legal Sends" column. `conforming` is the `**` case — any frame known a
priori to conform to the peer's capabilities and limitations — and `anyFrame` the `*`
case, where any frame may be sent. They are not collapsed, because `**` is the only
column where the peer's capabilities constrain the send. -/
inductive SendClass where
  | nothing
  | header
  | open
  | anyFrame
  | conforming
deriving Repr, BEq, DecidableEq

/-- The table's "Legal Sends" column as the table writes it. -/
def SendClass.name : SendClass → String
  | .nothing => "-"
  | .header => "HDR"
  | .open => "OPEN"
  | .anyFrame => "*"
  | .conforming => "**"

/-- The table's "Legal Receives" column. -/
inductive ReceiveClass where
  | nothing
  | header
  | open
  | anyFrame
deriving Repr, BEq, DecidableEq

/-- The table's "Legal Receives" column as the table writes it. -/
def ReceiveClass.name : ReceiveClass → String
  | .nothing => "-"
  | .header => "HDR"
  | .open => "OPEN"
  | .anyFrame => "*"

/-- The table's "Legal Connection Actions" column. -/
inductive ConnAction where
  | closeWrite
  | closeRead
  | tcpClose
deriving Repr, BEq, DecidableEq

/-- The action's name, as the table writes it. -/
def ConnAction.name : ConnAction → String
  | .closeWrite => "TCP Close for Write"
  | .closeRead => "TCP Close for Read"
  | .tcpClose => "TCP Close"

/-- The table's "Legal Sends" column, row by row. -/
def State.sendClass : State → SendClass
  | .start => .header
  | .hdrRcvd => .header
  | .hdrSent => .open
  | .hdrExch => .open
  | .openRcvd => .open
  | .openSent => .conforming
  | .openPipe => .conforming
  | .closePipe => .nothing
  | .ocPipe => .nothing
  | .opened => .anyFrame
  | .closeRcvd => .anyFrame
  | .closeSent => .nothing
  | .discarding => .nothing
  | .end => .nothing

/-- The table's "Legal Receives" column, row by row. -/
def State.receiveClass : State → ReceiveClass
  | .start => .header
  | .hdrRcvd => .open
  | .hdrSent => .header
  | .hdrExch => .open
  | .openRcvd => .anyFrame
  | .openSent => .open
  | .openPipe => .header
  | .closePipe => .open
  | .ocPipe => .header
  | .opened => .anyFrame
  | .closeRcvd => .nothing
  | .closeSent => .anyFrame
  | .discarding => .anyFrame
  | .end => .nothing

/-- The table's "Legal Connection Actions" column, row by row: `none` is a row the
table leaves blank. -/
def State.action : State → Option ConnAction
  | .closePipe => some .closeWrite
  | .ocPipe => some .closeWrite
  | .closeRcvd => some .closeRead
  | .closeSent => some .closeWrite
  | .discarding => some .closeWrite
  | .end => some .tcpClose
  | _ => none

/-! ## Refusals -/

/-- A refusal the connection layer raises: the protocol condition, the reason class, the
detail — which leads with the reason class the corpus vocabulary names, `truncated`,
`malformed`, `unsupported`, `limit` or `illegalState` — the state the refusal leaves the
peer in where it moves it, and the octets the peer writes while refusing.

The class is a **field** rather than a token a reader recovers by splitting the detail: it
is the part of a refusal that is interface — the corpus compares classes between the
artefacts — and a class read back out of prose by `String.splitOn` is one no kernel proof can
reason about. The detail still leads with the class, so a caller and a vector see the strings
they always saw. -/
structure Refusal where
  condition : String
  /-- The reason class this refusal names, which is the token its detail leads with. -/
  reasonClass : String
  detail : String
  /-- The state the refusal leaves the peer in, or `none` where it leaves it alone. -/
  state : Option State
  /-- The octets the peer writes while refusing: the protocol header a failed
  negotiation is answered with. -/
  wrote : List Octets
deriving Repr

/-- The condition the artifact uses for a wire-level failure: the only connection-error
any clause in the pinned artifacts raises, read from the generated choice table rather
than typed. A table that stopped declaring it yields a condition that is not a protocol
condition at all, which the corpus reports as a mismatch rather than accepting. -/
def framingError : String :=
  match (errorConditionsOf "connection-error").find?
      (fun choice => choice.name == "framing-error") with
  | some choice => choice.value
  | none => "the connection-error choice declares no framing-error"

/-- The condition for a performative whose *fields* break a rule the declared surface
states — one the performative must carry and does not, or one whose value the type's own
documentation constrains: the `amqp-error` family's `invalid-field`, read from the
generated choice table.

This is the second condition the specification raises, and it is the artifact's own
symbol rather than an invention: a well-formed described type whose field is wrong is
exactly what `invalid-field` names, while `framing-error` names the wire-level failures
the connection's clauses raise. Both layers use it for the same rule, so a
performative missing a mandatory field does not refuse differently depending on which
layer read it. -/
def invalidField : String :=
  match (errorConditionsOf "amqp-error").find? (fun choice => choice.name == "invalid-field") with
  | some choice => choice.value
  | none => "the amqp-error choice declares no invalid-field"

/-- A refusal of a given class, which moves nothing and writes nothing. -/
def refusal (reasonClass prose : String) : Refusal :=
  ⟨framingError, reasonClass, s!"{reasonClass}: {prose}", none, []⟩

/-- A refusal whose cause is a field's value rather than the wire, carrying the
artifact's own `invalid-field` condition. -/
def fieldRefusal (reasonClass prose : String) : Refusal :=
  ⟨invalidField, reasonClass, s!"{reasonClass}: {prose}", none, []⟩

/-- The condition for a frame that is perfectly well formed and arrives in a state that
does not permit it: the `amqp-error` family's `illegal-state`, whose definition in the
artifact is exactly "The peer sent a frame that is not permitted in the current state".

It is deliberately not `framing-error`: that condition's definition is "A valid frame
header cannot be formed from the incoming byte stream", which is a different failure
about the octets rather than about the moment. A peer acts on which one it is told, so
conflating them tells it the wrong thing. The distinction is drawn where it applies: the
open's doc mandates `framing-error` for an oversized frame and for a channel number
outside the supported range, and those keep it. -/
def illegalState : String :=
  match (errorConditionsOf "amqp-error").find?
      (fun choice => choice.name == "illegal-state") with
  | some choice => choice.value
  | none => "the amqp-error choice declares no illegal-state"

/-- A refusal whose cause is the moment rather than the octets, carrying the artifact's
own `illegal-state` condition. -/
def stateRefusal (reasonClass prose : String) : Refusal :=
  ⟨illegalState, reasonClass, s!"{reasonClass}: {prose}", none, []⟩

/-- Refuse unless a condition holds: the guards below are all of this shape, and
spelling them out keeps each one's diagnostic at the check that raised it. -/
def refuseUnless (condition : Bool) (reason : Refusal) : Except Refusal Unit :=
  if condition then .ok () else .error reason

/-- The header a peer answers a failed negotiation with: its own, which names a protocol
id and a version it speaks — the section requires "a valid protocol header with a
supported protocol version" and, for a protocol id it cannot accept, one "with an
acceptable protocol id", and this peer's own layer is both. -/
def negotiationReply (layer : Layer) : Except Refusal ProtocolHeader :=
  match layer.version with
  | some version => .ok ⟨layer.protocolId, version⟩
  | none =>
    .error (refusal "unsupported" s!"the artifact states no version for the {layer.name} \
      layer, so there is no supported header to answer with")

/-- The refusal a failed header negotiation leaves, with the reply the section mandates
and the close the table draws to END. -/
def headerFailure (layer : Layer) (reason : Refusal) : Except Refusal Refusal := do
  let reply ← negotiationReply layer
  return { reason with state := some .end, wrote := [reply.octets] }

/-- The protocol header at the front of a buffer, or the refusal version negotiation
raises.

The checks are in the layout's order — width, magic, protocol id, version — so that a
buffer with too few octets is a `truncated`, a buffer that is not a header at all is a
`malformed`, and a header for a protocol id or a version this peer does not speak is an
`unsupported`. The three are different defects, and the register's reading is what
keeps them apart in the detail rather than in the condition. -/
def decodeHeader (bytes : Octets) : Except Refusal ProtocolHeader :=
  if bytes.size < headerOctets then
    .error (refusal "truncated" s!"a protocol header is {headerOctets} octets and the \
      buffer holds {bytes.size}")
  else if bytes.extract 0 4 != magic then
    .error (refusal "malformed" s!"the buffer begins {toHex (bytes.extract 0 4)}, and a \
      protocol header begins with the ASCII letters AMQP")
  else
    match ProtocolId.ofCode (beAt bytes 4 1) with
    | none =>
      .error (refusal "unsupported" s!"protocol id {beAt bytes 4 1} is not a protocol \
        id this peer speaks")
    | some protocolId =>
      match protocolId.layer? with
      | none =>
        .error (refusal "unsupported" s!"the {protocolId.name} layer's protocol id is \
          one this peer does not speak")
      | some layer =>
        let version : Version := ⟨beAt bytes 5 1, beAt bytes 6 1, beAt bytes 7 1⟩
        match layer.version with
        | some stated =>
          if version = stated then .ok ⟨protocolId, version⟩
          else
            .error (refusal "unsupported" s!"the header asks for {protocolId.name} \
              version {version.major}.{version.minor}.{version.revision}, and this peer \
              speaks {stated.major}.{stated.minor}.{stated.revision}")
        | none =>
          .error (refusal "unsupported" s!"the artifact states no version for the \
            {protocolId.name} layer")

/-! ## What a step submits -/

/-- What a frame is, as the connection layer's own rules distinguish it: `open` and
`close` are the connection-level performatives the dispatch table gives this endpoint,
a SASL performative belongs to the security layer's dialogue, and `other` is every
frame the connection relays without deciding (the dispatch table's `I`, which the
session layer answers for). -/
inductive FrameRole where
  | open
  | close
  | sasl
  | other
deriving Repr, BEq, DecidableEq

/-- The role's name, for diagnostics. -/
def FrameRole.name : FrameRole → String
  | .open => "open"
  | .close => "close"
  | .sasl => "SASL"
  | .other => "relayed"

/-- The role a frame body carries, decided by the declared type its descriptor names:
the generated type table is what says whether a descriptor names `open`, `close` or a
performative whose declared roles include `sasl-frame`. -/
def roleOfBody (body : Value) : FrameRole :=
  match body with
  | .described descriptor _ =>
    match SpecAMQP.Spec.Frame.typeOfDescriptor descriptor with
    | some declaration =>
      if declaration.name == "open" then .open
      else if declaration.name == "close" then .close
      else if declaration.provides.contains "sasl-frame" then .sasl
      else .other
    | none => .other
  | _ => .other

/-- One item offered to the connection layer.

A send carries the frame the peer chose — the corpus asks it to send one and the
encoder has already produced the octets — while a receive carries only octets: which of
them is a protocol header and which a frame is decided by the state the peer is in,
which is the connection layer's own question, so `.arriving` is decoded here rather
than by the caller. -/
inductive Submission where
  | header (header : ProtocolHeader)
  /-- A frame the peer is asked to send, or one that arrived: `body` is `none` for the
  empty frame of `idle-time-out.7`, which carries no performative and so nothing to
  dispatch. -/
  | frame (channel : Nat) (octets : Octets) (body : Option Value)
  | arriving (octets : Octets)

/-! ## The declared surface as this layer reads it -/

/-- The anchor path of a declared type, looked up by name so that no module outside
`lean/Generated` writes an `amqp:`-shaped symbol. -/
def pathOf (typeName : String) : Option String :=
  (types.find? (fun entry => entry.name == typeName)).map (fun entry => entry.path)

/-- A field of a declared type, by name. -/
def fieldOf (typeName fieldName : String) : Option FieldDecl :=
  match pathOf typeName with
  | none => none
  | some path => (fieldsOf path).find? (fun field => field.name == fieldName)

/-- The default a field declares, as a number: `defaultValue` is the artifact's raw
attribute text, which is where a `channel-max` of 65535 and a `max-frame-size` of
4294967295 stop being strings. -/
def fieldDefault (typeName fieldName : String) : Option Nat :=
  match fieldOf typeName fieldName with
  | some field => field.defaultValue.bind (fun text => text.toNat?)
  | none => none

/-- The declared value of a choice, looked up by the type that declares it and the
choice's name, so a code the artifact states — the SASL outcome's `ok`, say — is read
rather than typed. -/
def choiceValue? (typeName choiceName : String) : Option String :=
  match pathOf typeName with
  | none => none
  | some path =>
    (choices.find?
      (fun entry => entry.ownerPath == path && entry.name == choiceName)).map
      (fun entry => entry.value)

/-- A performative's field values, in the order the wire carried them. -/
def itemsOf (body : Value) : List Value :=
  match body with
  | .described _ (.list items) => items
  | _ => []

/-- The value one field of a performative holds, by the field table's own index: a list
that stops short of the declared fields means the fields it stops short of are null,
which is the trailing-null rule the type system states. -/
def fieldValue (typeName fieldName : String) (body : Value) : Option Value :=
  match fieldOf typeName fieldName with
  | some field =>
    if 1 ≤ field.index then (itemsOf body)[field.index - 1]? else none
  | none => none

/-- An integer value's number, whichever width the wire used for it. -/
def valueNat : Value → Option Nat
  | .ubyte n => some n
  | .ushort n => some n
  | .uint n => some n
  | .ulong n => some n
  | _ => none

/-- A `multiple` field's symbols as the strings they are: a single symbol is the wire
form of a one-element list, and the corpus's own frames are written that way. -/
def symbolsOf : Value → List String
  | .symbol text => [text]
  | .list items => items.filterMap (fun item =>
      match item with
      | .symbol text => some text
      | _ => none)
  | .array _ items => items.filterMap (fun item =>
      match item with
      | .symbol text => some text
      | _ => none)
  | _ => []

/-- Whether an integer field is set: present and not null. -/
def fieldSet (typeName fieldName : String) (body : Value) : Bool :=
  match fieldValue typeName fieldName body with
  | some .null | none => false
  | some _ => true

/-- The mandatory fields of a performative that it does not carry.

The rule is the artifact's: a field the declared surface marks `mandatory` is one the
performative must set, so a performative missing one is not the performative its
descriptor names. The list comes from the generated field table rather than from
memory, which is why every layer reads it here instead of writing its own — a field the
artifact makes mandatory cannot be missed by one layer and caught by another. -/
def missingMandatory (typeName : String) (body : Value) : List String :=
  match pathOf typeName with
  | none => []
  | some path =>
    (fieldsOf path).filterMap (fun field =>
      if field.mandatory && !fieldSet typeName field.name body then some field.name else none)

/-- The primitive a declared type resolves to, following a restricted type to its
source: `channel-max` is declared a `ushort` and `milliseconds` a `ulong`, and a field's
wire value must be of the declared type rather than of any type that happens to be a
number.

The walk is bounded, since a table that declared a cycle would otherwise not terminate;
a type the surface does not declare has no primitive, which is a refusal rather than a
default. -/
def primitiveOf (typeName : String) : Option String :=
  let rec follow (name : String) (fuel : Nat) : Option String :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match types.find? (fun entry => entry.name == name) with
      | none => none
      | some declaration =>
        match declaration.typeClass, declaration.source with
        | .restricted, some source => follow source fuel
        | _, _ => some declaration.name
  follow typeName 8

/-- The refusal a field earns when the wire carries a value of a type other than the one
the declared surface gives it, or `none` where the two agree or the field is unset.

This is the check `intField`'s own comment promises and did not make: `valueNat` reads a
number out of any integer width, so without this a `channel-max` declared a `ushort` and
sent as a `ulong` was installed rather than refused — the substitution that the declared
type exists to prevent. -/
def fieldTypeRefusal? (owner fieldName : String) (body : Value) : Option Refusal :=
  match fieldValue owner fieldName body with
  | none | some .null => none
  | some value =>
    match primitiveOf (match fieldOf owner fieldName with
                        | some field => field.typeName
                        | none => "") with
    | none => none
    | some declared =>
      if SpecAMQP.Spec.Codec.typeName value == declared then none
      else
        some (fieldRefusal "malformed" s!"the {owner}'s {fieldName} field is declared a \
          {declared} and this one is a {SpecAMQP.Spec.Codec.typeName value}")

/-- An integer field of a performative, taking the default the generated field table
states where the sender left it unset. A field that is present and is not an integer of
the type the artifact declares for it is refused rather than read as a number or as the
default: the declared type is part of the performative's meaning, and silently
substituting either is the shape of a defect that survives every vector. -/
def intField (owner fieldName : String) (body : Value) : Except Refusal Nat :=
  match fieldTypeRefusal? owner fieldName body with
  | some reason => .error reason
  | none =>
    match fieldValue owner fieldName body with
    | none | some .null =>
      match fieldDefault owner fieldName with
      | some number => .ok number
      | none =>
        .error (fieldRefusal "malformed" s!"the {owner}'s {fieldName} field is unset and \
          the declared surface gives it no default")
    | some value =>
      match valueNat value with
      | some number => .ok number
      | none =>
        .error (fieldRefusal "malformed" s!"the {owner}'s {fieldName} field is a \
          {SpecAMQP.Spec.Codec.typeName value}, and the artifact declares it an integer")

/-- The limits an `open` declares: the largest frame the sender accepts, and the
highest channel number it accepts. -/
structure Limits where
  maxFrameSize : Nat
  channelMax : Nat
deriving Repr, BEq, DecidableEq

/-- The largest frame both peers must accept, from the artifact's own constant. A table
that stopped carrying it would make this zero, and every frame would then be refused as
over the limit — loudly, in the corpus, rather than quietly admitted. -/
def minMaxFrameSize : Nat := (constantNat "MIN-MAX-FRAME-SIZE").getD 0

/-- The limits in force before any explicit negotiation: "Prior to any explicit
negotiation, the maximum frame size is MIN-MAX-FRAME-SIZE and the maximum channel
number is 0." These are the only limits either peer can be known to satisfy before the
partner's `open` arrives, which is what makes the table's `**` column checkable. -/
def Limits.aPriori : Limits := ⟨minMaxFrameSize, 0⟩

/-- The limits an `open` frame declares, from its own fields. -/
def openLimits (body : Value) : Except Refusal Limits := do
  let maxFrameSize ← intField "open" "max-frame-size" body
  let channelMax ← intField "open" "channel-max" body
  return ⟨maxFrameSize, channelMax⟩

/-! ## The SASL dialogue -/

/-- The SASL performatives the security section defines, by the declared type their
descriptor names. -/
inductive SaslFrame where
  | mechanisms
  | init
  | challenge
  | response
  | outcome
  | other
deriving Repr, BEq, DecidableEq

/-- The SASL performative a body is. -/
def SaslFrame.ofBody (body : Value) : SaslFrame :=
  match body with
  | .described descriptor _ =>
    match SpecAMQP.Spec.Frame.typeOfDescriptor descriptor with
    | some declaration =>
      if declaration.name == "sasl-mechanisms" then .mechanisms
      else if declaration.name == "sasl-init" then .init
      else if declaration.name == "sasl-challenge" then .challenge
      else if declaration.name == "sasl-response" then .response
      else if declaration.name == "sasl-outcome" then .outcome
      else .other
    | none => .other
  | _ => .other

/-- The SASL dialogue's position, as the security section orders it: the server
announces its mechanisms, the partner chooses one and initiates, the challenge and
response step may occur zero or more times, and the outcome closes the dialogue.

There are four positions because the section names four, and the established layer does not
have one: a successful outcome does not leave this endpoint *past* the dialogue, it resets it
to `absent` on the AMQP layer, where the peers exchange protocol headers again. -/
inductive SaslPhase where
  | absent
  | awaitingMechanisms
  | mechanismsKnown
  | awaitingOutcome
deriving Repr, BEq, DecidableEq

/-- The dialogue's position in prose. -/
def SaslPhase.name : SaslPhase → String
  | .absent => "not started"
  | .awaitingMechanisms => "waiting for the partner's mechanisms"
  | .mechanismsKnown => "waiting for the sasl-init"
  | .awaitingOutcome => "waiting for the outcome"

/-- Which end of the dialogue this peer is: the peer that announced the mechanisms is
the server, the one that initiates is the client, and the security section requires the
two to correspond to the TCP roles. -/
inductive SaslRole where
  | server
  | client
deriving Repr, BEq, DecidableEq

/-- The code a successful outcome carries, from the `sasl-code` choice table. -/
def saslOk : Option Nat :=
  (choiceValue? "sasl-code" "ok").bind (fun text => text.toNat?)

/-! ## The endpoint -/

/-- One endpoint's connection state: the table's state, the layer whose header exchange
is in progress, the SASL dialogue's position, the mechanisms announced, and the two
sides' limits — its own, which govern what it accepts, and the partner's, which govern
what it may send. Both start at the a priori limits. -/
structure Endpoint where
  state : State
  /-- The layer this exchange is in: AMQP, or SASL while a security layer is being
  established. A peer begins in the AMQP layer, and either layer is entered by a header
  that names it — the peer's own, or the one that arrives when this peer has not spoken
  yet. -/
  layer : Layer
  phase : SaslPhase
  role : Option SaslRole
  /-- The mechanisms a `sasl-mechanisms` frame announced, as the symbols it carried.
  A mechanism name is a symbol, so it is compared octet for octet: no clause anywhere
  makes mechanism names case-insensitive. -/
  mechanisms : List String
  /-- What this peer's own `open` declared: the frames and channels it accepts. -/
  localLimits : Limits
  /-- What the partner's `open` declared: the frames and channels this peer may use. -/
  remoteLimits : Limits
deriving Repr

/-- A peer that has exchanged nothing. -/
def Endpoint.initial : Endpoint :=
  ⟨.start, .amqp, .absent, none, [], Limits.aPriori, Limits.aPriori⟩

/-- What the connection layer did: the endpoint it is, and the octets it wrote. The
writes are the header it sends — its own, or the supported one the artifact obliges a
peer to answer an unparsable header with — and the frame a send writes. -/
structure Outcome where
  endpoint : Endpoint
  wrote : List Octets
deriving Repr

/-! ## The transition relation -/

/-- Where a refusal leaves the peer.

A refused send writes nothing and moves nothing. A refused receive is an error on the
wire: in the AMQP layer the peer answers it by sending a close, which is DISCARDING —
the table's variant of CLOSE_SENT "where the close is triggered by an error", whose
incoming frames "MUST be silently discarded until the peer's close frame is received" —
while in the SASL layer no AMQP close can be written, because the layer is not
established, so the transport is cut and the peer is at END. A refusal that already
says where it leaves the peer keeps that: a failed negotiation ends the connection with
its own row. -/
def Refusal.withPlace (endpoint : Endpoint) (outbound : Bool) (reason : Refusal) : Refusal :=
  match reason.state with
  | some _ => reason
  | none =>
    if outbound then reason
    else if endpoint.state == .end then
      -- END is the table's "it is illegal for either endpoint to write anything more
      -- onto the connection": a violation there has nothing left to close, so the end
      -- stands rather than the peer closing a connection it has already closed.
      { reason with state := some .end }
    else if endpoint.layer == Layer.sasl then { reason with state := some .end }
    else { reason with state := some .discarding }

/-- Whether the table's send column permits a role to be sent in a state.

A second `open` is not admitted by the `*` and `**` rows either, but that exclusion is
*not* a transcription: the artifact says the first frame in each direction contains an
`open`, which implies at most one without forbidding a second. The rule is the register's,
recorded with its scope in `ledger/ambiguities/second-open-refusal.json`, and it is cited
here so that a reader does not take it for something the table states. -/
def permitsSend (state : State) (role : FrameRole) : Bool :=
  match state.sendClass with
  | .nothing => false
  | .header => false
  | .open => role == .open
  | .anyFrame => role != .open
  | .conforming => role != .open

/-- Whether the table's receive column permits a role to be received in a state, on the
same terms as `permitsSend` and with the same citation for the second-`open` exclusion. -/
def permitsReceive (state : State) (role : FrameRole) : Bool :=
  match state.receiveClass with
  | .nothing => false
  | .header => false
  | .open => role == .open
  | .anyFrame => role != .open

/-- The endpoint a permitted frame leaves, and the limits it declared.

Only `open` and `close` move the state: every other frame is one the dispatch table
hands to another endpoint, and the connection state does not change because a session
frame passed. Where the diagram draws no arrow for a frame the table permits — an
`open` received in HDR_RCVD, the one row whose legal receives the diagram does not
reach — the state stays where it is and the knowledge the frame carried is kept, which
is the same rule the `*` rows need for the frames they relay.

A received `close` ends the connection where a close has already been sent (CLOSE_SENT
and its error-triggered variant DISCARDING), and otherwise puts the endpoint in
CLOSE_RCVD; a sent `close` ends it where the partner's close has already been received,
because a close is the last thing written. -/
def Endpoint.afterFrame (endpoint : Endpoint) (outbound : Bool) (role : FrameRole)
    (declared : Limits) : Endpoint :=
  match role with
  | .open =>
    if outbound then
      let state :=
        match endpoint.state with
        | .hdrSent => .openPipe
        | .hdrExch => .openSent
        | .openRcvd => .opened
        | other => other
      { endpoint with state, localLimits := declared }
    else
      let state :=
        match endpoint.state with
        | .hdrExch => .openRcvd
        | .openSent => .opened
        | .closePipe => .closeSent
        | other => other
      { endpoint with state, remoteLimits := declared }
  | .close =>
    if outbound then
      match endpoint.state with
      | .openSent => { endpoint with state := .closePipe }
      | .openPipe => { endpoint with state := .ocPipe }
      | .closeRcvd => { endpoint with state := .end }
      | _ => { endpoint with state := .closeSent }
    else
      match endpoint.state with
      | .closeSent | .discarding => { endpoint with state := .end }
      | _ => { endpoint with state := .closeRcvd }
  | _ => endpoint

/-- The limits a frame's size and channel are measured against: the partner's, for a
frame about to be sent, and this peer's own for a frame that arrived.

A send from a `**` state is measured against the a priori limits whatever else is
known, because that column admits only frames "known a priori to conform to the peer's
capabilities and limitations" — which is exactly the difference between it and `*`. -/
def limitsFor (endpoint : Endpoint) (outbound : Bool) : Limits :=
  if outbound then
    match endpoint.state.sendClass with
    | .conforming => Limits.aPriori
    | _ => endpoint.remoteLimits
  else endpoint.localLimits

/-- The endpoint after a header exchange: a SASL exchange that has exchanged both headers and
whose dialogue has not begun is in the security layer's dialogue, waiting for the server's
mechanisms.

Both conjuncts are load-bearing. The state says the headers are exchanged; the phase says the
dialogue has not begun, because a header exchange that happens after the mechanisms arrived must
not restart a dialogue — the mechanisms are announced once and the outcome is terminal, so
re-entering `awaitingMechanisms` would keep what the peer had learned and wait for it again. The
reference's guard is the dialogue's stage for the same reason, and its `.idle` arm is this
`absent` one. -/
def Endpoint.afterHeaderExchange (endpoint : Endpoint) : Endpoint :=
  match endpoint.layer with
  | .amqp => endpoint
  | .sasl =>
    if endpoint.state == .hdrExch && endpoint.phase == .absent then
      { endpoint with phase := .awaitingMechanisms }
    else endpoint

/-! ## Applying a step -/

/-- A protocol header offered to or arriving at the connection layer.

The header a peer sends chooses its own protocol id, and that is what fixes the layer
for the exchange. A header that arrives in START does the same, because a server may
wait for the partner's header before sending its own, so nothing has been chosen yet; a
header that arrives after this peer has sent one must name the layer this exchange is
already in, or it is the table's `R:HDR[!=S:HDR]` row — a header this peer cannot
accept, which ends the connection rather than being read as the other layer's. -/
def stepHeader (endpoint : Endpoint) (outbound : Bool) (header : ProtocolHeader) :
    Except Refusal Outcome := do
  let layer ←
    match header.protocolId.layer? with
    | some layer => pure layer
    | none =>
      .error (refusal "unsupported" s!"the {header.protocolId.name} layer's protocol \
        id is one this peer does not speak")
  if outbound then
    refuseUnless (endpoint.state.sendClass == .header)
      (stateRefusal "illegalState" s!"{endpoint.state.name}'s legal sends are the table's \
        {endpoint.state.sendClass.name} column, and a protocol header is what HDR names")
    let state := if endpoint.state == .start then .hdrSent else .hdrExch
    let endpoint := Endpoint.afterHeaderExchange { endpoint with state, layer }
    return ⟨endpoint, [header.octets]⟩
  else
    refuseUnless (endpoint.state.receiveClass == .header)
      (stateRefusal "illegalState" s!"{endpoint.state.name}'s legal receives are the table's \
        {endpoint.state.receiveClass.name} column, and a protocol header is what HDR \
        names")
    if endpoint.state != .start then
      refuseUnless (layer == endpoint.layer)
        { refusal "unsupported" s!"the header asks for the {layer.name} layer while this \
            exchange is the {endpoint.layer.name} one, which is the table's \
            header-mismatch row, whose arrow ends the connection" with
          state := some .end }
    let state :=
      match endpoint.state with
      | .start => .hdrRcvd
      | .hdrSent => .hdrExch
      | .openPipe => .openSent
      | .ocPipe => .closePipe
      | other => other
    let endpoint := Endpoint.afterHeaderExchange { endpoint with state, layer }
    return ⟨endpoint, []⟩

/-- One SASL performative, applied to the security layer's dialogue.

The dialogue is ordered by the security section and not by the connection state table:
the server announces its mechanisms, the partner chooses one and initiates, the
challenge and response step may occur zero or more times, and the outcome closes the
dialogue. Where the section names no condition for a failure — a mechanism the
receiving peer does not support is to be closed with an "authentication-failure
close-code" that no value of the generated `connection-error` choice carries — the
refusal uses the condition the artifact does use for wire-level failures and says what
was unsupported in its class, rather than inventing a code the standard does not
define. -/
def stepSaslFrame (endpoint : Endpoint) (outbound : Bool) (size : Nat) (body : Value)
    (wrote : Octets) : Except Refusal Outcome := do
  refuseUnless (size ≤ minMaxFrameSize)
    (refusal "limit" s!"a SASL frame's maximum size is MIN-MAX-FRAME-SIZE, \
      {minMaxFrameSize} octets, and this one is {size}")
  let frame := SaslFrame.ofBody body
  let reporting (endpoint : Endpoint) : Outcome :=
    ⟨endpoint, if outbound then [wrote] else []⟩
  match endpoint.phase with
  | .awaitingMechanisms =>
    refuseUnless (frame == .mechanisms)
      (stateRefusal "illegalState" "the SASL dialogue is waiting for the partner's \
        sasl-mechanisms frame")
    let announced :=
      symbolsOf (fieldValue "sasl-mechanisms" "sasl-server-mechanisms" body |>.getD .null)
    refuseUnless (!announced.isEmpty)
      (fieldRefusal "malformed" "a sasl-mechanisms frame announces no mechanism, and the \
        artifact states that the list cannot be null or empty")
    let role := if outbound then some SaslRole.server else some SaslRole.client
    let endpoint :=
      { endpoint with phase := .mechanismsKnown, mechanisms := announced, role }
    return reporting endpoint
  | .mechanismsKnown =>
    refuseUnless (frame == .init)
      (stateRefusal "illegalState" "the SASL dialogue knows the partner's mechanisms and is \
        waiting for the sasl-init that chooses one")
    let mechanism :=
      match fieldValue "sasl-init" "mechanism" body with
      | some (.symbol text) => text
      | _ => ""
    refuseUnless (!((outbound && endpoint.role == some SaslRole.server) ||
        (!outbound && endpoint.role == some SaslRole.client)))
      (stateRefusal "illegalState" "the peer that announced the mechanisms is the SASL \
        server, and the security section gives the init to its partner")
    refuseUnless (endpoint.mechanisms.contains mechanism)
      (refusal "unsupported" s!"the mechanism {mechanism} is not one the partner \
        announced: {endpoint.mechanisms}")
    return reporting { endpoint with phase := .awaitingOutcome }
  | .awaitingOutcome =>
    -- The SASL Exchange picture gives each of the remaining performatives one direction:
    -- the server challenges and the client responds — a step that "can occur zero or more
    -- times depending on the details of the SASL mechanism chosen" — and the server sends
    -- the outcome. Only `sasl-init` was checked against its direction before, so a peer
    -- playing the client could challenge, which the picture does not admit.
    let server := endpoint.role == some SaslRole.server
    if frame == .challenge then
      refuseUnless (outbound == server)
        (stateRefusal "illegalState" "the sasl-challenge is the SASL server's to send, and \
          this peer is not the server")
      return reporting endpoint
    if frame == .response then
      refuseUnless (outbound != server)
        (stateRefusal "illegalState" "the sasl-response is the SASL client's to send, and this \
          peer is not the client")
      return reporting endpoint
    refuseUnless (frame == .outcome)
      (stateRefusal "illegalState" "the SASL dialogue is waiting for the outcome of the \
        exchange the init began")
    refuseUnless (outbound == server)
      (stateRefusal "illegalState" "the sasl-outcome is the SASL server's to send, and this \
        peer is not the server")
    let code := (fieldValue "sasl-outcome" "code" body).bind valueNat
    if code == saslOk then
      -- The layer is established, and the peers MUST exchange protocol headers again:
      -- this time for the AMQP layer, from the beginning.
      let established :=
        { endpoint with state := .start, layer := .amqp, phase := .absent, role := none,
                        mechanisms := [], localLimits := Limits.aPriori,
                        remoteLimits := Limits.aPriori }
      return ⟨established, []⟩
    else
      -- Authentication did not succeed. The artifact obliges the peer to close the
      -- connection and names a close-code for it that the choice table does not define,
      -- so the close is recorded as the state it leaves and no condition is invented.
      return ⟨{ endpoint with state := .end }, []⟩
  | .absent =>
    .error (stateRefusal "illegalState" s!"the SASL layer is not in a place for a SASL \
      performative: the dialogue is {endpoint.phase.name}")

/-- One AMQP-layer frame, applied to the state table.

The order of the checks is the artifact's: the layer decides whether this is even a
frame of this exchange, the table's column decides whether the moment permits it, the
`open`'s own rule decides the channel, and the limits in force decide the size. -/
def stepAmqpFrame (endpoint : Endpoint) (outbound : Bool) (channel size : Nat)
    (body : Value) (wrote : Octets) : Except Refusal Outcome := do
  let role := roleOfBody body
  refuseUnless (role != .sasl)
    (stateRefusal "illegalState" "a SASL performative belongs to the SASL layer's dialogue, \
      and this exchange is the AMQP layer's until protocol id three is negotiated")
  let column :=
    if outbound then endpoint.state.sendClass.name else endpoint.state.receiveClass.name
  refuseUnless (if outbound then permitsSend endpoint.state role
                else permitsReceive endpoint.state role)
    (stateRefusal "illegalState" s!"{endpoint.state.name} does not permit a {role.name} frame \
      to be {if outbound then "sent" else "received"}: the table's legal \
      {if outbound then "sends" else "receives"} column is {column}")
  refuseUnless (role != .open || channel == 0)
    (refusal "illegalState" s!"the open frame can only be sent on channel 0, and this \
      one is on channel {channel}")
  let absent :=
    match role with
    | .open => missingMandatory "open" body
    | .close => missingMandatory "close" body
    | _ => []
  refuseUnless absent.isEmpty
    (fieldRefusal "malformed" s!"the {role.name} performative does not carry {absent}, \
      and the declared surface marks it mandatory")
  let limits := limitsFor endpoint outbound
  refuseUnless (size ≤ limits.maxFrameSize)
    (refusal "limit" s!"the frame is {size} octets and the largest \
      {if outbound then "the partner accepts" else "this peer accepts"} is \
      {limits.maxFrameSize}")
  refuseUnless (channel ≤ limits.channelMax)
    (refusal "limit" s!"channel {channel} is above the highest channel number \
      {limits.channelMax} {if outbound then "the partner permits" else "this peer permits"}")
  let declared ← if role == .open then openLimits body else pure Limits.aPriori
  let endpoint := endpoint.afterFrame outbound role declared
  return ⟨endpoint, if outbound then [wrote] else []⟩

/-- Apply one submission to the connection layer, and place the refusal it raises.

A frame that arrives is decoded here rather than by the caller, because which of the
octets is a header and which a frame is the state's own question: the receive column is
what says which is due, and a protocol header offered where a frame belongs is a step
the moment does not permit rather than a frame to be misread. A failed negotiation is
answered with the header the section mandates and the close the table draws to END. -/
def step (endpoint : Endpoint) (outbound : Bool) (submission : Submission) :
    Except Refusal Outcome :=
  let dispatched :=
    match submission with
    | .header header => stepHeader endpoint outbound header
    | .frame channel octets body =>
      -- a bodyless frame reaches this path too, and the clause's reading is the same one
      -- the receive seam applies: nothing to dispatch, so the endpoint is unchanged
      match body with
      | none => .ok ⟨endpoint, []⟩
      | some body =>
        if endpoint.layer == Layer.sasl then
          stepSaslFrame endpoint outbound octets.size body octets
        else
          stepAmqpFrame endpoint outbound channel octets.size body octets
    | .arriving octets =>
      if outbound then
        .error (refusal "illegalState" "a send carries the frame the peer chose, which \
          the encoder has already written; octets are what arrives")
      else
        match endpoint.state.receiveClass with
        | .header =>
          match decodeHeader octets with
          | .ok header => stepHeader endpoint false header
          | .error reason =>
            match headerFailure endpoint.layer reason with
            | .ok reply => .error reply
            | .error missing => .error missing
        | _ =>
          if headerShaped octets then
            .error (refusal "illegalState" s!"a protocol header is not a frame of this \
              layer, and {endpoint.state.name}'s legal receives are the table's \
              {endpoint.state.receiveClass.name} column")
          else
            match SpecAMQP.Spec.Frame.readFrame octets with
            | .error refusal =>
              -- the class is the frame layer's own field: the frame layer's instance is where
              -- the two artefacts' classes are related, and this layer passes the refusal on
              -- under the condition a wire-level failure carries. The detail is the frame
              -- layer's message, which is what a caller has always been shown here.
              .error ⟨framingError, refusal.reasonClass, refusal.message, none, []⟩
            | .ok (frame, consumed) =>
              -- an empty frame carries no performative — "apart from this use, empty frames
              -- have no meaning" — so the endpoint is left as it was and nothing is
              -- written, which is what the reference layer does for the same input
              match frame.body with
              | none => .ok ⟨endpoint, []⟩
              | some body =>
                if endpoint.layer == Layer.sasl then
                  stepSaslFrame endpoint false consumed body #[]
                else
                  stepAmqpFrame endpoint false frame.channel consumed body #[]
  match dispatched with
  | .ok outcome => .ok outcome
  | .error reason => .error (Refusal.withPlace endpoint outbound reason)

end SpecAMQP.Spec.Connection
