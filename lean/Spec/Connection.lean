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

/-- The condition the artifact uses for data that could not be decoded: a value whose own
shape the declared surface does not admit.

It is the condition the message layer's declared-type refusals carry (`decodeRefusal`
there), and it is here for the same violation read at a different site: a `multiple` field
carried in a container Part 1 does not give it is a decoding failure wherever the field is
read, so the security layer refuses it under the same condition and the same class the
terminus path refuses it under rather than under a condition of its own. -/
def decodeError : String :=
  match (errorConditionsOf "amqp-error").find? (fun choice => choice.name == "decode-error") with
  | some choice => choice.value
  | none => "the amqp-error choice declares no decode-error"

/-- A refusal whose cause is the shape of a value rather than the wire or the moment. -/
def decodeRefusal (reasonClass prose : String) : Refusal :=
  ⟨decodeError, reasonClass, s!"{reasonClass}: {prose}", none, []⟩

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

/-- A `binary` value's payload: the one form whose payload is a byte string, and the form
a field declared `binary` (or a restriction of it, like `delivery-tag`) carries. -/
def valueOctets : Value → Option Octets
  | .binary payload => some payload
  | _ => none

/-- A `boolean` value's truth: the type's encoding is a single octet, false for the octet
zero and true for any other, which the layer's codec already reads that way. -/
def valueBool : Value → Option Bool
  | .boolean b => some b
  | _ => none

/-- A `multiple` field's symbols as the strings they are: a single symbol, or the elements of
an array.

This reads only the *elements* of whatever container it is handed, so it is not by itself a
reading of the field: the container's shape is the declaration's (`fieldShapeAdmitted`), and a
caller that skipped that check would admit a list, which Part 1 gives no `multiple` field. -/
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

/-- A boolean field's value, false when the field is absent.

A boolean field means *what it carries*: a field that is present and false is not the same
as a field that is not there, and the artifact names both states in one sentence —
`transfer/field:settled.6` requires the field to be "false (or unset)" — while its own
worked diagrams write `settled=False` on transfers and on dispositions rather than leaving
the field out. Reading presence where a clause reads a value collapses the two encodings
into one, and a rule that names both states becomes unenforceable: `settled.4` obliges a
sender under the «settled» negotiation to set the field true, which a presence reader
accepts a frame setting it false as satisfying. -/
def fieldBool (typeName fieldName : String) (body : Value) : Bool :=
  ((fieldValue typeName fieldName body).bind valueBool).getD false

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

/-- Whether a value found at a field's index is a shape the declaration admits: one element of
the declared primitive type, or — where the artifact marks the field `multiple` — an **array**
of them.

Part 1's types section gives a `multiple` field exactly those two shapes — its own worked
example encodes `book.authors` as the array constructor `0xE0` — which is the same sentence the
message layer's `multipleAccepts` reads for the terminus path. A *list* of values is neither of
them: it is what `symbolsOf` above takes its elements out of, and reading only the elements is
how a field comes to be "read" without its declaration ever being consulted.

The null that stands for an absent field is admitted here, so that a frame carrying one is
judged by the null-or-empty rule (`sasl-server-mechanisms.u1`) rather than refused as a shape. -/
def shapeAdmits (declared : String) (multiple : Bool) : Value → Bool
  | .null => true
  | .array _ items =>
    multiple && items.all (fun item => SpecAMQP.Spec.Codec.typeName item == declared)
  | value => SpecAMQP.Spec.Codec.typeName value == declared

/-- Whether a field's wire value is one the field's own declaration admits. The declaration's
`multiple` attribute and its declared type are read from the generated table, and the value is
then asked of `shapeAdmits`; an absent field is admitted here and left to the rules that speak
about absence. -/
def fieldShapeAdmitted (owner fieldName : String) (body : Value) : Bool :=
  match fieldOf owner fieldName with
  | none => true
  | some decl =>
    match primitiveOf decl.typeName with
    | none => true
    | some declared =>
      match fieldValue owner fieldName body with
      | none => true
      | some value => shapeAdmits declared decl.multiple value

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

/-- The declared surface's mandatory-field rule, for the five performatives this layer
reads itself: a SASL performative that does not carry a field the artifact marks
mandatory is not the performative its descriptor names, and the refusal is the one the
AMQP path already raises for `open` and `close` — the artifact's own `invalid-field`,
with the list read from the generated field table rather than written here.

The rule is enforced in the SASL layer for the same reason it is enforced in the AMQP
one, and its absence was observable: a `sasl-challenge` with no `challenge` and a
`sasl-response` with no `response` were taken as the performatives they name, a
`sasl-outcome` with no `code` silently became a failure, and a `sasl-init` with no
`mechanism` was refused as an *unoffered mechanism* under the wire-level condition — a
misattributed failure rather than a weaker check, and one both artefacts agreed on, so
no differential over them could see it.

Keyed by the performative's declared type name, which each arm knows before it calls
this: the arm's own moment guard has already refused every frame that is not the one
the dialogue is waiting for. -/
def refuseUnlessComplete (typeName : String) (body : Value) : Except Refusal Unit :=
  let absent := missingMandatory typeName body
  refuseUnless absent.isEmpty
    (fieldRefusal "malformed" s!"the {typeName} performative does not carry {absent}, \
      and the declared surface marks it mandatory")

/-- The refusal a failed SASL dialogue raises, as the peer that received the outcome reports
it.

Its condition is the **empty string**, and that is the reading rather than an omission: the
artifact obliges the peer to close the connection and names an "authentication-failure
close-code" that no value of the generated `connection-error` choice carries, so no protocol
condition exists for a failed authentication and none is invented. Choosing a declared row
because the table has one of that shape is how a specification acquires a condition the
artifact never named.

The reason class is the code's own declared name — `auth`, `sys`, `sys-perm` or `sys-temp`,
read out of the `sasl-code` choice by `saslCodeName` rather than written here — because the
four failures are four distinct values for four distinct causes and an outcome that reported
them all as "not ok" would have read the field and kept only a boolean. The place is END in
both directions: whichever peer learns of the failure has no dialogue left.

`SaslDialogue`'s contract states this as the law the four corpus vectors pin, and records
that the class vocabulary grew for this layer by exactly the values the artifact declares for
`sasl-code` and nothing else. -/
def saslFailure (reasonClass prose : String) : Refusal :=
  ⟨"", reasonClass, s!"{reasonClass}: {prose}", some .end, []⟩

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

/-- The dialogue's order as a number: nothing, then the announcement, then the init, then the
outcome.

Deliberately a rank *within* a layer rather than a rank of the layer's progress: a successful
outcome does not leave this endpoint past the dialogue — it resets it to `absent` on the AMQP
layer, where the peers exchange protocol headers again — so a rank that counted establishment as
"further along" would report the reset as the dialogue going backwards. `Proofs/SaslDialogue.lean`
proves the law that uses it: inside the SASL layer the rank never falls. -/
def SaslPhase.rank : SaslPhase → Nat
  | .absent => 0
  | .awaitingMechanisms => 1
  | .mechanismsKnown => 2
  | .awaitingOutcome => 3

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

/-- The name the `sasl-code` choice declares for an outcome code, or `none` for a value it
does not declare: the five values are read from the generated choice table rather than
written here, so a value the artifact added or moved would move this.

The four failure codes are distinct values for distinct causes — the artifact declares
them separately and labels each — so an outcome that reported them all as "not ok" would
have read the field and kept only a boolean. The `ok` name is the one the establishment
test reads, and the four others are what the artifact's own `sasl-code` choice carries. -/
def saslCodeName (code : Nat) : Option String :=
  match pathOf "sasl-code" with
  | none => none
  | some path =>
    (choices.find?
      (fun entry => entry.ownerPath == path && entry.value.toNat? == some code)).map
      (fun entry => entry.name)

/-- The names the `sasl-code` choice declares, in the table's order, for a diagnostic. -/
def saslCodeNames : List String :=
  match pathOf "sasl-code" with
  | none => []
  | some path =>
    (choices.filter (fun entry => entry.ownerPath == path)).map (fun entry => entry.name)

/-! ## The endpoint -/

/-- One endpoint's connection state: the table's state, the layer whose header exchange
is in progress, the SASL dialogue's position, the mechanisms announced, and the two
sides' limits — its own, which govern what it accepts, and the partner's, which govern
what it may send. Both start at the a priori limits. -/
structure Endpoint where
  state : State
  /-- The layer this exchange is in: AMQP, or SASL while a security layer is being
  established. A peer begins in the AMQP layer unless it offers SASL first, in which case the
  SASL layer precedes the connection; either layer is entered by a header whose protocol id
  names it. -/
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

/-- A peer that has exchanged nothing, at the layer it begins in: the AMQP layer, unless it offers
SASL first, in which case the SASL layer precedes the connection (Part 5) — which is the layer the
corpus's `AMQP\x03\x01\x00\x00` announces. Stated for a layer rather than for AMQP alone so that an
implementation's starting state can be *proved* against a specification state instead of assumed equal
to one. -/
def Endpoint.initialFor (layer : Layer) : Endpoint :=
  ⟨.start, layer, .absent, none, [], Limits.aPriori, Limits.aPriori⟩

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
    -- The mirror of the receive-side check below, and the reason it is not decoration: a peer
    -- that has already received a header has chosen the layer of this exchange, so a header it
    -- sends must name that layer. Without the check a peer could switch the layer by *sending*
    -- a header instead of refusing one — received SASL, then answered with an AMQP header — and
    -- land in the AMQP layer while its partner is in the SASL dialogue. Every exchange vector
    -- reached this arm from START, where either layer is free, so the asymmetry survived a
    -- corpus that tests the direction that works.
    --
    -- The refusal moves nothing: a refused send writes nothing and moves nothing, and this peer
    -- can still send the header of the layer the exchange is in. The receive-side refusal ends
    -- the connection because the unacceptable header has already crossed and there is nothing
    -- left to say; here nothing has crossed.
    if endpoint.state != .start then
      refuseUnless (layer == endpoint.layer)
        (refusal "unsupported" s!"the header names the {layer.name} layer while this \
          exchange is the {endpoint.layer.name} one, which is the table's header-mismatch \
          row: a peer does not send the header it would refuse to receive")
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

This function is reached only by a frame that carries a body: a bodyless frame is answered by the
dispatcher's `bodylessFrame`, which the security section makes an irrecoverable error in this layer,
so the "exactly one AMQP type" the frames clause requires is enforced before the dialogue is asked
anything here. The performative it is handed is the one the dispatcher decoded, whose descriptor the
frame layer has already checked provides `sasl-frame`.

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
    refuseUnlessComplete "sasl-mechanisms" body
    -- The field's own declaration before its elements: a `multiple` field is one element of its
    -- type or an array of them, and a list is neither, so a list is refused here as the message
    -- layer's terminus path refuses one. Reading the elements first is what admitted it before.
    refuseUnless (fieldShapeAdmitted "sasl-mechanisms" "sasl-server-mechanisms" body)
      (decodeRefusal "malformed"
        s!"sasl-mechanisms.sasl-server-mechanisms is declared a multiple symbol and the section carries a {SpecAMQP.Spec.Codec.typeName ((fieldValue "sasl-mechanisms" "sasl-server-mechanisms" body).getD .null)}")
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
    -- Before the mechanism is read: an init that carries no `mechanism` at all is not an init
    -- that names an unoffered mechanism, and the two are different failures. Read as the
    -- second, it was refused under the wire-level condition and told the peer its mechanism
    -- was unsupported when in fact it had sent none.
    refuseUnlessComplete "sasl-init" body
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
      refuseUnlessComplete "sasl-challenge" body
      return reporting endpoint
    if frame == .response then
      refuseUnless (outbound != server)
        (stateRefusal "illegalState" "the sasl-response is the SASL client's to send, and this \
          peer is not the client")
      refuseUnlessComplete "sasl-response" body
      return reporting endpoint
    refuseUnless (frame == .outcome)
      (stateRefusal "illegalState" "the SASL dialogue is waiting for the outcome of the \
        exchange the init began")
    refuseUnless (outbound == server)
      (stateRefusal "illegalState" "the sasl-outcome is the SASL server's to send, and this \
        peer is not the server")
    refuseUnlessComplete "sasl-outcome" body
    let code ← intField "sasl-outcome" "code" body
    -- The code must be one of the values the choice declares. `sasl-code` is an enumerated
    -- field, so a value outside its declared set is a field-value violation rather than an
    -- unsuccessful authentication: read as the second, an outcome carrying 9 was accepted and
    -- closed the connection, which told the peer its frame was well formed when its code was
    -- not a code the artifact defines.
    refuseUnless (saslCodeName code).isSome
      (fieldRefusal "malformed" s!"the sasl-outcome's code is {code}, and the sasl-code \
        choice declares {saslCodeNames}")
    if code == saslOk then
      -- The layer is established, and the peers MUST exchange protocol headers again:
      -- this time for the AMQP layer, from the beginning.
      let established :=
        { endpoint with state := .start, layer := .amqp, phase := .absent, role := none,
                        mechanisms := [], localLimits := Limits.aPriori,
                        remoteLimits := Limits.aPriori }
      -- Answering through `reporting`, as the mechanisms, init, challenge and response arms do:
      -- the octets an outbound frame is written with are the caller's, and an arm that dropped
      -- them would say this one performative puts nothing on the wire where the other four do.
      return reporting established
    else
      -- "If the authentication is unsuccessful, this field is not set." The rule is the
      -- artifact's and it is about this frame's own content, so a failure outcome that carries
      -- additional-data is refused the way every other field-value violation in this layer is.
      refuseUnless (!fieldSet "sasl-outcome" "additional-data" body)
        (fieldRefusal "malformed" s!"the sasl-outcome reports \
          {(saslCodeName code).getD "an undeclared code"}, which is not a success, and sets \
          additional-data: the artifact states that the field is not set when the \
          authentication is unsuccessful")
      -- Authentication did not succeed. The artifact obliges the peer to close the connection
      -- and names an "authentication-failure close-code" that no value of the generated
      -- `connection-error` choice carries, so the refusal's condition is empty: the artifact
      -- declares no condition for a failed dialogue, and picking a declared row because it
      -- exists would give this layer a condition the artifact never named.
      --
      -- What carries the information is the reason class: the code's own declared name, read
      -- from the `sasl-code` choice. The four failures are four distinct values for four
      -- distinct causes — a failed credential, a system error, a permanent one and a transient
      -- one — and an outcome that reported them all as "not ok" would have read the field and
      -- kept only a boolean. The place is END in both directions, because this peer has no
      -- dialogue left either way.
      Except.error (saslFailure ((saslCodeName code).getD
        "a code the sasl-code choice does not declare")
        "the sasl-outcome reports that the SASL dialog did not succeed, and the security \
          layer is not established")
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

/-- A frame with no body, answered by the layer it was offered to and by the table's column for the
direction it is offered in.

The two layers read the same empty frame differently, and the difference is the artifact's
rather than a convenience of this dispatcher.

In the AMQP layer an empty frame is traffic: "If a peer needs to satisfy the need to send
traffic to prevent idle timeout, and has nothing to send, it MAY send an empty frame, i.e., a
frame consisting solely of a frame header, with no frame body" — so the step is admitted and
the endpoint is left where it was, which is the reading `doc-idle-time-out.7` records for this
dispatcher and the one the corpus's `exchange-empty-frame-any-channel` pins.

That licence is the table's to give, and it is a *cell* rather than a shape — and a cell, like
every other frame's, belongs to a direction. An empty frame is still a frame, so the same column
the frame step asks is asked here, by the direction the frame is offered in: `permitsSend`'s
column for one the peer offers, `permitsReceive`'s for one that arrives, each with the role the
bodyless frame actually has (`.other`: a frame the connection relays without deciding). Where
that column admits a frame the idle-timeout reading stands; where it does not, the frame is
refused. Nor is the column asked only for its blank cell: a cell reading `OPEN` names the open
performative and a cell reading `HDR` names a protocol header, and a frame with no body is
neither — it carries no performative at all — so it is no more permitted in those states than in
a state whose column is `-`. Where the column does not admit it, the refusal is the one the
table's existing refusals use rather than one invented for this case:
`exchange-frame-in-end-refused` and its receive-side sibling `refused_close_in_end` pin that a
frame arriving in END — where both columns are `-` — is refused with `amqp:illegal-state` and the
class `illegalState`, and this is that same failure.

In the SASL layer the security section states the opposite rule about the same octets: "The
frame body of a SASL frame MUST contain exactly one AMQP type, whose type encoding MUST have
provides=\"sasl-frame\". Receipt of an empty frame is an irrecoverable error." A bodyless frame
is therefore refused in whatever phase it arrives, because the rule is about the frame rather
than about the dialogue's position.

The condition is this specification's condition for a wire-level failure, which is what a frame
whose body is not the performative its section requires is; the class is the frame layer's own
class for exactly that failure, because `readFrame` refuses a body that is not a described
performative the same way. The security artifact names no error condition at all — recorded in
`ledger/ambiguities/sasl-dialogue-condition.json` — so this is a reading of the layer's
existing convention rather than a transcription, and it is the convention every other frame the
SASL layer reads already uses. The place is END: the error is irrecoverable in the section's
own word, and in this layer no AMQP close can be written, because the layer is not
established.

Both routes of `step` answer through this function — the submission a peer offered, with
`outbound` true, and the frame `readFrame` decoded, with it false — so each route is asked of its
own column and neither can answer by the other's. -/
def bodylessFrame (endpoint : Endpoint) (outbound : Bool) : Except Refusal Outcome :=
  if endpoint.layer == Layer.sasl then
    .error (refusal "malformed" "the SASL frame carries no body, and the security section \
      requires a SASL frame's body to hold exactly one AMQP type providing sasl-frame: \
      receipt of an empty frame is an irrecoverable error")
  else if !(if outbound then permitsSend endpoint.state .other
            else permitsReceive endpoint.state .other) then
    .error (stateRefusal "illegalState" s!"{endpoint.state.name} does not permit a frame with \
      no body to be {if outbound then "sent" else "received"}: the table's legal \
      {if outbound then "sends" else "receives"} column is \
      {if outbound then endpoint.state.sendClass.name else endpoint.state.receiveClass.name}")
  else .ok ⟨endpoint, []⟩

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
      -- a bodyless frame reaches this path too, and which layer it was offered to, which
      -- direction it was offered in and which state it was offered in decide its reading:
      -- traffic in the AMQP layer where the table's column for that direction admits a frame,
      -- a refusal where it does not, and an irrecoverable error in the SASL one
      match body with
      | none => bodylessFrame endpoint outbound
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
              -- an empty frame carries no performative, and which layer received it and which
              -- state it arrived in decide what that means — "apart from this use, empty
              -- frames have no meaning" here, but only in a state whose receive column admits
              -- a frame; an irrecoverable error in the SASL layer — which is the reading the
              -- send route above applies to the same input, each by its own column
              match frame.body with
              | none => bodylessFrame endpoint false
              | some body =>
                if endpoint.layer == Layer.sasl then
                  stepSaslFrame endpoint false consumed body #[]
                else
                  stepAmqpFrame endpoint false frame.channel consumed body #[]
  match dispatched with
  | .ok outcome => .ok outcome
  | .error reason => .error (Refusal.withPlace endpoint outbound reason)

end SpecAMQP.Spec.Connection
