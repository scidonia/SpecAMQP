import Spec.Connection

/-!
# The session layer (Part 2: `amqp:transport/section:sessions`)

The session layer differs from the connection layer in the shape of its evidence: the
connection's state table is a picture with three columns, while the session's rules are
a *diagram* (picture 30, "State Transitions") plus seven state descriptions in prose
that say what each state may send and receive, and a set of clauses about the begin, the
end, the flows and the errors. The artifact carries no table for the session, so each
declaration here cites what it transcribed.

The declared surface — which fields a performative has, which are mandatory, what their
defaults are, and what condition an error names — is *not* duplicated here:
`Spec.Connection`'s declared-surface section reads the generated tables once, and both
layers use it, so a performative missing a mandatory field does not refuse differently
depending on which layer read it.

Scope, as the milestone fixes it: `begin`/`end`, `attach`/`detach`, `flow` and `transfer`
carrying one unfragmented `data` section. The *link* state machine is not here: `attach`'s
fields are read and their mandatory rules enforced, but nothing tracks a link's lifecycle,
its credit, its delivery numbers or its unsettled map. A `transfer`'s payload is opaque to
this layer, which is what the frame layer already says it is — "the remaining bytes in the
frame body form the payload for that frame", whose meaning "is defined by the semantics of
the given performative".

Two readings are worth stating before the code:

* **The state descriptions are the permission columns.** There is no table for the
  session, so `UNMAPPED` "cannot send or receive frames", `BEGIN_SENT` "MAY send frames
  but cannot receive them", `BEGIN_RCVD` "MAY receive frames, but cannot send them",
  `MAPPED` "MAY both send and receive", `END_SENT` "MAY receive frames, but cannot send
  them", `END_RCVD` "MAY send frames, but cannot receive them", and `DISCARDING` — "a
  variant of the END_SENT state" — receives what it then discards. Those sentences are
  `State.maySend` and `State.mayReceive`.
* **A session that cannot process input ends itself.** The section says it "MUST indicate
  this by issuing an END with an appropriate «error» indicating the cause of the problem",
  and "MUST then proceed to discard all incoming frames from the remote endpoint until
  receiving the remote endpoint's corresponding «end» frame" — which is the diagram's
  `MAPPED --S:END(error)--> DISCARDING` arrow. So a frame received in a session that
  cannot take it leaves the session in DISCARDING and the refusal carries the condition
  that END would name; where the state's own description says the endpoint cannot send at
  all, no END can be issued, so the state stands and the refusal says so.

A third reading is the interface's rather than this module's, recorded in
`ledger/ambiguities/channel-zero-layering.json`: dispatch is by channel, so a session
performative arriving on channel zero is answered by the *connection*'s rules and not by
this machine, and no vector exercises it.
-/

namespace SpecAMQP.Spec.Session

open SpecAMQP.Generated.Oasis (TypeDecl)
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Spec.Connection
  (choiceValue? fieldValue fieldSet framingError invalidField missingMandatory valueNat)

/-! ## The session state machine (picture 30, "State Transitions") -/

/-- The seven session states, in the artifact's own names. -/
inductive State where
  | unmapped
  | beginSent
  | beginRcvd
  | mapped
  | endSent
  | endRcvd
  | discarding
deriving Repr, BEq, DecidableEq

/-- Every state, in the order the artifact lists them. -/
def State.all : List State :=
  [.unmapped, .beginSent, .beginRcvd, .mapped, .endSent, .endRcvd, .discarding]

/-- The state's name, exactly as the artifact writes it. -/
def State.name : State → String
  | .unmapped => "UNMAPPED"
  | .beginSent => "BEGIN_SENT"
  | .beginRcvd => "BEGIN_RCVD"
  | .mapped => "MAPPED"
  | .endSent => "END_SENT"
  | .endRcvd => "END_RCVD"
  | .discarding => "DISCARDING"

/-- The state a name denotes, or `none` for a name the artifact does not have. -/
def State.ofName (name : String) : Option State :=
  State.all.find? (fun state => state.name == name)

/-- Whether the state's description lets the endpoint send frames: UNMAPPED cannot,
BEGIN_SENT may, BEGIN_RCVD cannot, MAPPED may, END_SENT cannot, END_RCVD may, and
DISCARDING — "a variant of the END_SENT state" — cannot. -/
def State.maySend : State → Bool
  | .unmapped => false
  | .beginSent => true
  | .beginRcvd => false
  | .mapped => true
  | .endSent => false
  | .endRcvd => true
  | .discarding => false

/-- Whether the state's description lets the endpoint receive frames. -/
def State.mayReceive : State → Bool
  | .unmapped => false
  | .beginSent => false
  | .beginRcvd => true
  | .mapped => true
  | .endSent => true
  | .endRcvd => false
  | .discarding => true

/-! ## The performatives this layer answers for -/

/-- The session performatives, by the declared type their descriptor names. `other` is
every performative a frame can carry that this layer does not answer for: the dispatch
table hands `open` and `close` to the connection endpoint, so a body this layer does not
know is a frame the session cannot process. -/
inductive Performative where
  | begin
  | end
  | attach
  | detach
  | flow
  | transfer
  | other
deriving Repr, BEq, DecidableEq

/-- The performative's name, for diagnostics. -/
def Performative.name : Performative → String
  | .begin => "begin"
  | .end => "end"
  | .attach => "attach"
  | .detach => "detach"
  | .flow => "flow"
  | .transfer => "transfer"
  | .other => "another performative"

/-- The performative a declared type names. -/
def performativeOfDeclared (declaration : TypeDecl) : Performative :=
  if declaration.name == "begin" then .begin
  else if declaration.name == "end" then .end
  else if declaration.name == "attach" then .attach
  else if declaration.name == "detach" then .detach
  else if declaration.name == "flow" then .flow
  else if declaration.name == "transfer" then .transfer
  else .other

/-- The performative a frame body is, from the declared type its descriptor names. -/
def Performative.ofBody (body : Value) : Performative :=
  match body with
  | .described descriptor _ =>
    match SpecAMQP.Spec.Frame.typeOfDescriptor descriptor with
    | some declaration => performativeOfDeclared declaration
    | none => .other
  | _ => .other

/-! ## Refusals -/

/-- A refusal the session layer raises: the condition the END it issues would name, the
class-led detail the corpus vocabulary reads, and the state the refusal leaves. -/
structure Refusal where
  condition : String
  detail : String
  /-- The state the refusal leaves the session in, or `none` where it leaves it alone. -/
  state : Option State
deriving Repr

/-- The condition an END carries when the session cannot process what it received: the
`amqp-error` family's `illegal-state`, the artifact's own symbol for a perfectly well
formed frame arriving at the wrong moment. A table that stopped declaring it yields a
condition that is not a protocol condition at all, which the corpus reports as a mismatch
rather than accepting. -/
def illegalStateCondition : String :=
  (choiceValue? "amqp-error" "illegal-state").getD "the amqp-error choice declares no illegal-state"

/-- The condition an END carries when it ends a session that cannot be reached at the
channel the frame arrived on. No session-error value means "no session is mapped here",
so this is the condition the register adopts for every wire-level failure. -/
def wireCondition : String := framingError

/-- The condition for a transfer that exceeds a window: the `session-error` family's
`window-violation`, which is the artifact's own symbol for exactly this, read from the
generated choice table. No clause raises it — the windows' definitions and the doc's
update paragraphs imply it — so the rule it names is a reading of those, and it is
reported as one. -/
def windowViolation : String :=
  (choiceValue? "session-error" "window-violation").getD "the session-error choice declares no window-violation"


/-- A refusal of a given class, which leaves the state alone. -/
def refusal (condition reasonClass prose : String) : Refusal :=
  ⟨condition, s!"{reasonClass}: {prose}", none⟩

/-- Refuse unless a condition holds. -/
def refuseUnless (condition : Bool) (reason : Refusal) : Except Refusal Unit :=
  if condition then .ok () else .error reason

/-! ## The session's flow-control state (doc `session-flow-control`) -/

/-- The id space the transfer numbers run in: a `transfer-number` is a `uint`, and
`next-outgoing-id` is "incremented after each successive «transfer» according to
RFC-1982 serial number arithmetic". -/
def serialModulus : Nat := 2 ^ 32

/-- The six variables the session's flow-control doc names, plus the value
`next-outgoing-id` had when this endpoint began: the `initial-outgoing-id` of the
artifact's second formula for `remote-incoming-window`.

`next-incoming-id` "identifies the expected transfer-id of the next incoming «transfer»
frame"; `incoming-window` "defines the maximum number of incoming «transfer» frames that
the endpoint can currently receive"; `next-outgoing-id` "is the transfer-id to assign to
the next transfer frame"; `outgoing-window` "defines the maximum number of outgoing
«transfer» frames that the endpoint can currently send"; `remote-incoming-window`
"reflects the maximum number of outgoing transfers that can be sent without exceeding the
remote endpoint's incoming-window"; `remote-outgoing-window` "reflects the maximum number
of incoming transfers that MAY arrive without exceeding the remote endpoint's
outgoing-window". -/
structure Windows where
  nextIncomingId : Nat
  incomingWindow : Nat
  nextOutgoingId : Nat
  outgoingWindow : Nat
  remoteIncomingWindow : Nat
  remoteOutgoingWindow : Nat
  initialOutgoingId : Nat
deriving Repr, BEq, DecidableEq

/-- The windows a session starts at when a corpus names a state without the begins that
would have set them: both peers' windows 1000 and both next ids 0, which is the arithmetic
baseline a `session:` start assumes and which every vector that cares about the numbers
sets for itself by running the begins. -/
def Windows.start : Windows :=
  ⟨0, 1000, 0, 1000, 1000, 1000, 0⟩

/-- The windows this endpoint's own begin sets: the field labels call them "the initial
incoming-window of the sender" and "the initial outgoing-window of the sender", and
`next-outgoing-id` is "the transfer-id of the first transfer id the sender will send". -/
def Windows.afterSendingBegin (windows : Windows) (nextOutgoing incoming outgoing : Nat) :
    Windows :=
  { windows with nextOutgoingId := nextOutgoing % serialModulus,
                 initialOutgoingId := nextOutgoing % serialModulus,
                 incomingWindow := incoming, outgoingWindow := outgoing }

/-- The windows the peer's begin sets. `next-incoming-id` becomes "the expected
transfer-id of the next incoming «transfer» frame", which is the id the partner will put
on its first transfer — the `next-outgoing-id` it announced — and the two remote windows
come from the same formula the doc gives for a received flow, with the unset branch taken:
`initial-outgoing-id + incoming-window - next-outgoing-id` for the peer's incoming window,
and its announced `outgoing-window` for its outgoing one. -/
def Windows.afterReceivingBegin (windows : Windows) (theirNextOutgoing theirIncoming
    theirOutgoing : Nat) : Windows :=
  { windows with nextIncomingId := theirNextOutgoing % serialModulus,
                 remoteIncomingWindow :=
                   (windows.initialOutgoingId + theirIncoming) % serialModulus -
                     windows.nextOutgoingId,
                 remoteOutgoingWindow := theirOutgoing }

/-- The windows a sent transfer leaves, per the doc's "sending a transfer": the endpoint
"will increment its next-outgoing-id, decrement its remote-incoming-window, and MAY
(depending on policy) decrement its outgoing-window". The policy is a parameter rather
than a silent choice, because the artifact leaves it open and a MAY that is compiled into
one branch is a decision nobody can see. -/
def Windows.afterSendingTransfer (windows : Windows) (policy : Bool) : Windows :=
  { windows with
      nextOutgoingId := (windows.nextOutgoingId + 1) % serialModulus,
      remoteIncomingWindow := windows.remoteIncomingWindow - 1,
      outgoingWindow := if policy then windows.outgoingWindow - 1 else windows.outgoingWindow }

/-- The windows a received transfer leaves, per the doc's "receiving a transfer": the
endpoint "will increment the next-incoming-id to match the implicit transfer-id of the
incoming transfer plus one, as well as decrementing the remote-outgoing-window, and MAY
(depending on policy) decrement its incoming-window". -/
def Windows.afterReceivingTransfer (windows : Windows) (transferId : Nat)
    (policy : Bool) : Windows :=
  { windows with
      nextIncomingId := (transferId + 1) % serialModulus,
      remoteOutgoingWindow := windows.remoteOutgoingWindow - 1,
      incomingWindow := if policy then windows.incomingWindow - 1 else windows.incomingWindow }

/-- The windows a received flow leaves: the doc says the endpoint "MUST update the
next-incoming-id directly from the next-outgoing-id of the frame, and ... the
remote-outgoing-window directly from the outgoing-window of the frame", and gives
`remote-incoming-window` as `next-incoming-id_flow + incoming-window_flow -
next-outgoing-id_endpoint`, or, "if the next-incoming-id field of the flow frame is not
set", as `initial-outgoing-id_endpoint + incoming-window_flow - next-outgoing-id_endpoint`.

The subtraction is over the id space the transfer numbers live in, so it wraps there
rather than going negative: a window is a count of transfers that may arrive, and an id
arithmetic that would make it negative is one the doc's RFC-1982 sentence already places
in that space. -/
def Windows.afterReceivingFlow (windows : Windows) (frameNextOutgoing frameIncoming
    frameOutgoing : Nat) (frameNextIncoming : Option Nat) : Windows :=
  let incomingId := frameNextIncoming.getD windows.initialOutgoingId
  { windows with
      nextIncomingId := frameNextOutgoing % serialModulus,
      remoteOutgoingWindow := frameOutgoing,
      -- a Nat subtraction here truncates at zero, which is the exhausted window rather
      -- than a wrapped one: the doc gives the formula and not what happens when the
      -- numbers leave no room, and an exhausted window fails the next send loudly rather
      -- than permitting it quietly
      remoteIncomingWindow :=
        (incomingId + frameIncoming) % serialModulus - windows.nextOutgoingId }

/-! ## The session endpoint -/

/-- One session endpoint: the state, the outgoing channel it is assigned to, the
incoming channel the partner's begin arrived on, whether the partner's begin has arrived
at all — which `flow`'s `next-incoming-id` rule turns on, and which the state alone
cannot say, since `END_RCVD` is reached from a session whose begin had arrived and which
no longer has an incoming channel — and the flow-control state the doc calls for. -/
structure Session where
  state : State
  /-- The channel this endpoint sends on, assigned by its own begin. -/
  outgoing : Option Nat
  /-- The channel the partner sends on, learned from the partner's begin. -/
  incoming : Option Nat
  /-- Whether the partner's begin has arrived. -/
  peerBegun : Bool
  /-- The session's flow-control state. -/
  windows : Windows
deriving Repr

/-- The policy the two MAY-decrements of the doc's update paragraphs are subject to.
Held as a value rather than compiled in, so the choice is visible: this is the reading the
corpus runs with, and the other branch is conforming too. -/
def startPolicy : Bool := true

/-- A session endpoint that has been created and has not begun. -/
def Session.initial : Session := ⟨.unmapped, none, none, false, Windows.start⟩

/-- The lowest channel number a session can be assigned: "it is RECOMMENDED that
implementations always assign the lowest available unused channel number", and channel
zero is the connection's under the register's reading, so this is one. -/
def startChannel : Nat := 1

/-- The session a state name starts at, with the channels its own description says it
has: "UNMAPPED ... is not mapped to any incoming or outgoing channels", `BEGIN_SENT` "is
assigned an outgoing channel number, but there is no entry in the incoming channel map",
`BEGIN_RCVD` "has an entry in the incoming channel map, but has not yet been assigned an
outgoing channel number", `MAPPED` "has both", `END_SENT` "has an entry in the incoming
channel map, but is no longer assigned an outgoing channel number", `END_RCVD` "is
assigned an outgoing channel number, but there is no entry in the incoming channel map",
and `DISCARDING` is "a variant of the END_SENT state". Whether the partner's begin has
arrived follows the same sentences: every state a begin had reached has one, and the two
that a begin has not — `UNMAPPED` and `BEGIN_SENT` — do not. -/
def Session.atState (state : State) : Session :=
  match state with
  | .unmapped => ⟨.unmapped, none, none, false, Windows.start⟩
  | .beginSent => ⟨.beginSent, some startChannel, none, false, Windows.start⟩
  | .beginRcvd => ⟨.beginRcvd, none, some startChannel, true, Windows.start⟩
  | .mapped => ⟨.mapped, some startChannel, some startChannel, true, Windows.start⟩
  | .endSent => ⟨.endSent, none, some startChannel, true, Windows.start⟩
  | .endRcvd => ⟨.endRcvd, some startChannel, none, true, Windows.start⟩
  | .discarding => ⟨.discarding, none, some startChannel, true, Windows.start⟩

/-! ## Applying a step -/

/-- A window field as a number: the fields the arithmetic reads are mandatory, so a
performative that reaches the arithmetic carries them, and a field that is not a number
reads as zero rather than aborting the step — the mandatory rule has already refused the
performatives that omit them. -/
def fieldNumber (typeName : String) (body : Value) (fieldName : String) : Nat :=
  ((fieldValue typeName fieldName body).bind valueNat).getD 0

/-- The session a begin frame leaves, with the channel rules the artifact states for the
frame that announces a session endpoint: the `remote-channel` field "MUST be empty for a
locally initiated session, and MUST be set when announcing the endpoint created as a
result of a remotely initiated session" — where it is "the channel on which the remote
session sent the begin". -/
def stepBegin (session : Session) (outbound : Bool) (channel : Nat) (body : Value) :
    Except Refusal Session := do
  if outbound then
    match session.state with
    | .unmapped =>
      refuseUnless (!fieldSet "begin" "remote-channel" body)
        (refusal invalidField "malformed"
          "a locally initiated begin MUST NOT set a remote-channel, and this one does")
      let windows :=
        session.windows.afterSendingBegin (fieldNumber "begin" body "next-outgoing-id")
          (fieldNumber "begin" body "incoming-window") (fieldNumber "begin" body "outgoing-window")
      return { session with state := .beginSent, outgoing := some channel, windows }
    | .beginRcvd =>
      match session.incoming, fieldValue "begin" "remote-channel" body with
      | some theirChannel, some value =>
        refuseUnless (valueNat value == some theirChannel)
          (refusal invalidField "malformed"
            s!"a begin answering a remotely initiated session MUST set the remote-channel \
              to the channel its begin arrived on, {theirChannel}")
        let windows :=
          session.windows.afterSendingBegin (fieldNumber "begin" body "next-outgoing-id")
            (fieldNumber "begin" body "incoming-window") (fieldNumber "begin" body "outgoing-window")
        return { session with state := .mapped, outgoing := some channel, windows }
      | _, _ =>
        .error (refusal invalidField "malformed"
          "a begin answering a remotely initiated session MUST set the remote-channel, \
            and this one leaves it empty")
    | other =>
      .error (refusal illegalStateCondition "illegalState"
        s!"a session sends one begin, and this one is already {other.name}")
  else
    match session.state with
    | .unmapped =>
      let windows := session.windows.afterReceivingBegin (fieldNumber "begin" body "next-outgoing-id")
        (fieldNumber "begin" body "incoming-window") (fieldNumber "begin" body "outgoing-window")
      return { session with state := .beginRcvd, incoming := some channel, peerBegun := true,
                            windows }
    | .beginSent =>
      let windows := session.windows.afterReceivingBegin (fieldNumber "begin" body "next-outgoing-id")
        (fieldNumber "begin" body "incoming-window") (fieldNumber "begin" body "outgoing-window")
      return { session with state := .mapped, incoming := some channel, peerBegun := true,
                            windows }
    | other =>
      .error (refusal illegalStateCondition "illegalState"
        s!"a session receives one begin, and this one is already {other.name}")

/-- The session an end frame leaves, following the diagram's arrows: a sent end goes to
END_SENT, or to DISCARDING when it carries an error; a received end goes to END_RCVD, and
to UNMAPPED where this endpoint had already sent its own. -/
def Session.afterEnd (session : Session) (outbound : Bool) (withError : Bool) : Session :=
  if outbound then
    match session.state with
    | .mapped =>
      { session with state := (if withError then .discarding else .endSent),
                     outgoing := none }
    | .endRcvd =>
      { session with state := .unmapped, outgoing := none, incoming := none,
                     peerBegun := false }
    | other => { session with state := other, outgoing := none }
  else
    match session.state with
    | .endSent | .discarding =>
      { session with state := .unmapped, outgoing := none, incoming := none,
                     peerBegun := false }
    | _ => { session with state := .endRcvd, incoming := none, peerBegun := true }

/-- One frame the session layer answers for.

The checks are the artifact's: the frame must be one this session's channel carries (the
connection maps incoming frames to sessions by channel, so a frame on another channel is
not this session's to process), its mandatory fields must be set, and the state's own
description must permit the direction. A receive the session cannot process is answered by
the END the section mandates where the state can send at all — which is DISCARDING — and a
send it cannot take is simply not taken, leaving the state where it was. -/
def step (session : Session) (outbound : Bool) (channel : Nat) (body : Value) :
    Except Refusal Session := do
  let performative := Performative.ofBody body
  let typeName :=
    match performative with
    | .begin => "begin" | .end => "end" | .attach => "attach" | .detach => "detach"
    | .flow => "flow" | .transfer => "transfer" | .other => ""
  -- "any incoming frames on the session MUST be silently discarded until the peer's end
  -- frame is received": in the error-triggered close of DISCARDING what arrives is
  -- discarded without being looked at, and only the peer's end is answered
  if !outbound && session.state == .discarding && performative != .end then
    return session
  -- the channel this session answers on: the two begins are what establish the mapping,
  -- so they are the frames that arrive and leave before it exists
  let mapped := if outbound then session.outgoing else session.incoming
  refuseUnless (performative == .begin || mapped == some channel)
    (refusal wireCondition "illegalState"
      s!"channel {channel} is not mapped to this session, whose \
        {if outbound then "outgoing" else "incoming"} channel is {mapped}")
  -- what the state's own description permits: every frame but the begin, whose rule is
  -- the diagram's arrows rather than the permission column, since a session that is
  -- UNMAPPED "cannot send or receive frames" and the begin is the frame that maps it
  let permitted :=
    performative == .begin ||
      (if outbound then session.state.maySend else session.state.mayReceive)
  let placed (condition reasonClass prose : String) : Refusal :=
    if outbound then refusal condition reasonClass prose
    else
      -- the section's answer to input it cannot process: an END with an error, which the
      -- diagram draws from MAPPED to DISCARDING, and which a state that cannot send at
      -- all cannot issue
      { refusal condition reasonClass prose with
          state := if session.state == .mapped then some State.discarding else none }
  refuseUnless permitted
    (placed illegalStateCondition "illegalState"
      s!"{session.state.name} does not permit this session to \
        {if outbound then "send" else "receive"} a {performative.name} frame")
  -- the mandatory fields the generated field table states
  refuseUnless ((missingMandatory typeName body).isEmpty)
    (placed invalidField "malformed"
      s!"the {typeName} performative does not carry {missingMandatory typeName body}, \
        and the declared surface marks it mandatory")
  match performative with
  | .begin => stepBegin session outbound channel body
  | .end => return session.afterEnd outbound (fieldSet "end" "error" body)
  | .flow =>
    -- "This value MUST be set if the peer has received the begin frame for the session,
    -- and MUST NOT be set if it has not."
    let set := fieldSet "flow" "next-incoming-id" body
    refuseUnless (set == session.peerBegun)
      (placed invalidField "malformed"
        s!"a flow's next-incoming-id must be set exactly when the partner's begin has \
          arrived, and it is {if set then "set" else "unset"} while the begin has \
          {if session.peerBegun then "" else "not "}arrived")
    if outbound then return session
    else
      -- "When the endpoint receives a «flow» frame from its peer, it MUST update the
      -- next-incoming-id directly from the next-outgoing-id of the frame, and it MUST
      -- update the remote-outgoing-window directly from the outgoing-window of the frame"
      let windows :=
        session.windows.afterReceivingFlow (fieldNumber "flow" body "next-outgoing-id")
          (fieldNumber "flow" body "incoming-window")
          (fieldNumber "flow" body "outgoing-window")
          ((fieldValue "flow" "next-incoming-id" body).bind valueNat)
      return { session with windows }
  | .transfer =>
    if outbound then do
      -- the two windows a sent transfer is charged against: ours, which "defines the
      -- maximum number of outgoing «transfer» frames that the endpoint can currently
      -- send", and the partner's, which our remote-incoming-window mirrors
      refuseUnless (session.windows.outgoingWindow > 0)
        (placed windowViolation "limit" "this session's outgoing window is exhausted, so           it may not send another transfer")
      refuseUnless (session.windows.remoteIncomingWindow > 0)
        (placed windowViolation "limit" "the partner's incoming window is exhausted, so           it can accept no further transfers")
      return { session with
                 windows := session.windows.afterSendingTransfer startPolicy }
    else do
      refuseUnless (session.windows.incomingWindow > 0)
        (placed windowViolation "limit" "this session's incoming window is exhausted, so           it cannot receive another transfer")
      -- "the implicit transfer-id of the incoming transfer": the id the partner assigned
      -- it, which is the one this session expected
      return { session with
                 windows := session.windows.afterReceivingTransfer
                   session.windows.nextIncomingId startPolicy }
  | .attach | .detach => return session
  | .other =>
    -- a performative the dispatch table gives a session and this slice does not model —
    -- a disposition, whose link is S4's — is carried rather than judged: the session's
    -- own state and channel rules still apply, and nothing here decides a link's moment
    return session

end SpecAMQP.Spec.Session
