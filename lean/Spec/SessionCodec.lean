import Harness.Runner
import Spec.ConnectionCodec
import Spec.FrameCodec
import Spec.Protocol
import Spec.Session

/-!
# The specification's exchange layer as a corpus codec: connection and session

An exchange spans two machines: the connection's, whose state table is a picture with
three columns, and the session's, whose rules are a diagram plus seven prose state
descriptions. They are answered by one codec because the layers are not independent — the
session's moment depends on the connection's, and a frame's layer follows from what it
carries rather than from a field the vector could set.

The dispatch, which is the interface's reading and is recorded in
`ledger/ambiguities/channel-zero-layering.json`:

* a protocol header is the connection's;
* a frame carrying `open` or `close` is the connection's, whatever channel it is on —
  the dispatch table gives those two to the connection endpoint, and `close` may be
  received on any channel up to the channel maximum;
* a frame carrying anything else belongs to the session on the channel it carries, so it
  is handed to the connection first — which decides whether the connection can carry it
  at all: its state's column, the channel maximum and the frame size — and then to the
  session, which decides whether the moment is legal;
* a frame on channel zero is the connection's, and a *session* performative arriving
  there is refused rather than treated as a session step, because the connection has no
  session to delegate it to.

One consequence is worth stating because it looks like a broken convention and is not:
when the connection refuses a frame that a session was going to answer — the frame is
over the channel maximum, or arrives in a connection state whose column forbids it — the
refusal is the connection's and the state it leaves is the connection's, so that step
reports a `connection:` name even though the frame is on a session's channel. The state
name says which machine answered, which is the only thing it can honestly say; the
session's state did not move.

The state a `session:` start names is the session's, and the connection is taken to be
`OPENED` as if both `open`s had been exchanged with their fields unset: that is the
interface the milestone fixes, so a session vector need not replay the connection
handshake, and a frame on any channel from 1 to 65535 is admissible.
-/

namespace SpecAMQP.Spec.SessionCodec

open Lean
open SpecAMQP.Harness
open SpecAMQP.Spec.Connection (Endpoint Limits State framingError)
open SpecAMQP.Spec.FrameCodec (frameOfJson)
open SpecAMQP.Spec.Session (Session Performative)
open SpecAMQP.Spec (WidenedSession)

/-- One peer in an exchange: the connection endpoint, and the widened session endpoint the session
layer's rules are about. The session is the widened one — a registry of named links, each with two
endpoint-local handle spaces and one shared unsettled history — whose session-scope state is the
restricted reading's. `Spec.Protocol.step` is what answers for it. -/
structure Peer where
  connection : Endpoint
  session : WidenedSession

/-- The limits an `open` whose fields are unset declares, read from the generated field
table: what a `session:` start assumes the two peers exchanged. -/
def declaredLimits : Limits :=
  { maxFrameSize := (SpecAMQP.Spec.Connection.fieldDefault "open" "max-frame-size").getD 0,
    channelMax := (SpecAMQP.Spec.Connection.fieldDefault "open" "channel-max").getD 0 }

/-- The connection endpoint a `session:` start implies: both peers' `open`s exchanged
with their fields unset, which is `OPENED` with the declared limits on both sides. -/
def establishedConnection : Endpoint :=
  { Endpoint.initial with state := State.opened, localLimits := declaredLimits, remoteLimits := declaredLimits }

/-- Which machine answers for a step. -/
inductive Target where
  | connection
  /-- A frame a session answers for, with the channel it carries, its performative, and
  the payload after that performative. The payload is the frame's opaque remainder and only
  a session with a transaction layer reads it; it is carried here because the codec is
  where the frame is read. -/
  | session (channel : Nat) (body : SpecAMQP.Spec.Codec.Value) (payload : Octets)
  /-- A session performative on channel zero, which is the connection's to relay and
  nobody's to answer as a session step. -/
  | stray

/-- The frame a step carries, decoded where it carries octets rather than a structure:
the corpus vocabulary names the channel and the body, and either is what says which
machine the step is for. -/
def carried (step : ExchangeStep) :
    Except String (Option (Nat × SpecAMQP.Spec.Codec.Value × Octets)) := do
  match step.value with
  | some json =>
    let frame ← frameOfJson json
    match frame.body with
    | some body => return some (frame.channel, body, frame.payload)
    | none => return none
  | none =>
    match step.bytes with
    | none => return none
    | some octets =>
      if SpecAMQP.Spec.Connection.headerShaped octets then return none
      else
        match SpecAMQP.Spec.Frame.decodeFrame octets with
        | .error _ => return none
        | .ok (frame, _) =>
          match frame.body with
          | some body => return some (frame.channel, body, frame.payload)
          | none => return none

/-- Whether a frame is the connection's rather than a session's: `open` and `close` are
the two the dispatch table gives the connection endpoint, whatever channel they are on —
which is why a `close` may be received "on any channel up to the maximum channel number
negotiated in open" — and a SASL performative belongs to the security layer's dialogue,
which the connection layer carries between the two header exchanges. -/
def isConnectionLevel (body : SpecAMQP.Spec.Codec.Value) : Bool :=
  match SpecAMQP.Spec.Frame.typeOfDescriptor (match body with
    | .described descriptor _ => descriptor
    | other => other) with
  | some declaration =>
    declaration.name == "open" || declaration.name == "close" ||
      declaration.provides.contains "sasl-frame"
  | none => false

/-- Which machine answers for a step.

A step whose octets are a protocol header, or which the frame layer cannot read, is the
connection's: it is the one that reads headers and reports the framing failures. A frame
carrying `open` or `close` is the connection's too, and a session performative on channel
zero is the connection's by the register's reading — where it is refused, because the
connection has no session on channel zero to delegate it to. -/
def targetOf (step : ExchangeStep) : Except String Target := do
  match (← carried step) with
  | none => return .connection
  | some (channel, body, payload) =>
    if isConnectionLevel body then return .connection
    else if channel == 0 then return .stray
    else return .session channel body payload

/-- A connection outcome with its layer on the state name. -/
def asConnection (outcome : StepOutcome) : StepOutcome :=
  { outcome with state := s!"connection:{outcome.state}" }

/-- One step, dispatched to the machine that answers for it. -/
def stepOf (peer : Peer) (step : ExchangeStep) : Except String (StepOutcome × Peer) := do
  match (← targetOf step) with
  | .connection =>
    let (outcome, connection) ← SpecAMQP.Spec.ConnectionCodec.stepOf peer.connection step
    return (asConnection outcome, { peer with connection := connection })
  | .stray =>
    -- the connection's rules apply to the frame, and then there is no session on channel
    -- zero for it to be delegated to
    let (relayed, connection) ← SpecAMQP.Spec.ConnectionCodec.stepOf peer.connection step
    if !relayed.admitted then
      return (asConnection relayed, { peer with connection := connection })
    return (⟨false, none, s!"connection:{connection.state.name}", some framingError,
             s!"illegalState: a session performative is not for channel 0, where the \
               connection has no session to delegate it to; the peer is in \
               connection:{connection.state.name}"⟩,
            { peer with connection := connection })
  | .session channel body payload =>
    -- the connection first: the frame must be one it can carry, at all
    let (relayed, connection) ← SpecAMQP.Spec.ConnectionCodec.stepOf peer.connection step
    if !relayed.admitted then
      return (asConnection relayed, { peer with connection := connection })
    -- and where the connection is discarding because of an error, what a session would
    -- have answered is discarded with it: "any incoming frames on the connection MUST be
    -- silently discarded until the peer's close frame is received"
    if connection.state == State.discarding then
      return (asConnection relayed, { peer with connection := connection })
    -- then the session, whose moment depends on what the connection is doing
    match SpecAMQP.Spec.Protocol.step peer.session step.send channel body payload with
    | .ok session =>
      let state := s!"session:{session.legacy.state.name}"
      return ({ relayed with state, detail := s!"admitted; the peer is in {state}" },
              { peer with connection := connection, session := session })
    | .error reason =>
      if reason.closesConnection then
        -- the session's rule with the connection's consequence: `attach/field:handle.2`
        -- and `begin/field:handle-max.2` both mandate an immediate close, which is the
        -- connection's frame to write, so the connection moves to CLOSE_SENT and the
        -- state the outcome names is the one that moved
        let connection := { connection with state := State.closeSent }
        let state := s!"connection:{connection.state.name}"
        return (⟨false, none, state, some reason.condition,
                 s!"{reason.detail}; the peer closes the connection, and is in {state}"⟩,
                { peer with connection, session := peer.session })
      let session :=
        SpecAMQP.Spec.Protocol.withState peer.session
          (reason.state.getD peer.session.legacy.state)
      let state := s!"session:{session.legacy.state.name}"
      return (⟨false, none, state, some reason.condition,
               s!"{reason.detail}; the peer is in {state}"⟩,
              { peer with connection := connection, session := session })

/-- The peer a start state names.

`connection:<NAME>` starts the connection's machine at that state with a session that has
not begun; `session:<NAME>` starts the session's machine at that state under the
connection a session implies. A name the table does not have fails here rather than being
read as some default. -/
def start (name : String) : Except String Peer := do
  match name.splitOn ":" with
  | ["connection", state] =>
    let connection ← SpecAMQP.Spec.ConnectionCodec.specExchangeCodec.start state
    return { connection, session := SpecAMQP.Spec.Protocol.sessionOf Session.initial }
  | ["session", state] =>
    let session ←
      match SpecAMQP.Spec.Session.State.ofName state with
      | some state => pure (SpecAMQP.Spec.Protocol.sessionOf (Session.atState state))
      | none => .error s!"'{state}' is not a session state the artifact declares"
    return { connection := establishedConnection, session }
  | _ =>
    .error s!"'{name}' is not a layer-prefixed state: a state name begins with \
      `connection:` or `session:`"

/-- The specification's connection and session layers behind the corpus interface. -/
def specExchangeCodec : ExchangeCodec where
  name := "specification"
  St := Peer
  start := start
  step := stepOf

end SpecAMQP.Spec.SessionCodec
