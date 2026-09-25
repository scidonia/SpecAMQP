import Harness.Runner
import Ref.ConnectionCodec
import Ref.Protocol
import Ref.Session
import Ref.Vectors

/-!
# The reference implementation's exchange layer: connection and session

The same interface as the specification's `Spec.SessionCodec`: one codec for both
machines, because a frame's layer follows from what it carries and the session's moment
depends on the connection's. The dispatch is the register's reading — a protocol header,
`open`/`close` and a SASL performative are the connection's; a session performative
belongs to the session on the channel it carries; one on channel zero has no session to
be delegated to and is refused — and the state name a step reports says which machine
answered, which is why a step whose frame the connection refuses names a connection
state even when the frame is on a session's channel.

A `session:` start names the session's state under the connection a session implies:
`OPENED` as if both `open`s had been exchanged with their fields unset.
-/

namespace SpecAMQP.Ref.SessionCodec

open Lean
open SpecAMQP.Harness
open SpecAMQP.Ref.Connection (Bounds Peer)
open SpecAMQP.Ref.Protocol (WidenedSession)
open SpecAMQP.Ref.Session (Endpoint)

/-- One peer in an exchange: the connection's endpoint and the session's. The session is the widened
one — a registry of named links with two endpoint-local handle spaces and one shared unsettled
history — whose session-scope state is the restricted endpoint's. -/
structure Both where
  connection : Peer
  session : WidenedSession

/-- The bounds an `open` whose fields are unset declares, from the generated field
table. -/
def declaredBounds : Bounds :=
  ⟨(match SpecAMQP.Ref.Connection.declaredDefault "open" "max-frame-size" with
    | some n => n | none => 0),
   (match SpecAMQP.Ref.Connection.declaredDefault "open" "channel-max" with
    | some n => n | none => 0)⟩

/-- The connection a `session:` start implies. -/
def establishedConnection : Peer :=
  { Peer.new with state := SpecAMQP.Ref.Connection.State.open, own := declaredBounds, partner := declaredBounds }

/-- Which machine answers for a step. -/
inductive Target where
  | connection
  | session (channel : Nat) (body : Value) (payload : Octets)
  | stray

/-- Whether the frame is the connection's: `open`, `close`, or a SASL performative,
whose dialogue the connection layer carries. -/
def connectionLevel (body : Value) : Bool :=
  match SpecAMQP.Ref.Frame.typeOfDescriptor (match body with
    | .described descriptor _ => descriptor
    | other => other) with
  | some declaration =>
    declaration.name == "open" || declaration.name == "close" ||
      declaration.provides.contains "sasl-frame"
  | none => false

/-- The frame a step carries, decoded where it carries octets. -/
def carried (step : ExchangeStep) : Except String (Option (Nat × Value × Octets)) := do
  match step.value with
  | some json =>
    let frame ← SpecAMQP.Ref.Vectors.frameOfJson json
    match frame.body with
    | some body => return some (frame.channel, body, frame.payload)
    | none => return none
  | none =>
    match step.bytes with
    | none => return none
    | some octets =>
      if SpecAMQP.Ref.Connection.looksLikeHeader octets then return none
      else
        match SpecAMQP.Ref.Frame.decodeFrame octets with
        | .error _ => return none
        | .ok (frame, _) =>
          match frame.body with
          | some body => return some (frame.channel, body, frame.payload)
          | none => return none

/-- Which machine answers for a step. -/
def targetOf (step : ExchangeStep) : Except String Target := do
  match (← carried step) with
  | none => return .connection
  | some (channel, body, payload) =>
    if connectionLevel body then return .connection
    else if channel == 0 then return .stray
    else return .session channel body payload

/-- A connection outcome with its layer on the state name. -/
def asConnection (outcome : StepOutcome) : StepOutcome :=
  { outcome with state := s!"connection:{outcome.state}" }

/-- One step, dispatched to the machine that answers for it. -/
def stepOf (both : Both) (step : ExchangeStep) : Except String (StepOutcome × Both) := do
  match (← targetOf step) with
  | .connection =>
    let (outcome, connection) ← SpecAMQP.Ref.ConnectionCodec.stepOf both.connection step
    return (asConnection outcome, { both with connection := connection })
  | .stray =>
    let (relayed, connection) ← SpecAMQP.Ref.ConnectionCodec.stepOf both.connection step
    if !relayed.admitted then
      return (asConnection relayed, { both with connection := connection })
    return (⟨false, none, s!"connection:{connection.state.label}",
             some SpecAMQP.Ref.Connection.wireCondition,
             s!"illegalState: a session performative is not for channel 0, where the \
               connection has no session to delegate it to; the peer is in \
               connection:{connection.state.label}"⟩,
            { both with connection := connection })
  | .session channel body payload =>
    let (relayed, connection) ← SpecAMQP.Ref.ConnectionCodec.stepOf both.connection step
    if !relayed.admitted then
      return (asConnection relayed, { both with connection := connection })
    -- where the connection is discarding because of an error, what a session would have
    -- answered is discarded with it
    if connection.state == SpecAMQP.Ref.Connection.State.discard then
      return (asConnection relayed, { both with connection := connection })
    match SpecAMQP.Ref.Protocol.step both.session step.send channel body payload with
    | .ok session =>
      let state := s!"session:{session.legacy.state.label}"
      return ({ relayed with state, detail := s!"admitted; the peer is in {state}" },
              { both with connection := connection, session := session })
    | .error reason =>
      if reason.closes then
        -- the session's rule with the connection's consequence: an immediate close is the
        -- connection's frame to write, so the connection moves and the state the outcome
        -- names is the one that moved
        let connection := { connection with
                              state := SpecAMQP.Ref.Connection.State.sndClose }
        let state := s!"connection:{connection.state.label}"
        return (⟨false, none, state, some reason.condition,
                 s!"{reason.detail}; the peer closes the connection, and is in {state}"⟩,
                { both with connection := connection })
      let session :=
        SpecAMQP.Ref.Protocol.withState both.session
          (reason.place.getD both.session.legacy.state)
      let state := s!"session:{session.legacy.state.label}"
      return (⟨false, none, state, some reason.condition,
               s!"{reason.detail}; the peer is in {state}"⟩,
              { both with connection := connection, session := session })

/-- The peer a layer-prefixed start state names. -/
def start (name : String) : Except String Both := do
  match name.splitOn ":" with
  | ["connection", state] =>
    let connection ← SpecAMQP.Ref.ConnectionCodec.refExchangeCodec.start state
    return { connection := connection,
             session := SpecAMQP.Ref.Protocol.sessionOf (Endpoint.atState .unmapped) }
  | ["session", state] =>
    let session ←
      match SpecAMQP.Ref.Session.State.lookup state with
      | some state => pure (SpecAMQP.Ref.Protocol.sessionOf (Endpoint.atState state))
      | none => .error s!"'{state}' is not a session state the artifact declares"
    return { connection := establishedConnection, session := session }
  | _ =>
    .error s!"'{name}' is not a layer-prefixed state: a state name begins with \
      `connection:` or `session:`"

/-- The reference implementation's connection and session layers behind the corpus
interface. -/
def refExchangeCodec : ExchangeCodec where
  name := "reference"
  St := Both
  start := start
  step := stepOf

end SpecAMQP.Ref.SessionCodec
