/-
# R4's wire application: the corpus's *send* side, at the shell's `App` seam

`PLAN.md` §23.1's R4 drives the shipped endpoint over a socket, and the shipped endpoint runs an
application that announces the header and then says nothing. That is the right smallest endpoint and the
wrong application for a differential: every `send` step of an exchange vector asks the endpoint to put a
frame on the wire, and with an application that sends nothing the differential can only report that
nothing arrived. It would report it for every vector and prove nothing about the endpoint.

This is the application that plays the corpus's send side: it reads a vector, works out which of its
`send` steps are the application's (the shell announces the header itself, before the core's first read,
so a step whose pre-state is `START` is not the application's to play), and emits a step's octets when the
core is in the state that step is played from. Its counterpart is `scripts/endpoint/wire_peer.py`, which
plays the vector's `receive` side over the socket; together they are a corpus-driven pair on the wire.

**It is harness, not a claim about an application.** It lives outside `lean/Shell/` for the same reason
`EndpointProbe.Client` does: the shell is parameterised by `App` so that a different application is a
different value rather than a different shell, and no test-only policy ships. Nothing here is proved, and
nothing here is protocol logic — the octets come from the corpus, the core decides whether they may be
sent, and the shell writes them.

Two properties are deliberate and load-bearing:

* **It is pure, and therefore idempotent.** `App` is a function of the core's state and the outputs just
  produced, and the shell may ask it more than once in one state. Keying the choice on the *state* rather
  than on an internal counter means the same state always gives the same answer, so a step is never sent
  twice: an admitted send moves the core to the next state, and only the step played from that state can
  be chosen next.
* **A state that matches no step sends nothing, and the differential reports that.** Silence here is a
  divergence with a name — "the vector expects the endpoint to write *n* octets and nothing arrived" — not
  a quiet success, which is why the observer is the differential rather than this module.
-/

import Shell.Driver
import Harness.Runner

namespace WireApp

open Lean
open SpecAMQP.Shell
open SpecAMQP.Harness (Octets exchangeStepOf toHex)

/-- A state name without the layer prefix the corpus writes: the corpus says `connection:HDR_EXCH` where
the core's own state name is `HDR_EXCH`. -/
def bare (name : String) : String :=
  (name.splitOn ":").reverse.head?.getD name

/-- One `send` step the application plays: the octets, and the state name it is played from. -/
structure Send where
  octets : Octets
  playedFrom : String
deriving Repr

/-- The application's steps, in the vector's order, each with the state it is played from.

The pre-state of the first step is the vector's `start`; of every later one, the state the previous step
left the peer in — or, when a step names no state, the state its layer was last left in, which is how
`Harness.Runner` reads an omitted `state` and therefore how a vector that says "this frame, now" is
carried forward.

A `send` step that carries a `value` rather than octets is *refused loudly*: the corpus writes those to
say "send a frame the harness builds", the octets of which are the implementation's own choice, so a wire
replay has nothing to compare and must not pretend otherwise. -/
def sendsOf (startName : String) (steps : Array Json) : Except String (Array Send) := do
  let mut playedFrom := bare startName
  let mut out : Array Send := #[]
  for step in steps do
    let parsed ← exchangeStepOf step
    let expect := (step.getObjVal? "expect").toOption.getD (Json.mkObj [])
    let after := (expect.getObjValAs? String "state").toOption.getD playedFrom
    if parsed.send then
      match parsed.bytes with
      | some bytes => out := out.push { octets := bytes, playedFrom := playedFrom }
      | none =>
        .error "this vector asks the endpoint to send a `value`, whose octets the implementation \
          chooses: a wire differential has nothing to compare, so this application refuses the vector \
          rather than sending something the corpus did not pin"
    playedFrom := bare after
  return out

/-- **The application.** In the state a step is played from, send that step's octets; in any other state,
send nothing. The first match in the vector's order wins, so two steps played from one state are played in
the order the corpus writes them. -/
def app (sends : Array Send) : App :=
  fun core _ =>
    match sends.find? (fun step => step.playedFrom == core.conn.state.name) with
    | some step => { octets := #[step.octets], done := false }
    | none => { octets := #[], done := false }

/-- **The header this endpoint announces.** The shell plumbs the header and the core checks it — the
application is what decides which one to offer — so the vector's own header is announced where the vector
pushes it first, and the AMQP layer's otherwise.

It matters because the header's protocol id *is* the layer the connection is in: the corpus is written for
a peer that offers SASL first (protocol id 3), and an endpoint that announces the AMQP header for such a
peer never enters the SASL layer at all, however correct its core is. -/
def headerOf (sends : Array Send) (fallback : Octets) : Octets :=
  match sends.find? (fun step => step.octets.size == 8 &&
      toHex (step.octets.extract 0 4) == "414d5150") with
  | some step => step.octets
  | none => fallback

end WireApp

open WireApp SpecAMQP.Shell Lean
open SpecAMQP.Harness (Octets toHex)

def usage : IO UInt32 := do
  IO.eprintln "usage: amqp-wire-app server <port> <corpus.ndjson> <vector-id> [read-octets]"
  return (2 : UInt32)

/-- The vector's own JSON, found by id in the corpus file: an id the file does not carry is a loud
failure, not an empty script, because an application that plays nothing looks exactly like an endpoint
that has nothing to send. -/
def vectorOf (path id : String) : IO Json := do
  let text ← IO.FS.readFile path
  for line in text.splitOn "\n" do
    if line.trimAscii.isEmpty then
      continue
    match Json.parse line with
    | .error message => throw (IO.userError s!"{path} is not JSON: {message}")
    | .ok json =>
      if ((json.getObjValAs? String "vector").toOption.getD "") == id then
        return json
  throw (IO.userError s!"{path} carries no vector '{id}'")

/-- The process: the shipped shell, serving one connection, with the corpus's send side as the
application. Readiness is printed after the bind and flushed, so a caller that reads the line knows the
port exists; exit statuses follow the endpoint process's convention (`0` ran, `1` the connection or the
vector failed, `2` the command line is not this programme's). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | role :: portText :: rest =>
    if role != "server" then
      IO.eprintln s!"amqp-wire-app: '{role}' is not a role this programme has"
      return (2 : UInt32)
    let port ←
      match portOf portText with
      | .ok p => pure p
      | .error message =>
        IO.eprintln s!"amqp-wire-app: {message}"
        return (2 : UInt32)
    let (path, id, tail) ←
      match rest with
      | path :: id :: tail => pure (path, id, tail)
      | _ =>
        IO.eprintln "amqp-wire-app: a corpus file and a vector id are required"
        return (2 : UInt32)
    let readOctets ←
      match tail with
      | [] => pure defaultReadOctets
      | [text] =>
        match readOctetsOf text with
        | .ok n => pure n
        | .error message =>
          IO.eprintln s!"amqp-wire-app: {message}"
          return (2 : UInt32)
      | _ =>
        IO.eprintln "amqp-wire-app: read-octets must be one decimal number"
        return (2 : UInt32)
    try
      let json ← vectorOf path id
      let startName ←
        match (json.getObjValAs? String "start").toOption with
        | some name => pure name
        | none => throw (IO.userError s!"the vector '{id}' names no start state")
      let steps := (json.getObjValAs? (Array Json) "steps").toOption.getD #[]
      let sends ←
        match sendsOf startName steps with
        | .ok sends => pure sends
        | .error message => throw (IO.userError message)
      let header := headerOf sends (← announcedHeader .amqp)
      let listener ← listenOn port
      try
        IO.println s!"endpoint: listening port={port} read-octets={readOctets.toNat} \
          vector={id} send-steps={sends.size} header={toHex header}"
        (← IO.getStdout).flush
        let core ← serveConn listener header (app sends) readOctets
        IO.println s!"endpoint: the connection ended in {core.conn.state.name}"
      finally
        listener.close
      return (0 : UInt32)
    catch e =>
      IO.eprintln s!"endpoint: {e}"
      return (1 : UInt32)
  | _ => usage
