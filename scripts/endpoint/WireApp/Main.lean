/-
# R4's wire application: the corpus's *send* side, at the shell's `App` seam

`PLAN.md` §23.1's R4 drives the shipped endpoint over a socket, and the shipped endpoint runs an
application that announces the header and then says nothing. That is the right smallest endpoint and the
wrong application for a differential: every `send` step of an exchange vector asks the endpoint to put a
frame on the wire, and with an application that sends nothing the differential can only report that
nothing arrived. It would report it for every vector and prove nothing about the endpoint.

This is the application that plays the corpus's send side: it reads a vector, works out the `send` steps the
application plays — **all** of them, the protocol header included, because the shell announces nothing on a
connection's behalf — and emits a step's octets when the core is in the state that step is played from. Its
counterpart is `scripts/endpoint/wire_peer.py`, which plays the vector's `receive` side over the socket;
together they are a corpus-driven pair on the wire.

A vector that begins **before** the header exchange (`start: connection:START`) carries the whole exchange in
its own steps, the header included, so the application plays them as they come. A vector that begins *after*
it (`start: connection:HDR_EXCH`) does not, and the application supplies the header that exchange needs as an
opening move of its own: the header is octets at the `App` seam like any other step, so the shell's `START` is
simply where the application is first asked. The peer keys its own prologue on the same `start`, which is what
keeps the two ends of a vector that begins mid-dialogue in step.

**It is pure: the same state always gives the same answer, and it is asked as often as the shell needs to.**
`App` is a function of the core's state and the outputs just produced, and the same state must always produce
the same answer — the point of replaying a corpus is that the process does not depend on timing. What the
shell adds is *how often* it is asked, and this application turns on that: `Shell.Driver.serveApp` asks it
again after each step it takes, and a **refused** send is the one step that cannot move the core, so a
re-prompt in the same state whose outputs carry a refusal is this application's signal that the step it just
attempted is spent and the next step played from that state is due. That is what makes a vector's second send
from one state playable at all — measured on `slice-open-missing-container-id` and
`slice-open-channel-max-wrong-type` (two opens from `HDR_EXCH`, the first refused) and on
`slice-open-before-header` (a refused open, then the header, both from `START`).

* **A state that matches no step sends nothing, and the differential reports that.** Silence here is a
  divergence with a name — "the vector expects the endpoint to write *n* octets and nothing arrived" — not
  a quiet success, which is why the observer is the differential rather than this module.
* **A third `send` from one state is beyond this keying, and the shell's bound is what makes that loud.**
  A pure function of `(state, outputs)` can tell the second of two same-state sends from the first — the
  refusal in the outputs — but not the third from the second: both are re-prompts in one state with a
  refusal in hand. Where a vector needs that, this application repeats the second step and
  `Shell.Driver.serveApp`'s round bound throws, naming the bound, rather than looping or quietly stopping.
  None of `vectors/slice.ndjson`'s vectors reaches it.
* **It is asked once per unit the peer's octets complete, and again after each step it takes.** That is the
  shell's loop rather than this application's choice (`Shell.Driver.serveUnits` asks it after each unit a read
  completed, `Shell.Driver.serveApp` re-asks it while it returns work): a state the core reaches *inside* one
  read is one this application is asked in, whatever the read size or how the kernel split the peer's writes,
  and a read that completes no unit asks it nothing.
-/

import Shell.Driver
import Harness.Runner

namespace WireApp

open Lean
open SpecAMQP.Shell
open SpecAMQP.Contracts (Output)
open SpecAMQP.Harness (Octets exchangeStepOf toHex)

/-- A state name without the layer prefix the corpus writes: the corpus says `connection:HDR_EXCH` where
the core's own state name is `HDR_EXCH`. -/
def bare (name : String) : String :=
  (name.splitOn ":").reverse.head?.getD name

/-- One `send` step the application plays: the octets, the state name it is played from, and whether the
vector expects the core to **refuse** it.

The last field is what lets the application tell a re-prompt from a fresh prompt when two steps are played
from one state: a refused send leaves the core exactly where it was, so the application is asked again in the
same state, and the refusal in the outputs is the only thing that distinguishes the second ask from the
first. -/
structure Send where
  octets : Octets
  playedFrom : String
  refused : Bool
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
    let status := (expect.getObjValAs? String "status").toOption.getD "admitted"
    let after := (expect.getObjValAs? String "state").toOption.getD playedFrom
    if parsed.send then
      match parsed.bytes with
      | some bytes =>
        out := out.push { octets := bytes, playedFrom := playedFrom, refused := status == "refused" }
      | none =>
        .error "this vector asks the endpoint to send a `value`, whose octets the implementation \
          chooses: a wire differential has nothing to compare, so this application refuses the vector \
          rather than sending something the corpus did not pin"
    playedFrom := bare after
  return out

/-- **The header this endpoint announces as its opening move, for a vector that begins after the header
exchange.** A vector whose `start` is `START` carries the exchange in its own steps and is given nothing
here; one that begins past it has no header step, so the application supplies the AMQP layer's header —
the shell announces nothing of its own, and the core reads the layer out of whatever header it is handed. -/
def prologueOf (startName : String) (header : Octets) : Array Send :=
  if bare startName == SpecAMQP.Spec.Connection.State.start.name then
    #[]
  else
    #[{ octets := header, playedFrom := SpecAMQP.Spec.Connection.State.start.name, refused := false }]

/-- Whether the outputs just produced carry a **refusal**: the core's answer to a submission it would not
send. `Impl.Core.refusedAnswer` emits the condition and the reason class, both with `ok := false`, and no
other output in the vocabulary does. -/
def refusedOutputs (outs : List Output) : Bool :=
  outs.any fun out =>
    match out with
    | .api answer => !answer.ok
    | .frame _ => false

/-- **The application.** In the state a step is played from, send that step's octets; in any other state,
send nothing.

The first match in the vector's order wins, so two steps played from one state are played in the order the
corpus writes them: the first, then — once the core has refused it and the shell asks again in the state the
refusal left it in — the next. The refusal in the outputs is what marks the attempted step spent; an
admitted step moves the core, so the first match in the *new* state is already the next step. -/
def app (sends : Array Send) : App :=
  fun core outs =>
    let playable := (sends.filter (fun step => step.playedFrom == core.conn.state.name)).toList
    match playable with
    | [] => { octets := #[], done := false }
    | step :: rest =>
      if refusedOutputs outs && step.refused then
        match rest with
        | next :: _ => { octets := #[next.octets], done := false }
        | [] => { octets := #[], done := false }
      else
        { octets := #[step.octets], done := false }

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
      let header ← announcedHeader .amqp
      let plan := prologueOf startName header ++ sends
      let listener ← listenOn port
      try
        IO.println s!"endpoint: listening port={port} read-octets={readOctets.toNat} \
          vector={id} send-steps={plan.size} header={toHex header}"
        (← IO.getStdout).flush
        let core ← serveConn listener (app plan) readOctets
        IO.println s!"endpoint: the connection ended in {core.conn.state.name}"
      finally
        listener.close
      return (0 : UInt32)
    catch e =>
      IO.eprintln s!"endpoint: {e}"
      return (1 : UInt32)
  | _ => usage
