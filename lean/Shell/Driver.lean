/-
# The shell (R2, `PLAN.md` §23.1): the IO the proved core is surrounded by

The core (`Impl.Core`, `Impl.Stream`) is pure: octets and events in, octets and events out, no `IO`. A
process that speaks AMQP also needs a socket, a read loop and a write loop, and this module is that part
and nothing else. It lives in `lean/Shell/` rather than in `lean/Impl/` because the directory is the
claim: nothing inside `lean/Impl/` may import `Impl.Transport`, so "the only unproved module in the
shipped tree is the boundary" stays a fact about a directory rather than a reading of two files, and the
shell does import it.

## What the shell is, and what it is not

**It is not proved, and that is a named position rather than an omission.** `Conforms` (`PLAN.md` §10)
quantifies over octets and answers — `Input` and `Output` — and this module is where file descriptors,
`recv` and `send` live, none of which the relation can see. The implementation's unproved part is
therefore *two* things and not one: the socket boundary (`Impl.Transport` plus the kernel's socket ABI)
and **this shell**. §23.1 has been amended to say so, because "the core is proved to conform" is a claim
about the core, and a reader who takes it for a claim about the *process* has been misled by an omission.

The shell's own correctness, stated as the three obligations it does not prove and that R4's wire
differential is the only tier that can test:

1. **It loops on a short read.** `recv` promises at most what was asked for, so a read that returns part
   of what the peer sent is ordinary and the octets it returned are fed to `Impl.Stream.feed`, which
   keeps what does not yet make a unit. Neither this loop nor the boundary may assume that one read is
   one frame.
2. **It writes exactly what the core returns, and all of it.** The octets of an `Output.frame` are written
   in the order the core produced them, looping while `send` accepts them in pieces, and a `send` that
   accepts nothing is a loud failure rather than a shorter payload. The shell adds no framing, no
   buffering and no reordering of its own: an `Output.frame` that is not written whole, or is written
   twice, or is written out of order, is a defect here and not in the core.
3. **It treats `recv`'s `none` as the peer's orderly close, not as a fault.** The boundary refuses a
   zero-octet *request* (`EINVAL`) precisely so the two cannot be confused: `none` means the peer
   finished, and the shell responds by calling `Impl.Stream.closed` — dropping the octets that can never
   be completed — and ending the connection quietly. A transport failure is a different arm and it
   propagates as the `IO.Error` the boundary raised.

What the shell *does* decide — and it is deliberately almost nothing — is the size of one `recv` request,
and the sequencing of the socket's lifecycle (`listen`, `accept`, `connect`, `close`). Both are
parameters or straight-line code, not protocol behaviour, which is why §10's relation can quantify past
them.

## The seam with the proved part, function by function

The shell calls exactly these, and nothing else of the core:

* `Impl.Core.announceHeader` — the fixed header this peer announces, laid out from the specification's
  own protocol id and version (`Impl.Core.announceHeader`'s version comes from the generated constant
  table). The shell resolves its `none` — the artifact stating no version for the AMQP layer — into a
  loud failure.
* `Impl.Stream.feed` — octets read from the socket, in whatever sizes the kernel returned them, to the
  endpoint's state and the outputs to put on the wire.
* `Impl.Core.submit` — the application asking to send octets, answered with what to write or with the
  reason its octets are not something this peer can send (a loud failure here, not a silent skip).
* `Impl.Stream.closed` — the peer's orderly close.
* The `Output` vocabulary: `Output.frame` for the wire, `Output.api` for what the endpoint's owner is
  told (which R4's runner reads as the verdict line).

The socket's side is `Impl.Transport`'s six operations and no seventh: a synchronous recv-feed-write loop
needs `accept`, `recv`, `send` and `close`, and `listen`/`connect` are what make those reachable. §23.1
defines the boundary's size as the count the trust gate prints, so a seventh operation would be a visible
change and a decision rather than a detail.
-/

import Impl.Core
import Impl.Stream
import Impl.Transport

namespace SpecAMQP.Shell

open SpecAMQP.Harness (Octets)
open SpecAMQP.Contracts (Output)
open SpecAMQP.Impl.Transport
open SpecAMQP.Impl.Core (State)

/-- How many octets one `recv` request asks for. The kernel may return fewer — that is what makes the
read loop necessary — and the value is a parameter of the shell so a control can force the splits it
wants rather than relying on timing. -/
def defaultReadOctets : USize := 4096

/-- What the application asks for after the core has answered: octets to send, and whether it is
finished with the connection.

The shell has no protocol policy of its own. Which frames an endpoint sends, and when, belongs to the
programme the endpoint *is* — the corpus runner of R4, or a test harness — and this is the seam where it
is asked through the core (`Impl.Core.submit`), so that no frame is ever built by the shell. -/
structure Reply where
  /-- The octets to send, in order. -/
  octets : Array Octets
  /-- Whether the application is finished: a finished application closes the connection. -/
  done : Bool

/-- The application, as the shell sees it: the core's state after a step, and the outputs it produced. -/
abbrev App := State → List Output → Reply

/-! ## The two loops the boundary makes necessary -/

/-- **Write every octet.** `send` reports what the kernel accepted, so a caller that must write all of
`octets` loops — and this loop *checks* the boundary's promise as it uses it: a `send` that accepts
nothing fails loudly rather than silently producing a shorter write, and one that claims more than it was
offered fails loudly too. (`scripts/loopback/Loopback/Wire.lean`'s `sendAll` is the worked example of the
same discipline; it is R1's harness and this is the shipped path, so the two are separate by design.) -/
def sendAll (conn : Conn) (octets : ByteArray) : IO Unit := do
  let mut sent := 0
  let mut calls := 0
  while sent < octets.size do
    let accepted ← send conn (octets.extract sent octets.size)
    let taken := accepted.toNat
    calls := calls + 1
    if taken = 0 then
      throw (IO.userError s!"the transport accepted no octets at {sent} of {octets.size}")
    if sent + taken > octets.size then
      throw (IO.userError
        s!"the transport accepted {taken} octets at {sent} of {octets.size}, which is more than it was offered")
    sent := sent + taken
  -- a write the kernel took in one call is the ordinary case and says nothing; one it took in pieces is
  -- the case this loop exists for, and the count is what makes it observable rather than inferred
  if calls > 1 then
    IO.println s!"endpoint: wrote {octets.size} octets in {calls} send call(s)"
    (← IO.getStdout).flush

/-- Where the endpoint's owner is told what happened. The shell writes one line per answer to standard
output, which is the socket-level twin of the corpus's verdict line ("the state name on a step taken,
the condition and reason class on a refusal"), and R4's runner reads it there. Kept as a function so a
different consumer is a different function rather than a different shell. -/
def reportAnswer (answer : SpecAMQP.Contracts.ApiResponse) : IO Unit :=
  IO.println (if answer.ok then s!"took {answer.name}" else s!"refused {answer.name}")

/-- Put the core's outputs on the wire, in the order the core produced them: frames out, and the
application's answers reported rather than written. -/
def writeOutputs (conn : Conn) (outs : List Output) : IO Unit := do
  for out in outs do
    match out with
    | .frame bytes => sendAll conn bytes
    | .api answer => reportAnswer answer

/-- Ask the application what to send, put it through the core, and write what the core says. The core's
refusal to read the octets as a send is a **loud** failure: the application asked for something this peer
cannot send, and continuing would put nothing on the wire while the caller believed otherwise. -/
def serveApp (conn : Conn) (core : State) (outs : List Output) (app : App) : IO (State × Bool) := do
  let reply := app core outs
  let mut core := core
  let mut live := true
  for octets in reply.octets do
    match SpecAMQP.Impl.Core.submit core octets with
    | .error message =>
      throw (IO.userError s!"the application asked to send octets the core cannot send: {message}")
    | .ok (core', outs') =>
      core := core'
      writeOutputs conn outs'
      if core'.conn.state == SpecAMQP.Spec.Connection.State.end then
        live := false
  return (core, live && !reply.done)

/-- **Read once.** One `recv` request, fed to the core whatever its size: `none` is the peer's orderly
close and ends the connection, and the octets that arrived incomplete are dropped with it
(`Impl.Stream.closed`). -/
def readOnce (conn : Conn) (core : State) (readOctets : USize) : IO (Option (State × List Output)) := do
  let some bytes ← recv conn readOctets | return none
  let (core', outs) := SpecAMQP.Impl.Stream.feed core bytes
  writeOutputs conn outs
  return some (core', outs)

/-- **The loop**: read, feed, write, ask the application, and repeat until the peer closes the stream or
the application is finished.

This is where the shell's three unproved obligations live: a short read is fed as it arrives (the core
keeps what does not yet make a unit), the outputs are written whole and in order, and `recv`'s `none`
ends the connection rather than being treated as a fault. Returns the state the connection ended in,
which is what the process reports. -/
def pump (conn : Conn) (core : State) (app : App)
    (readOctets : USize := defaultReadOctets) : IO State := do
  let mut core := core
  let mut live := true
  while live do
    match ← readOnce conn core readOctets with
    | none =>
      -- the peer's orderly close (obligation 3 above): nothing further can arrive, and the octets held
      -- incomplete can never be completed, so they are dropped and the endpoint says so
      IO.println "endpoint: the peer closed the stream (orderly)"
      core := SpecAMQP.Impl.Stream.closed core
      live := false
    | some (core', outs) =>
      let (core'', keepGoing) ← serveApp conn core' outs app
      core := core''
      live := keepGoing
  return core

/-- **The layer a protocol header names.** The header *is* the decision: `announcedHeader` builds it from
the layer this peer offers, and the connection starts in the layer that same header names, so announcing
one layer and speaking the other is not a state this shell can reach. The protocol id is the field the
layout draws at index 4 — `magic` is four octets — and anything that is not SASL's is read as AMQP, which
is the conservative default rather than a third layer this peer does not speak. -/
def layerOfHeader (header : Octets) : SpecAMQP.Spec.Connection.Layer :=
  if header[4]? == some (SpecAMQP.Spec.Connection.octet
      (SpecAMQP.Spec.Connection.Layer.protocolId SpecAMQP.Spec.Connection.Layer.sasl).code)
  then .sasl else .amqp

/-- **Run one connection from the application's opening move to the end**: the announced header first
(the shell's only protocol act of its own, and the one §23.1 calls "a fixed header"), then the loop, then
the socket's close. -/
def runConnection (conn : Conn) (header : Octets) (app : App)
    (readOctets : USize := defaultReadOctets) : IO State := do
  let core : State :=
    { conn := { SpecAMQP.Spec.Connection.Endpoint.initial with layer := layerOfHeader header },
      inbox := #[] }
  match SpecAMQP.Impl.Core.submit core header with
  | .error message =>
    throw (IO.userError s!"this peer cannot announce its own header: {message}")
  | .ok (core, outs) =>
    writeOutputs conn outs
    pump conn core app readOctets

/-! ## The socket's lifecycle -/

/-- **Bind and listen**, so that a caller can announce the port it is ready on before it blocks. A
failure to bind propagates as the boundary's own `IO.Error`: the shell does not retry, because "the port
is taken" is a fact about the environment that a retry loop would hide. -/
def listenOn (port : UInt16) : IO Listener := listen port

/-- **Serve one connection on a listening socket**: accept, run the connection, close it. The listener
stays the caller's to close, so a caller that wants to serve more than one connection (a later rung)
does not have to open the port twice. -/
def serveConn (listener : Listener) (header : Octets) (app : App)
    (readOctets : USize := defaultReadOctets) : IO State := do
  let conn ← accept listener
  try
    let core ← runConnection conn header app readOctets
    conn.close
    return core
  catch e =>
    conn.close
    throw e

/-- **Dial one connection**: connect, run it, close the socket. -/
def dial (port : UInt16) (header : Octets) (app : App)
    (readOctets : USize := defaultReadOctets) : IO State := do
  let conn ← connect port
  try
    let core ← runConnection conn header app readOctets
    conn.close
    return core
  catch e =>
    conn.close
    throw e

/-- The fixed header a peer announces for a layer, or a loud failure: the artifact stating no version for
that layer is a defect in the tables this repository generates from, and it would leave the endpoint with
nothing to send. The layer defaults to AMQP, so a caller that offers only the AMQP layer says nothing. -/
def announcedHeader (layer : SpecAMQP.Spec.Connection.Layer := .amqp) : IO Octets :=
  match SpecAMQP.Impl.Core.announceHeaderFor layer with
  | some header => pure header
  | none =>
    throw (IO.userError
      s!"the artifact states no version for the {layer.name} layer, so this peer has no header to \
announce")

/-! ## Reading a command line

Three small parsers, shared by the endpoint process and the harness probe below the socket: a typo in a
port is refused by name rather than truncated to a port number that means something else, and a read size
is never zero — the boundary refuses a zero-octet *request* precisely so it cannot be confused with an
orderly close, and nothing in this tree should be able to ask for one.
-/

/-- A decimal argument in `[low, high]`. -/
def boundedArg (name text : String) (low high : Nat) : Except String Nat :=
  match text.toNat? with
  | none => .error s!"{name} must be a decimal number, not '{text}'"
  | some n =>
    if n < low || n > high then .error s!"{name} must be between {low} and {high}, not {n}"
    else .ok n

/-- A port: in the range a `UInt16` can carry, and not below the reserved range. -/
def portOf (text : String) : Except String UInt16 :=
  (boundedArg "port" text 1024 65535).map (fun n => n.toUInt16)

/-- A read size: at least one octet. -/
def readOctetsOf (text : String) : Except String USize :=
  (boundedArg "read-octets" text 1 (1024 * 1024)).map (fun n => n.toUSize)

end SpecAMQP.Shell
