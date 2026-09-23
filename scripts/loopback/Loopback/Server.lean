/-
# The loopback server

One connection, one dialogue, then exit: accept, read the announced payload, echo
it back octet for octet, and report what it saw. The reports are the evidence —
the octet counts and, above all, the *number of `recv` calls* the payload took,
because a payload that spans many reads is the case where a shim truncates or
reorders without saying so.

Two orderings here are deliberate rather than incidental.

`listen` happens before the readiness line is printed, so a runner that waits for
that line cannot race the port into existence. And the line is *flushed*: Lean's
stdout is block-buffered, so without the flush a server that then blocks in
`accept` would leave its readiness line in a buffer and a waiting runner would wait
forever — a failure that looks like a hang in the transport and is not one.

The last `recv` is not decoration. After echoing, the server reads once more and
expects `none`, which is the only way the orderly-close case of the boundary's
contract is exercised by R1's evidence rather than merely documented.
-/

import Loopback.Payload
import Loopback.Wire

namespace Loopback.Server

open SpecAMQP.Impl.Transport

def usage : String := "usage: amqp-loopback-server <port> <chunk-octets>"

/-- Serve one connection to completion. Throws on anything that makes the dialogue
impossible; the entry point turns that into a message and an exit status. -/
def serve (port : UInt16) (chunk : Nat) : IO Unit := do
  let listener ← listen port
  IO.println s!"server: listening port={port} chunk={chunk}"
  -- Flushed deliberately: see the module header. A reader waiting for this line is
  -- the intended consumer, and an unflushed line never reaches it.
  (← IO.getStdout).flush

  let conn ← accept listener
  IO.println "server: accepted one connection"

  let (header, headerCalls) ← Wire.recvExactly conn Wire.headerOctets chunk
  let announced ← IO.ofExcept (Wire.headerLength header)
  IO.println s!"server: dialogue announces {announced} octets (header in {headerCalls} recv call(s))"

  let (payload, payloadCalls) ← Wire.recvExactly conn announced chunk
  IO.println s!"server: received {payload.size} octets in {payloadCalls} recv call(s)"

  let sendCalls ← Wire.sendAll conn payload
  IO.println s!"server: echoed {payload.size} octets in {sendCalls} send call(s)"

  match ← recv conn chunk.toUSize with
  | none => IO.println "server: peer closed the connection (orderly)"
  | some extra =>
    throw (IO.userError s!"peer sent {extra.size} octets after the dialogue")

  conn.close
  listener.close
  IO.println "server: closed"

/--
The server's command line: parse, serve, and turn the outcome into an exit status.
Namespaced rather than a bare `main`, because Lean emits the C `main` wrapper only for
a module that declares a *local* `main`, and Lake allows one executable per root
module — so each executable gets its own four-line root module (`ServerMain.lean` for
the real one, `ControlServerMain.lean` for the control) and they share this function
instead of a copy of it.
-/
def runMain (args : List String) : IO UInt32 := do
  match args with
  | [portText, chunkText] =>
    match Wire.portArg portText, Wire.chunkArg chunkText with
    | .ok port, .ok chunk =>
      try
        serve port chunk
        return 0
      catch error =>
        IO.eprintln s!"server: {error}"
        return 1
    | .error message, _ =>
      IO.eprintln s!"server: {message}\n{usage}"
      return 2
    | _, .error message =>
      IO.eprintln s!"server: {message}\n{usage}"
      return 2
  | _ =>
    IO.eprintln usage
    return 2

end Loopback.Server
