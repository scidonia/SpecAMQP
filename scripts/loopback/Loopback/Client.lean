/-
# The loopback client

Dial, send a known byte string announced by its length, read the same number of
octets back, and compare them octet for octet. The comparison is the whole point:
delivering the right *number* of octets proves the transfer's length, and only a
per-octet comparison proves the values arrived in the order they were sent — a shim
that reorders a multi-buffer transfer preserves every count and fails here.

The exit status carries the verdict, so the runner can rely on the process rather
than on parsing this output: zero for a match, one for a mismatch or a failed
dialogue, and two for a usage error.
-/

import Loopback.Payload
import Loopback.Wire

namespace Loopback.Client

open SpecAMQP.Impl.Transport

def usage : String := "usage: amqp-loopback-client <port> <octets> <chunk-octets>"

/-- The client's command line: where to connect, how much to send, and how much to
ask for per read — the last of which is what makes the payload span many `recv`
calls rather than arriving in one. -/
def parse (args : List String) : Except String (UInt16 × Nat × Nat) :=
  match args with
  | [portText, countText, chunkText] => do
    -- 64 MiB is a harness ceiling, not a transport limit: it keeps a mistyped length
    -- from being a multi-gigabyte allocation in a test.
    let port ← Wire.portArg portText
    let count ← Wire.boundedArg "octets" countText 0 (64 * 1024 * 1024)
    let chunk ← Wire.chunkArg chunkText
    return (port, count, chunk)
  | _ => .error usage

/-- One dialogue; `true` if the octets came back unchanged. -/
def run (port : UInt16) (count chunk : Nat) : IO Bool := do
  let conn ← connect port
  IO.println s!"client: connected port={port} payload={count} chunk={chunk}"

  let payload := Payload.ofLength count
  let headerCalls ← Wire.sendAll conn (Wire.lengthHeader count)
  let payloadCalls ← Wire.sendAll conn payload
  IO.println s!"client: sent {count + Wire.headerOctets} octets in {headerCalls + payloadCalls} send call(s)"

  let (echoed, recvCalls) ← Wire.recvExactly conn count chunk
  IO.println s!"client: received {echoed.size} octets in {recvCalls} recv call(s)"

  let matched ← match Payload.compare payload echoed with
    | .ok () =>
      IO.println "client: byte-for-byte comparison: MATCH"
      pure true
    | .error difference =>
      IO.println s!"client: byte-for-byte comparison: MISMATCH — {difference}"
      pure false

  conn.close
  IO.println "client: closed"
  return matched

/--
The client's command line: parse, run one dialogue, and carry the verdict in the exit
status. Namespaced for the same reason the server's is — see `Loopback/Server.lean`.
-/
def runMain (args : List String) : IO UInt32 := do
  match parse args with
  | .error message =>
    IO.eprintln s!"client: {message}"
    return 2
  | .ok (port, count, chunk) =>
    try
      if ← run port count chunk then return 0 else return 1
    catch error =>
      IO.eprintln s!"client: {error}"
      return 1

end Loopback.Client
