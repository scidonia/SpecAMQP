/-
`amqp-endpoint server <port> [read-octets]` — listen, accept one connection, speak the protocol.
`amqp-endpoint client <port> [read-octets]` — dial, speak the protocol, close.

The endpoint as a process. Every protocol decision it makes is the specification's own, through the pure
core (`Impl.Core`, `Impl.Stream`); what this file adds is the shape of a process — an argv, a socket's
lifecycle, exit statuses — and the *application* the connection runs, which here is the smallest one that
is still an endpoint: announce the protocol header (the shell does that on every connection, from
`Impl.Core.announceHeader`) and end the connection once both headers have been exchanged, so the process
terminates instead of blocking for a peer that is only testing the transport.

This is the process R4's wire differential replays the corpus against, and the application it runs there
is the runner's, not this one's: `Shell.Driver.App` is the seam, so a corpus-driven application is a
different `App` value rather than a different shell.

Exit status, so a caller can rely on it:

* `0` — the connection ran and ended (including an orderly close by the peer);
* `1` — the transport failed, the peer sent something the core refused at a level the shell cannot
  continue from, or the socket could not be opened: the message on standard error names which;
* `2` — the command line is not this programme's (an unknown role, a port out of range, a bad read size).

Nothing here is proved, and the shell's three unproved obligations are stated in `Shell.Driver`'s header
next to the loops that carry them.
-/

import Shell.Driver

open SpecAMQP.Shell
open SpecAMQP.Harness (Octets)

/-- A decimal argument in `[low, high]`: a typo is refused by name rather than truncated to a port
number that means something else. -/
def boundedArg (name text : String) (low high : Nat) : Except String Nat :=
  match text.toNat? with
  | none => .error s!"{name} must be a decimal number, not '{text}'"
  | some n =>
    if n < low || n > high then .error s!"{name} must be between {low} and {high}, not {n}"
    else .ok n

/-- A port: in the range a `UInt16` can carry, and not below the reserved range. -/
def portOf (text : String) : Except String UInt16 :=
  (boundedArg "port" text 1024 65535).map (fun n => n.toUInt16)

/-- A read size: at least one octet, so that a zero-octet request — which the boundary refuses rather
than confusing it with an orderly close — cannot be asked for from here. -/
def readOctetsOf (text : String) : Except String USize :=
  (boundedArg "read-octets" text 1 (1024 * 1024)).map (fun n => n.toUSize)

/-- The application a **client** runs: announce nothing of its own (the shell announces the header on
every connection, because it is the one frame §23.1 calls fixed) and finish once both protocol headers
have been exchanged, so a client that has nothing to say closes the connection rather than blocking. -/
def clientApp : App :=
  fun core _ => { octets := #[], done := core.conn.state == SpecAMQP.Spec.Connection.State.hdrExch }

/-- The application a **server** runs: announce nothing of its own and never finish of its own accord, so
the connection ends when the peer closes the stream — which is the path that exercises
`Shell.Driver.pump`'s orderly-close arm and `Impl.Stream.closed` in a live process. -/
def serverApp : App :=
  fun _ _ => { octets := #[], done := false }

def usage : IO UInt32 := do
  IO.eprintln "usage: amqp-endpoint server <port> [read-octets]"
  IO.eprintln "       amqp-endpoint client <port> [read-octets]"
  return (2 : UInt32)

def main (args : List String) : IO UInt32 := do
  match args with
  | role :: portText :: rest =>
    if role != "server" && role != "client" then
      IO.eprintln s!"amqp-endpoint: '{role}' is not a role this programme has"
      return (2 : UInt32)
    let port ←
      match portOf portText with
      | .ok p => pure p
      | .error message =>
        IO.eprintln s!"amqp-endpoint: {message}"
        return (2 : UInt32)
    let readOctets ←
      match rest with
      | [] => pure defaultReadOctets
      | [text] =>
        match readOctetsOf text with
        | .ok n => pure n
        | .error message =>
          IO.eprintln s!"amqp-endpoint: {message}"
          return (2 : UInt32)
      | _ =>
        IO.eprintln "amqp-endpoint: read-octets must be one decimal number"
        return (2 : UInt32)
    let header ←
      try
        announcedHeader
      catch e =>
        IO.eprintln s!"amqp-endpoint: {e}"
        return (1 : UInt32)
    try
      if role == "server" then
        let listener ← listenOn port
        try
          -- the readiness line is flushed: Lean's stdout is block-buffered, so an unflushed line never
          -- reaches a caller that is waiting for the port to exist
          IO.println s!"endpoint: listening port={port} read-octets={readOctets.toNat}"
          (← IO.getStdout).flush
          let core ← serveConn listener header serverApp readOctets
          IO.println s!"endpoint: the connection ended in {core.conn.state.name}"
        finally
          listener.close
      else
        let core ← dial port header clientApp readOctets
        IO.println s!"endpoint: the connection ended in {core.conn.state.name}"
      return (0 : UInt32)
    catch e =>
      IO.eprintln s!"endpoint: {e}"
      return (1 : UInt32)
  | _ => usage
