/-
`amqp-endpoint server <port> [read-octets] [--layer=amqp|sasl]` — listen, accept one connection, speak the protocol.
`amqp-endpoint client <port> [read-octets] [--layer=amqp|sasl]` — dial, speak the protocol, close.

The endpoint as a process. Every protocol decision it makes is the specification's own, through the pure
core (`Impl.Core`, `Impl.Stream`); what this file adds is the shape of a process — an argv, a socket's
lifecycle, exit statuses — and the *application* the connection runs, which here is the smallest one that
is still an endpoint: announce the protocol header (the application's opening move, from
`Impl.Core.announceHeaderFor`, at the layer `--layer=` names) and end the connection once both headers
have been exchanged, so the process terminates instead of blocking for a peer that is only testing the
transport.

`--layer=` is the one configuration input this process has, and it names a single decision: the layer the
endpoint offers. The header is built from it by the *application* — the shell announces nothing on a
connection's behalf — and the core reads the layer back out of the header the application supplies, so the
layer announced and the layer spoken are the same one; a peer that announces SASL and then speaks AMQP,
which is what R4's SASL vectors measured before this switch existed, is not a state this process can reach.
The default is AMQP, which is also the layer a peer with no switch at all announces.

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

/-- The application a **client** runs: announce the protocol header — the application's opening move, since
the shell announces nothing of its own — and finish once both protocol headers have been exchanged, so a
client that has nothing to say closes the connection rather than blocking. -/
def clientApp (header : Octets) : App :=
  fun core _ =>
    if core.conn.state == SpecAMQP.Spec.Connection.State.start then
      { octets := #[header], done := false }
    else
      { octets := #[], done := core.conn.state == SpecAMQP.Spec.Connection.State.hdrExch }

/-- The application a **server** runs: announce the protocol header and never finish of its own accord, so
the connection ends when the peer closes the stream — which is the path that exercises
`Shell.Driver.pump`'s orderly-close arm and `Impl.Stream.closed` in a live process. -/
def serverApp (header : Octets) : App :=
  fun core _ =>
    if core.conn.state == SpecAMQP.Spec.Connection.State.start then
      { octets := #[header], done := false }
    else
      { octets := #[], done := false }

def usage : IO UInt32 := do
  IO.eprintln "usage: amqp-endpoint server <port> [read-octets] [--layer=amqp|sasl]"
  IO.eprintln "       amqp-endpoint client <port> [read-octets] [--layer=amqp|sasl]"
  return (2 : UInt32)

/-- The layer this process offers, named by the switch: `--layer=amqp` or `--layer=sasl`. AMQP is the
default, and it is the one value the announced header and the connection's starting layer both come from,
because the header the shell builds is the one it starts the connection in. -/
def layerOf (text : String) : Except String SpecAMQP.Spec.Connection.Layer :=
  match text.toLower with
  | "amqp" => .ok .amqp
  | "sasl" => .ok .sasl
  | other => .error s!"layer must be amqp or sasl, not '{other}'"

/-- The `--layer=` switch, wherever it appears in the command line. The switch is removed before the
positional arguments are read, so `server 5672 --layer=sasl` and `server --layer=sasl 5672` are the same
command line; a misspelt layer is refused by name rather than silently defaulted, since the default is a
protocol decision and not a fallback. -/
def layerFlag (args : List String) : Except String SpecAMQP.Spec.Connection.Layer :=
  match args.find? (fun a => a.startsWith "--layer=") with
  | none => .ok .amqp
  | some a => layerOf (a.drop 8).toString

def main (args : List String) : IO UInt32 := do
  let layer ←
    match layerFlag args with
    | .ok chosen => pure chosen
    | .error message =>
      IO.eprintln s!"amqp-endpoint: {message}"
      return (2 : UInt32)
  match args.filter (fun a => !a.startsWith "--layer=") with
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
        announcedHeader layer
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
          let core ← serveConn listener (serverApp header) readOctets
          IO.println s!"endpoint: the connection ended in {core.conn.state.name}"
        finally
          listener.close
      else
        let core ← dial port (clientApp header) readOctets
        IO.println s!"endpoint: the connection ended in {core.conn.state.name}"
      return (0 : UInt32)
    catch e =>
      IO.eprintln s!"endpoint: {e}"
      return (1 : UInt32)
  | _ => usage
