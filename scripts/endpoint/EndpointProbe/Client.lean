/-
# The endpoint shell's harness peer

The shell's own correctness is three obligations its docstring states and no proof in this tree covers —
it loops on a short read, it writes exactly what the core returns and all of it, and it treats `recv`'s
`none` as the peer's orderly close. `scripts/run-endpoint-shell.sh` is what *forces* them, and it needs one
thing this repository's shipped process does not have: an application that asks the shell to write more
than one `send` will accept, so that the write loop is exercised rather than argued.

This is that application, on both sides of one connection. The **server** side sends an `open` declaring a
large `max-frame-size`; the **client** side then sends a ~3 kB `open`, which the specification permits only
because it has seen that declaration — the core refuses to send a frame above the peer's a priori limit
(`512`, `MIN-MAX-FRAME-SIZE`), and a probe that skipped the declaration would be measuring a refusal
instead of a write. The binary links the *control* shim (`scripts/loopback/mutants/shim_controls.c`) so
that a write is offered to the kernel in 1024-octet pieces whatever the kernel would have taken, and it
uses the shipped loops — `Shell.Driver.sendAll`, `readOnce`, `pump`, `runConnection`, `dial`, `serveConn` —
because they are the same functions the endpoint process runs.

It lives outside `lean/Shell/` so that no test-only policy is shipped: the shell is parameterised by `App`
precisely so that a test application is a different value rather than a different shell.
-/

import Shell.Driver

namespace EndpointProbe

open SpecAMQP.Shell
open SpecAMQP.Harness (Octets)

/-- The `container-id` the probe's frame carries: long enough that the frame is several times the control
shim's per-`send` cap, which is what makes `sendAll` loop. -/
def containerId : String := String.ofList (List.replicate 3000 'x')

/-- An `open` built by the specification's own frame writer: descriptor 16 is the `open` performative the
generated tables declare, `container-id` is the one field its surface makes mandatory, and the limits are
declared as the caller asks. -/
def openWith (containerId : String) (maxFrameSize channelMax : Nat) : Except String Octets :=
  SpecAMQP.Spec.Frame.encodeFrame
    { doff := 2, frameType := SpecAMQP.Spec.Frame.FrameType.amqp, channel := 0, extended := #[],
      body := some (.described (.ulong 16)
        (.list [.string containerId, .null, .uint maxFrameSize, .ushort channelMax])),
      payload := #[] }

/-- The large frame the client sends, and the declaration the server sends first. -/
def bigOpen : Except String Octets := openWith containerId 65535 65535

/-- The declaration the probe server announces: a short frame, so it passes the a priori limit, and a
`max-frame-size` large enough that the peer's write of `bigOpen` is permitted. -/
def permission : Except String Octets := openWith "probe" 65535 65535

/-- The **client** application: send the large frame once the peer has declared a limit that permits it.
The condition is the protocol's own — the frame is sent when the partner's `open` has said the peer accepts
frames that large, which is the one thing that makes the write legal rather than refused. -/
def clientApp (frame : Octets) : App :=
  fun core _ =>
    if core.conn.remoteLimits.maxFrameSize ≥ frame.size then
      { octets := #[frame], done := true }
    else
      { octets := #[], done := false }

/-- The **server** application: declare the large limit once both headers have been exchanged, and then
wait for the peer to close. -/
def serverApp (declaration : Octets) : App :=
  fun core _ =>
    if core.conn.state == SpecAMQP.Spec.Connection.State.hdrExch then
      { octets := #[declaration], done := false }
    else
      { octets := #[], done := false }

end EndpointProbe

open EndpointProbe SpecAMQP.Shell

def usage : IO UInt32 := do
  IO.eprintln "usage: amqp-endpoint-probe server|client <port> [read-octets]"
  return (2 : UInt32)

/-- The process: run the shipped shell with the probe's application on either side of one connection. Exit
statuses follow the endpoint process's convention (`0` ran, `1` the connection failed or the
specification's writer refused the probe's frame, `2` the command line is not this programme's). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | role :: portText :: rest =>
    if role != "server" && role != "client" then
      IO.eprintln s!"endpoint-probe: '{role}' is not a role this programme has"
      return (2 : UInt32)
    let port ←
      match portOf portText with
      | .ok p => pure p
      | .error message =>
        IO.eprintln s!"endpoint-probe: {message}"
        return (2 : UInt32)
    let readOctets ←
      match rest with
      | [] => pure defaultReadOctets
      | [text] =>
        match readOctetsOf text with
        | .ok n => pure n
        | .error message =>
          IO.eprintln s!"endpoint-probe: {message}"
          return (2 : UInt32)
      | _ =>
        IO.eprintln "endpoint-probe: read-octets must be one decimal number"
        return (2 : UInt32)
    let frame ←
      if role == "server" then
        match permission.toOption with
        | some f => pure f
        | none =>
          IO.eprintln "endpoint-probe: the specification's writer refuses the probe's declaration"
          return (1 : UInt32)
      else
        match bigOpen.toOption with
        | some f => pure f
        | none =>
          IO.eprintln "endpoint-probe: the specification's writer refuses the probe's frame"
          return (1 : UInt32)
    let header ←
      try
        announcedHeader
      catch e =>
        IO.eprintln s!"endpoint-probe: {e}"
        return (1 : UInt32)
    try
      if role == "server" then
        -- the listener is bound *before* the readiness line, so a harness that reads it knows the port
        -- exists: a line printed before the bind would let a collision be read as readiness
        let listener ← listenOn port
        try
          IO.println s!"probe: listening port={port} read-octets={readOctets.toNat} \
            frame-of={frame.size} octets"
          (← IO.getStdout).flush
          let core ← serveConn listener header (serverApp frame) readOctets
          IO.println s!"probe: the connection ended in {core.conn.state.name}"
        finally
          listener.close
      else
        IO.println s!"probe: client, frame of {frame.size} octets, read-octets={readOctets.toNat}"
        (← IO.getStdout).flush
        let core ← dial port header (clientApp frame) readOctets
        IO.println s!"probe: the connection ended in {core.conn.state.name}"
      return (0 : UInt32)
    catch e =>
      IO.eprintln s!"endpoint-probe: {e}"
      return (1 : UInt32)
  | _ => usage
