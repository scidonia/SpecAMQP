/-
# The harness's wire discipline

Everything between the two loopback processes: the framing the client announces, the
two loops that make a byte stream out of the transport's partial operations, and the
argument validation both binaries share so they refuse the same things.

The loops matter more than the framing. `Transport.recv` promises at most
`maxOctets` and `Transport.send` promises only what the kernel took, so a caller
that assumes either is doing the whole job will silently truncate — which is the
fault this rung exists to make impossible. Both loops therefore *check* the
boundary's promises as they use them: a `recv` that returns more octets than it was
asked for, or a `send` that accepts nothing, fails loudly here rather than quietly
producing a shorter payload that a length-only comparison might still accept.

## Why the two processes must not read in identical windows

This is a fact about the experiment, not about the code, and it is here because it
was measured rather than reasoned: a planted control that swapped the first two
octets of *every* `recv` was **not** caught when the two processes happened to read
in the same windows. The fault is involutive — the server swapped the octets on the
way in and the client swapped them again on the way out, in the same places, so the
comparison saw the original payload and reported a match. It was caught only by the
multi-buffer case, where the two directions' read boundaries fall differently.

The repair is in `scripts/run-transport-loopback.sh`, which now gives the server and
the client different read sizes so the windows cannot coincide, and the control was
re-run to confirm that every non-empty case catches it with a named offset. The
lesson generalises past this harness: a mutant whose failure depends on symmetry
between two processes is a mutant whose failure cannot be attributed, and the
symmetric case has to be broken deliberately rather than left to chance.

(The other measurement a reader needs is in `Server.lean`: Lean's stdout is
block-buffered, so the readiness line must be flushed or a waiting runner waits
forever. Neither fact is visible in the code, which is why both are written down.)
-/

import Impl.Transport

namespace Loopback.Wire

open SpecAMQP.Impl.Transport

/-- The length header's width. -/
def headerOctets : Nat := 8

/-- An eight-octet big-endian length, which is all the harness needs a frame to
carry: the dialogue is a known byte string with a known length, so that the server
knows how much to read before echoing and neither side can deadlock waiting for the
other to finish writing. -/
def lengthHeader (count : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (fun i : Fin 8 => UInt8.ofNat ((count / 256 ^ (7 - i.val)) % 256)))

/-- Read back a length header. Rejects a header that is not exactly eight octets
rather than reading a prefix of it. -/
def headerLength (header : ByteArray) : Except String Nat :=
  if header.size != headerOctets then
    .error s!"length header must be {headerOctets} octets, not {header.size}"
  else
    let step (acc : Nat) (i : Nat) : Except String Nat :=
      match header[i]? with
      | some b => .ok (acc * 256 + b.toNat)
      | none => .error s!"unreadable length header at octet {i}"
    (List.range headerOctets).foldlM step 0

/-- Write every octet of `octets`, looping over as many `send` calls as the kernel
requires, and report how many that took: a shim that truncated would either need
more calls or accept fewer octets than asked, and both are visible in that number. -/
def sendAll (conn : Conn) (octets : ByteArray) : IO Nat := do
  let mut sent := 0
  let mut calls := 0
  while sent < octets.size do
    let accepted ← send conn (octets.extract sent octets.size)
    let taken := accepted.toNat
    calls := calls + 1
    if taken == 0 then
      throw (IO.userError s!"transport send accepted no octets at {sent} of {octets.size}")
    if sent + taken > octets.size then
      throw (IO.userError s!"transport send accepted {taken} octets at {sent} of {octets.size}")
    sent := sent + taken
  return calls

/-- Read exactly `count` octets in requests of at most `chunk`, looping over as many
`recv` calls as it takes, and report how many that took. A peer that closes before
`count` octets is an error naming how much arrived, not a short read: a truncated
transfer must not be able to look like a complete one. -/
def recvExactly (conn : Conn) (count chunk : Nat) : IO (ByteArray × Nat) := do
  let mut received := ByteArray.empty
  let mut calls := 0
  while received.size < count do
    let want := min chunk (count - received.size)
    let some part ← recv conn want.toUSize
      | throw (IO.userError s!"peer closed after {received.size} of {count} octets")
    if part.size > want then
      throw (IO.userError s!"transport recv returned {part.size} octets for a request of {want}")
    calls := calls + 1
    received := received ++ part
  return (received, calls)

/-- A decimal argument in `[low, high]`, so that a typo in the harness's command
line is refused by name rather than truncated to a port number that means something
else. -/
def boundedArg (name text : String) (low high : Nat) : Except String Nat :=
  match text.toNat? with
  | none => .error s!"{name} must be a decimal number, not '{text}'"
  | some n =>
    if n < low || n > high then
      .error s!"{name} must be between {low} and {high}, not {n}"
    else
      .ok n

/-- A port number, in the range a `UInt16` can carry and not below the reserved
range. -/
def portArg (text : String) : Except String UInt16 := do
  let n ← boundedArg "port" text 1024 65535
  return n.toUInt16

/-- A buffer size: at least one octet, and small enough that the harness's own
allocation cannot be the thing that fails. -/
def chunkArg (text : String) : Except String Nat :=
  boundedArg "chunk" text 1 (1024 * 1024)

end Loopback.Wire
