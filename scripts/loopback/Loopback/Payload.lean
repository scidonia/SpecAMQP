/-
# R1's known byte string

The payload the loopback exchanges is generated, not typed in, and it is
position-dependent: octet `i` is `i % 251`. That is what makes a silent shim fault
visible. A buffered or truncated transfer loses *values*, a reordered one puts the
right values at the wrong places, and a duplicated one repeats a window — and
against `i % 251` every one of those differs from the expectation at the first
affected position rather than only at its length. A prime period also means no
sub-block repeats, so a shifted stream cannot resynchronise by accident.

The comparison reports the first difference with both octets and the offset,
because "the payload did not match" is not a report: the offset is what says
whether the fault was a truncation (a difference inside the received length), a
reordering (a difference where two windows swapped) or a spurious extra read.
-/

namespace Loopback.Payload

/-- Octet `i` of the known byte string. -/
def octetAt (i : Nat) : UInt8 := UInt8.ofNat (i % 251)

/-- The known byte string of `n` octets. -/
def ofLength (n : Nat) : ByteArray :=
  ByteArray.mk ((Array.range n).map octetAt)

/-- Two hexadecimal digits for one octet, for the difference report. -/
def hexOctet (b : UInt8) : String :=
  let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]

/--
`ok` if `actual` is `expected` octet for octet, and otherwise a diagnostic naming
the first place they differ — the length first, since a transfer that ended early
has no "first differing octet" to report.
-/
def compare (expected actual : ByteArray) : Except String Unit := Id.run do
  if expected.size != actual.size then
    return .error s!"length differs: expected {expected.size} octets, received {actual.size}"
  for i in [0 : expected.size] do
    let some want := expected[i]? | return .error s!"unreadable expectation at {i}"
    let some got := actual[i]? | return .error s!"unreadable result at {i}"
    if want != got then
      return .error s!"octet {i} differs: received {hexOctet got}, expected {hexOctet want}"
  return .ok ()

end Loopback.Payload
