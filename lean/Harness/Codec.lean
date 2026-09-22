import Lean.Data.Json

/-!
# The interface a corpus runner needs from a codec

Two artefacts sit either side of the corpus — the reference implementation and the
specification — and they must not share a value representation, or agreement
between them would say nothing. What they may share is the *harness*: the corpus
vocabulary, the hex rendering, and the verdict logic. This file is that boundary.

A codec converts octets to a corpus value and back, using the vocabulary defined
by `tests/contracts/value-vector.schema.json`. Everything else — running vectors,
comparing expectations, reporting verdicts — is the runner's business, and is
therefore identical for both artefacts by construction.
-/

namespace SpecAMQP.Harness

abbrev Octets := Array UInt8

/-- Octets to a corpus value, and back, for one artefact.

`decode` returns the value and how many octets it consumed, so a runner can
require that a vector's input was consumed entirely rather than silently
accepting a prefix.
-/
structure Codec where
  /-- The artefact's name, quoted in verdict reports. -/
  name : String
  /-- Octets to a corpus value: `Except` carrying why it failed. -/
  decode : Octets → Except String (Lean.Json × Nat)
  /-- A corpus value back to octets. -/
  encode : Lean.Json → Except String Octets

end SpecAMQP.Harness
