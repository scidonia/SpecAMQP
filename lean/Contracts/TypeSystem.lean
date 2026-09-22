import Spec.Value

/-!
# Acceptance declarations for the AMQP 1.0 type system

This module names the claims the specification makes about the encoding grammar,
so a reviewer reads the approved statement here rather than reconstructing it
from the proof file. It follows the pattern set by TemperMint's conformance
declarations: the contract states the exact proposition, and the acceptance
theorem applies the proof at exactly that type.

Every declaration here is about the *specification*: what the OASIS artifacts
require, formalised. Nothing here refers to an implementation.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Value

/-- Approved claim for the constructor grammar (Part 1).

Reading it: the grammar's reserved octets are exactly `%x01-3F`; every octet from
`%x40` to `%xFF` lies in a category the grammar names, so there is no unassigned
hole; the twelve escape octets the grammar reserves for future formats are
unassigned in the declared surface and still carry their range's category; and
every encoding the artifact declares follows the category and width its range
gives it. -/
def ConstructorGrammarConforms : Prop :=
  reservedCodes = (List.range 0x3F).map (fun offset => offset + 1) ∧
  escapeOctets.all (fun code => (Generated.Oasis.encodingOf code).isNone) = true ∧
  escapeOctets.all (fun code => classify code != Constructor.reserved) = true ∧
  Generated.Oasis.encodings.all followsRange = true ∧
  (List.range 256).filter (fun code => classify code != Constructor.reserved) =
    [0x00] ++ (List.range 0xC0).map (fun offset => offset + 0x40)

/-- Acceptance: the grammar claims hold at exactly the type above. -/
theorem constructor_grammar_public : ConstructorGrammarConforms :=
  ⟨reservedCodes_eq, escapeOctets_unassigned, escapeOctets_in_range,
   encodings_follow_range, formatCodeRanges_exact⟩

end SpecAMQP.Contracts
