import Generated.Oasis.Encodings
import Spec.Codec
import Spec.Value

/-!
# The specification codec's laws (S1 acceptance propositions)

Two laws are stated here, and they are *stated* rather than claimed: the
declarations below are propositions, and no theorem asserts them yet. Until a
proof exists, the evidence in force for the specification codec is the corpus
(67,124 vectors through the executable, §13 S1) and the differential contract
against the independently written reference. A `sorry` in this file would be a
claim nobody proved, which is why the gate in `tests/contracts/s1_proof_integrity.sh`
refuses one and these are propositions rather than theorems.

Why the laws are stated in advance of their proofs: they are the contract the
proof work implements, and stating them now pins what "round trip" and "narrowest
form" mean before anybody writes a lemma shaped to whatever was easy.

A note on what the propositions do *not* say. Neither of them mentions the OASIS
tables: the classification and the declared surface have their own contract
(`Contracts.TypeSystem`, where the specification's constructor grammar is proved
equal to the artifact's encoding table). These two are about the codec built on
that surface — that reading recovers what writing produced, and that writing never
spends more octets than an accepted encoding of the same value.
-/

namespace SpecAMQP.Contracts

open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Spec.Codec (decodeValue encodeValue)
open SpecAMQP.Harness (Octets)

/-- Round trip on the writer's domain: every value the writer encodes is read back
byte for byte, consuming the whole buffer.

The hypothesis is a statement about the writer, not a restriction on the value:
wherever `encodeValue` produces octets at all, the reader recovers exactly that
value from exactly those octets. Where the writer refuses (a value outside the
surface the tables declare), there is nothing to claim, and the reader refusing
those same bytes is also in scope because the writer never produced them.

The consumed count matters as much as the value: an encoding that decoded to the
right value while leaving trailing octets would satisfy a weaker statement and
would be wrong, since an AMQP frame's payload boundary is exactly this. -/
def RoundTripOnEncodedValues : Prop :=
  ∀ (value : Value) (bytes : Octets),
    encodeValue value = .ok bytes →
    decodeValue bytes = .ok (value, bytes.size)

/-- Canonicality: the writer never spends more octets than an accepted encoding of
the same value.

Stated over buffers rather than over values because canonicality is a statement
about *which octets are chosen*, and a value can have many accepted encodings (a
`str32` with a three-octet payload decodes to the same string as the `str8` form).
The law says the writer's choice is never longer than what the reader accepted:
for a buffer that decodes in full, the writer's encoding is at most that size. The
narrowest-form rule of Part 1 — narrow whenever the value and length fit, wide
otherwise — is what makes this true, and the corpus asserts it directly on the
vectors marked `canonical: true`, where the writer's output must equal the input
bytes exactly. -/
def NarrowestEncoding : Prop :=
  ∀ (bytes : Octets) (value : Value) (consumed : Nat),
    decodeValue bytes = .ok (value, consumed) →
    consumed = bytes.size →
    ∃ canonical, encodeValue value = .ok canonical ∧ canonical.size ≤ bytes.size

-- The acceptance declaration is deliberately absent rather than stubbed. It becomes
-- this, with a proof and no `sorry`, once `SpecAMQP.Proofs.codec_laws` exists:
--
--   theorem codec_laws : RoundTripOnEncodedValues ∧ NarrowestEncoding :=
--     ⟨SpecAMQP.Proofs.codec_round_trip, SpecAMQP.Proofs.codec_narrowest⟩
--
-- A `def … : Prop` is a contract anybody can read; a `theorem … := by sorry` would
-- be a claim nobody proved, and the trust scan would have to catch it as damage
-- rather than the file announcing it.

end SpecAMQP.Contracts
