import Spec.ReadLaws
import Proofs.CodecRoundTrip
import Proofs.ExceptMap

/-!
# The value codec's round trip: R2, the variable-width families

R1 (`Proofs/CodecRoundTrip.lean`) proves the fixed-width scalars, where no length field is
involved and a field's size is the row's declared width. This file is **R2: the families
whose encoding is a length followed by that many octets** — `string`, `symbol` and
`binary`, in both the 8-bit and 32-bit forms the declared surface offers.

What the field law does for a fixed width, the length agreement does for a variable one:
the writer emits the length of the payload it wrote and then the payload, the reader reads
a length and then that many octets, and the round trip is the two agreeing *and* the
narrow/wide choice being a function of the payload the writer actually has. That last part
is where `NarrowestEncoding` first bites, so the choice is stated here as `lengthWidthOf`
rather than left inside the encoder's code: the width is one octet up to 255 octets of
payload and four beyond, because a one-octet length field carries `n` exactly when
`n < 256`.

## What is stated

`RoundTripVariableWidth` is the rung's claim, over the specification's own
`encodeValue`/`decodeValue`, for every value in the three families; `VariableWidthScalar`
is its domain. Like R1's, the claim is a `def … : Prop` and not a `theorem`: a statement
is not a claim.

## What is proved

* `lengthWidthOf_narrow`, `lengthWidthOf_wide` — the choice rule at its two sides, so the
  rule is a fact about the rung rather than a comment about the encoder.
* `lengthPrefixed_eq` — the writer's half of the length agreement: a payload whose length
  fits the row's field is written as the *narrowest* big-endian field carrying that
  length, then the payload unchanged.
* `lengthPrefixed_ok` — the emitted octets are exactly the length field plus the payload,
  so a length field costs the payload's own octets and nothing else.
* `takeBe_beOctets` — the reader's half: a cursor over `prefix ++ beOctets width n`, at
  the offset right after `prefix`, reads back exactly `n`. It composes the two facts R1's
  prerequisites established — the consumed-slice identity and the field's value law — and
  is what makes a length field a *readable* field rather than a run of octets the reader
  happens to step over.

## What is stated but not yet proved

`RoundTripVariableWidth` itself. What remains is the composition at each family's own
step: that the writer's choice of row agrees with `lengthWidthOf` on the payload it has,
that the reader's length field feeds back into how many octets it then takes, and that the
recovered payload is the writer's payload — under `utf8Of` for the two text families. No
obstruction is known in any of the three; each is a step of the same kind as R1's, over
the branch the writer's own success has already selected.
-/
namespace SpecAMQP.Proofs

open SpecAMQP.Generated.Oasis (EncodingDecl)
open SpecAMQP.Spec.Codec
open SpecAMQP.Spec.ReadLaws
open SpecAMQP.Harness (Octets)

/-! ## The rung's claim -/

/-- The values R2 covers: the three families whose encoding is a length followed by that
many octets, in both the 8-bit and 32-bit forms.

A *shape* predicate, not a range restriction: a payload too long for even the 32-bit form
is in scope, and its case is discharged by the writer refusing it — which is exactly what
the implication's hypothesis `encodeValue value = .ok bytes` records, since no such
`bytes` exists. -/
def VariableWidthScalar : Value → Prop
  | .string _ | .symbol _ | .binary _ => True
  | _ => False

/-- **R2: the variable-width families round-trip.**

For every value in the three families the writer encodes, the reader recovers that value
from exactly those octets and consumes the whole buffer. Where the writer refuses — a
payload that no declared width carries — there is nothing to claim and the implication is
vacuous. -/
def RoundTripVariableWidth : Prop :=
  ∀ (value : Value) (bytes : Octets),
    VariableWidthScalar value → encodeValue value = .ok bytes →
      decodeValue bytes = .ok (value, bytes.size)

/-! ## The narrow/wide choice, stated -/

/-- **The narrow/wide choice for a variable-width family.** The width of the length field
is the narrowest the declared surface offers that can carry the payload's length: one
octet up to 255 octets of payload, four beyond. A one-octet field carries `n` exactly when
`n < 256`, which is the same condition written as `n ≤ 255`.

This is `NarrowestEncoding` in its first instance. The encoder inlines this rule at each
of the three families — `string` and `symbol` from `toUTF8.toList`'s length, `binary` from
`payload.size` — and naming it makes the rule part of the rung, so a proof about the round
trip can ask what the choice is instead of re-deriving it from whichever branch it
unfolded. -/
def lengthWidthOf (payloadLength : Nat) : Nat :=
  if payloadLength ≤ 255 then 1 else 4

/-- The narrow side of the rule: a payload of at most 255 octets takes a one-octet length
field. -/
theorem lengthWidthOf_narrow (payloadLength : Nat) (h : payloadLength ≤ 255) :
    lengthWidthOf payloadLength = 1 := by
  simp [lengthWidthOf, h]

/-- The wide side of the rule: a payload of 256 octets or more takes a four-octet length
field. -/
theorem lengthWidthOf_wide (payloadLength : Nat) (h : 256 ≤ payloadLength) :
    lengthWidthOf payloadLength = 4 := by
  simp [lengthWidthOf, Nat.not_le.mpr h]

/-- The two spellings of a field's bound agree: `2 ^ (8 * width)`, as `filled` states it,
is `256 ^ width`, as the field's value law states it. -/
theorem two_pow_eight_mul (width : Nat) : 2 ^ (8 * width) = 256 ^ width := by
  rw [Nat.pow_mul, show (2 : Nat) ^ 8 = 256 by decide]

/-! ## The writer's half of the length agreement -/

/-- **The length the writer emits is the length of the payload it wrote.**

A payload whose length fits the row's field is written as the narrowest big-endian field
carrying that length, followed by the payload unchanged. The hypothesis is exactly what
`filled` requires, and what the writer's own success supplies: where the length does not
fit, there are no octets to make a claim about. -/
theorem lengthPrefixed_eq (decl : EncodingDecl) (payload : List UInt8)
    (h : payload.length < 2 ^ (8 * decl.width)) :
    lengthPrefixed decl payload = .ok (beOctets decl.width payload.length ++ payload) := by
  simp only [lengthPrefixed, filled, h, ↓reduceIte]
  rfl

/-- **A length field costs the payload's own octets and nothing else.**

The writer's octets under a length-prefixed row are the length field plus the payload, so a
length field's own octets are the whole overhead and the payload is carried unchanged: the
octets a successful write emits are the row's width plus the payload's length long.

This *subsumes* the earlier form of this fact, which spoke about the list
`beOctets decl.width payload.length ++ payload` rather than about the writer's own output:
that list is what `lengthPrefixed_eq` identifies the output with, so it follows from this at
`out :=` that list. There is one statement here rather than two for that reason — the
success form is the claim, and the octets form is what it says about the only octets the
writer can have produced. -/
theorem lengthPrefixed_ok (decl : EncodingDecl) (payload : List UInt8) (out : List UInt8)
    (h : lengthPrefixed decl payload = .ok out) :
    out.length = decl.width + payload.length := by
  cases hf : filled decl.width payload.length with
  | error e => simp [lengthPrefixed, hf] at h
  | ok field =>
    have hfield : field = beOctets decl.width payload.length := by
      by_cases hfit : payload.length < 2 ^ (8 * decl.width)
      · have h' := hf
        simp [filled, hfit] at h'
        exact h'.symm
      · simp [filled, hfit] at hf
    simp only [lengthPrefixed, hf, hfield] at h
    rw [← Except.ok.inj h]
    simp [List.length_append, beOctets_length]

/-! ## The reader's half of the length agreement -/

/-- **The length field reads back.**

A cursor whose buffer is `prefix` followed by the writer's length prefix
`beOctets width n`, positioned at the offset just after `prefix`, reads exactly `n` — the
value the writer wrote, in the field the writer chose, at the position the writer put it.

This composes the two facts about the reader: the consumed-slice identity
(`extract_toList_eq_drop_take`) puts the octets the reader took into the writer's own list
vocabulary, and the field's value law (`bigEndianFieldValue`) values them. The buffer's
list and the cursor's position are hypotheses rather than a constructed array so that the
statement needs no conversion lemma: the composition site already has both. -/
theorem takeBe_beOctets (width n : Nat) (header : List UInt8) (c : Cursor)
    (hlist : c.data.toList = header ++ beOctets width n) (hpos : c.pos = header.length)
    (hfit : n < 2 ^ (8 * width)) :
    takeBe width c = .ok (n, (⟨c.data, c.pos + width⟩ : Cursor)) := by
  have hsize : c.pos + width ≤ c.data.size := by
    simp [← Array.length_toList, hlist, hpos, List.length_append, beOctets_length]
  have hvalue : beValue (beOctets width n) = n := by
    show (beOctets width n).foldl (fun acc byte => acc * 256 + byte.toNat) 0 = n
    rw [bigEndianFieldValue width n,
      Nat.mod_eq_of_lt (by rw [← two_pow_eight_mul]; exact hfit)]
  rw [takeBe_eq_fold width c hsize, hlist, hpos, List.drop_left,
    List.take_of_length_le (by simp [beOctets_length]), hvalue]

end SpecAMQP.Proofs
