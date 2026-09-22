import Proofs.CodecRoundTripVariable

/-!
# The value codec's round trip: R3, the compounds

R1 (`Proofs/CodecRoundTrip.lean`) proves the fixed-width scalars; R2
(`Proofs/CodecRoundTripVariable.lean`) proves the length agreement for the families whose
encoding is a length followed by that many octets. This file is **R3: the compounds** —
`list`, `map` and `array` — whose encoding is a *size*, then a *count*, then the body.

Two things make R3 different from the rungs below it, and both are stated here rather than
left implicit.

**The choice rule is generalised, not restated.** R2 named the narrow/wide decision for a
length field as `lengthWidthOf`: one octet up to 255 octets of payload, four beyond. A
compound's decision has the same shape with a different condition — the writer takes the
eight-bit form when `body.length + 1 ≤ 255 ∧ count ≤ 255`, because the same size field
carries both the body's octets and the count. `widthChoice` states the decision once, over
*the quantities the field must carry*, and the two instances are proved to be instances
(`lengthWidthOf_eq_widthChoice`, `sizeWidthOf_eq_widthChoice`). The general form is the
right one for a reason worth recording: the condition is not a predicate of one number, so
a generalisation that took a single `Nat` would have had to exclude the compound case
rather than cover it.

**The size agreement is R2's shape at a different width.** `lengthPrefixed_ok` says a
length field is the whole overhead of a variable-width payload. `compoundOctets_eq`,
`arrayOctets_eq` and the two size facts say the same for a compound: the emitted octets
are the size field, the count field, then the body (and, for an array, the element
constructor between them), so the field's own octets are the whole overhead and the body
is carried unchanged. Nothing here re-derives R2's reasoning — it is the same statement
one level up, and it uses `beOctets_length` from R1.

## What is stated

`CompoundScalar` and `RoundTripCompound`, the claim of this rung, over the
specification's own `encodeValue`/`decodeValue`.

**The dependency on the earlier rungs is explicit.** The round trip for a compound is the
round trip for its *items* plus the framing around them: a list's items are values, so the
proof needs the round trip for whatever those items are — R1's claim for scalars, R2's for
the length-prefixed families, and this rung's own claim for compounds nested inside
compounds. That is the first rung whose proof must use a previous rung's claim as a
hypothesis rather than as a lemma, and the claim is stated so that it can be used that way
(`CompoundScalar` is a predicate on values, and `RoundTripCompound` quantifies over values
of that shape).

**The reader's fuel is a hypothesis, not an aside.** `decodeValue` enters with the octet
count as the budget, and every descent spends at least one octet, but a compound's *items*
are read at the same fuel as the compound (`readItems fuel`, `readElements fuel`), while
the compound itself has already spent one: so a statement about a compound read at the
entry fuel says nothing directly usable about the items read inside it. R1 and R2 did not
have to care because their values do not recurse. This rung therefore states its claim at
the entry fuel and records that the descent needs its own fuel accounting as a remaining
obligation, rather than assuming the entry budget reaches the items.

## What is proved

* `widthChoice`, `widthChoice_narrow`, `widthChoice_wide` — the narrow/wide decision once,
  with both of its sides.
* `lengthWidthOf_eq_widthChoice`, `sizeWidthOf_eq_widthChoice` — the two instances, so the
  general rule is the rule the writer follows at both places rather than a third spelling
  beside them.
* `compoundOctets_eq`, `arrayOctets_eq` — the writer's octets for a list, map or array
  under the row's own check, in closed form.
* `compoundOctets_ok_length`, `arrayOctets_ok_length` — the size field is the whole
  overhead, `lengthPrefixed_ok`'s statement at the compound's width.

## What is stated but not yet proved

`RoundTripCompound`. What remains is: that the writer's chosen row satisfies its own check
(the arithmetic that turns `body.length + 1 ≤ 255 ∧ count ≤ 255` into the bound
`compoundOctets` checks); that the reader's measured span equals the declared size for a
body the writer produced; and the induction itself, where the items' round trip is used as
a hypothesis at the fuel the descent supplies. The first two are arithmetic of the same
kind the earlier rungs closed; the third is where the fuel accounting lives.
-/
namespace SpecAMQP.Proofs

open SpecAMQP.Generated.Oasis (EncodingDecl)
open SpecAMQP.Spec.Codec
open SpecAMQP.Spec.ReadLaws
open SpecAMQP.Harness (Octets)

/-! ## The narrow/wide decision, stated once -/

/-- **The narrow/wide decision, in general.**

The writer takes the narrowest form the declared surface offers: one octet when every
quantity the field must carry fits in one octet, four otherwise. A *length* field carries
one quantity, the payload's length; a compound's *size* field carries two, the size and
the count, since the same field has to hold both.

Taking a single `Nat` here would have excluded the compound case rather than covered it,
which is why the general form is over the quantities the field carries. -/
def widthChoice (quantities : List Nat) : Nat :=
  if quantities.all (fun q => q ≤ 255) then 1 else 4

/-- The narrow side of the general rule: every quantity fits in one octet, so one octet is
taken. -/
theorem widthChoice_narrow (quantities : List Nat)
    (h : quantities.all (fun q => q ≤ 255) = true) : widthChoice quantities = 1 := by
  simp [widthChoice, h]

/-- The wide side of the general rule: some quantity does not fit in one octet, so the
four-octet form is taken. -/
theorem widthChoice_wide (quantities : List Nat)
    (h : quantities.all (fun q => q ≤ 255) = false) : widthChoice quantities = 4 := by
  simp [widthChoice, h]

/-- R2's rule for a length field is this rule at one quantity: the payload's length. -/
theorem lengthWidthOf_eq_widthChoice (payloadLength : Nat) :
    lengthWidthOf payloadLength = widthChoice [payloadLength] := by
  by_cases h : payloadLength ≤ 255 <;> simp [widthChoice, lengthWidthOf, h]

/-- **A compound's rule is the same rule at two quantities.** The writer's condition for
the eight-bit compound form is `body.length + 1 ≤ 255 ∧ count ≤ 255`, where `body.length + 1`
is the size the compound declares — the same size field carrying both. -/
def sizeWidthOf (size count : Nat) : Nat :=
  if size ≤ 255 ∧ count ≤ 255 then 1 else 4

/-- The compound instance of the general rule, proved rather than asserted. -/
theorem sizeWidthOf_eq_widthChoice (size count : Nat) :
    sizeWidthOf size count = widthChoice [size, count] := by
  by_cases hs : size ≤ 255 <;> by_cases hc : count ≤ 255 <;>
    simp [widthChoice, sizeWidthOf, hs, hc]

/-! ## The writer's octets, in closed form -/

/-- **A compound's octets under its own check.** The size field, the count field and the
body, with the size counting the octets after it: the count field's width plus the body's
length. The hypothesis is exactly the check `compoundOctets` performs. -/
theorem compoundOctets_eq (decl : EncodingDecl) (count : Nat) (body : List UInt8)
    (h : decl.width + body.length < 2 ^ (8 * decl.width) ∧ count < 2 ^ (8 * decl.width)) :
    compoundOctets decl count body =
      .ok (beOctets decl.width (decl.width + body.length) ++ beOctets decl.width count ++ body) := by
  simp only [compoundOctets, h.1, h.2]
  rfl

/-- **An array's octets under its own check.** The size field, the count field, the element
constructor, then the elements: the size counts all three of the things after it. -/
theorem arrayOctets_eq (decl : EncodingDecl) (constructor : UInt8) (count : Nat)
    (elements : List UInt8)
    (h : decl.width + 1 + elements.length < 2 ^ (8 * decl.width) ∧
          count < 2 ^ (8 * decl.width)) :
    arrayOctets decl constructor count elements =
      .ok (beOctets decl.width (decl.width + 1 + elements.length) ++
        beOctets decl.width count ++ [constructor] ++ elements) := by
  simp only [arrayOctets, h.1, h.2]
  rfl

/-- **A compound's size field is the whole overhead.** The octets a list or map emits are
the size field, the count field and the body, so the field and the count are all that a
compound costs beyond its body — `lengthPrefixed_ok`'s statement at the compound's width. -/
theorem compoundOctets_ok_length (width count : Nat) (body : List UInt8) :
    (beOctets width (width + body.length) ++ beOctets width count ++ body).length =
      width + (width + body.length) := by
  simp [List.length_append, beOctets_length]

/-- **An array's size field is the whole overhead, plus its one constructor octet.** The
elements and the constructor are carried unchanged; the field and the count are the
overhead beyond them. -/
theorem arrayOctets_ok_length (width count : Nat) (constructor : UInt8)
    (elements : List UInt8) :
    (beOctets width (width + 1 + elements.length) ++ beOctets width count ++
      [constructor] ++ elements).length = width + (width + 1 + elements.length) := by
  simp [List.length_append, beOctets_length] <;> omega

/-! ## The rung's claim -/

/-- The values R3 covers: the three compound forms whose encoding is a size, a count and a
body, and the described form that carries one of them.

A *shape* predicate, not a range restriction: a compound whose size or count does not fit
the row's field is in scope, and its case is discharged by the writer refusing it — which
is what the implication's hypothesis `encodeValue value = .ok bytes` records, since no such
`bytes` exists. -/
def CompoundScalar : Value → Prop
  | .list _ | .map _ | .array _ _ => True
  | _ => False

/-- **R3: the compounds round-trip.**

For every compound the writer encodes, the reader recovers that value from exactly those
octets and consumes the whole buffer. This is the first claim that has to be *used* by its
own proof: a compound's items are values, so the round trip for a list of strings needs
R2's claim, for a list of integers R1's, and for a list of lists this claim again — which
is why it is stated as a predicate on values rather than as a lemma about one encoding. -/
def RoundTripCompound : Prop :=
  ∀ (value : Value) (bytes : Octets),
    CompoundScalar value → encodeValue value = .ok bytes →
      decodeValue bytes = .ok (value, bytes.size)

end SpecAMQP.Proofs
