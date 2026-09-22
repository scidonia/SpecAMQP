import Spec.Codec

/-!
# The value codec's round trip: R1, the fixed-width scalars

`lean/Contracts/Codec.lean` states `RoundTripOnEncodedValues` — for every value the
writer encodes, the reader recovers that value from exactly those octets, consuming all
of them — as a proposition, deliberately unproved, so that nobody mistakes the corpus
for a proof. The proof is split into rungs so that progress is visible rung by rung, and
this file is **R1: the fixed-width scalars**, where no length field is involved and the
claim reduces to byte-level lemmas.

## What is stated

`RoundTripFixedWidth` is the rung's claim, stated over the specification's own
`encodeValue`/`decodeValue` and *not* over the reference implementation's: for every
value whose body is one fixed-width scalar — null, boolean, the eight integer widths
including the small and zero forms, `float`, `double`, the three decimals, `uuid`,
`timestamp` and `char` — if the writer encodes it then the reader recovers it from those
octets, having consumed the whole buffer.

It is a `def … : Prop` rather than a `theorem`, for the same reason the acceptance
declaration is: a statement is not a claim, and a `theorem … := by sorry` would be a
claim nobody proved. The theorems below are the parts of it that are proved.

## What is proved

* `go_length`, `beOctets_length` — the writer's big-endian loop writes exactly the width
  it is handed, so a field's octet count is the row's declared width. This is what makes
  the reader's `takeBytes` take exactly the right number of octets out of the writer's
  own output, and it is the size half of the composition.

## What is stated but not yet proved, with the obstruction named

Two obligations stand between the lemmas above and the composition, and neither is a
`sorry` dressed up.

1. **The field's value** (`BigEndianFieldValue`, `FieldValueRoundTrip`). The loop writes
   `n % 256` into its first octet, so a field of `width` octets carries `n % 256 ^ width`
   and no more — the same bound `filled` checks, so `filled`'s success would turn the
   modulo into an identity. The induction is routine and its hypothesis goes through;
   what the core library does not have is the modular step

   ```
   n % 256 ^ (k + 1) = n % 256 + 256 * ((n / 256) % 256 ^ k)
   ```

   — the law that a two-digit number's remainder is its low digit plus `256` times the
   remainder of its high part. Core offers the self-modulus forms
   (`Nat.add_mul_mod_self_left`, `Nat.mul_mod_mul_left`, `Nat.div_add_mod`) but not this
   composite one, and the goal reached without it is recorded with the statement so the
   next step is a `Nat` lemma rather than a guess. The route that works is the one this
   was attempted along: decompose `n = 256 * (n / 256) + n % 256` and
   `n / 256 = 256 ^ k * ((n / 256) / 256 ^ k) + (n / 256) % 256 ^ k` with
   `Nat.div_add_mod`, turn `256 ^ (k + 1)` into `256 * 256 ^ k` with `pow_succ` and a
   commutation, distribute, strip the multiple of the modulus with `Nat.mul_add_mod`,
   and close with `Nat.mod_eq_of_lt` against
   `256 * ((n / 256) % 256 ^ k) + n % 256 < 256 * 256 ^ k`. Note also that `norm_num`
   is a Mathlib tactic and is *not* available to this closure: `0 < 256` has to be a
   `decide`, and the bound otherwise stays in `Nat`/`omega` territory.

2. **The reader's slice arithmetic.** `takeBytes` slices with `Array.extract`, and a
   payload's length is the field's symbolic width, so the composition needs the fact
   that dropping the constructor octet and taking `width` octets from the writer's own
   output yields exactly the field. `Array.toList_extract` and `Array.foldl_toList` —
   both in `Init.Data.Array.Lemmas`, so no new dependency — reduce that to a `List`
   statement about `beOctets width n`, which `beOctets_length` sizes and
   `BigEndianFieldValue` values. It is bookkeeping at the `Array`/`List` boundary rather
   than a mathematical gap.

3. **The two's-complement pair**, separate from both: `twosComplement` and
   `signedOfOctets` are inverses on the half-open range, and the boundary arithmetic
   around `Int`'s modulo is the remaining work for `byte`, `short`, `int`, `long` and
   `timestamp`.

A rung proved only for `fuel = bytes.size` would have no usable induction hypothesis, so
the composition is to be proved in the general form the reader admits — "a value read
with at least the remaining octets as fuel consumes exactly the value's octets" — and
the entry statement derived from it by instantiating the fuel at the buffer's length.
That general form is what the frame proofs need from the value layer too, which is why
it belongs here once rather than per rung.

## The table facts the composition will unfold

The reader's second question is which type a constructor octet selects, and the answer
is the generated table, not a list in this file:

```text
dataDecl 0x50    = .ok ⟨0x50, none, .fixed, 1, "ubyte", "8-bit unsigned integer"⟩
rowOf "ubyte" 1  = .ok ⟨0x50, none, .fixed, 1, "ubyte", "8-bit unsigned integer"⟩
```

Both reduce — the table is a committed list and the lookups are computable — so the
composition unfolds them rather than citing them. They are recorded here as named
evaluation facts because a `decide` over them wants a `Decidable (Except String
EncodingDecl)` the goal does not synthesize; `simp`/`rfl` on the concrete lookup is the
route that works, which is worth knowing before someone reaches for `native_decide`.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Spec.Codec
open SpecAMQP.Harness (Octets)

/-! ## The rung's claim -/

/-- The values R1 covers: one fixed-width scalar, with no length field anywhere in its
encoding.

A *shape* predicate, not a range restriction: a `ubyte` above 255 is in scope, and its
case is discharged by the writer refusing it — which is exactly what the implication's
hypothesis `encodeValue value = .ok bytes` records, since no such `bytes` exists. -/
def FixedWidthScalar : Value → Prop
  | .null | .boolean _ => True
  | .ubyte _ | .ushort _ | .uint _ | .ulong _ => True
  | .byte _ | .short _ | .int _ | .long _ => True
  | .float _ | .double _ | .decimal32 _ | .decimal64 _ | .decimal128 _ => True
  | .uuid _ | .timestamp _ | .char _ => True
  | _ => False

/-- **R1: the fixed-width scalars round-trip.**

For every fixed-width scalar the writer encodes, the reader recovers that value from
exactly those octets and consumes the whole buffer. Where the writer refuses — a payload
wider than its field, or a raw payload whose length is not the row's width — there is
nothing to claim and the implication is vacuous. -/
def RoundTripFixedWidth : Prop :=
  ∀ (value : Value) (bytes : Octets),
    FixedWidthScalar value → encodeValue value = .ok bytes →
      decodeValue bytes = .ok (value, bytes.size)

/-! ## The writer's big-endian field, sized -/

/-- The writer's big-endian loop writes exactly the width it is handed.

Stated about `beOctets.go` — the `let rec` inside `beOctets`, reachable by name — because
the width is what an induction over the loop can see, and because the lemmas that build
on it want the loop rather than its reversal. -/
theorem go_length : ∀ (width n : Nat), (beOctets.go width n).length = width := by
  intro width
  induction width with
  | zero => intro n; simp [beOctets.go]
  | succ k ih => intro n; simp [beOctets.go, ih]

/-- A big-endian field is as long as the row's declared width, so the reader's
`takeBytes` takes exactly the field and nothing else. -/
theorem beOctets_length (width n : Nat) : (beOctets width n).length = width := by
  simp [beOctets, go_length]

/-! ## The writer's big-endian field, valued -/

/-- The modular step the field-value induction needs: the remainder of a number taken
modulo `256 * b` is its low octet plus `256` times the remainder of its high part.

No induction: `Nat.div_add_mod` at the truncated modulus gives
`256 * ((n % (256 * b)) / 256) + (n % (256 * b)) % 256 = n % (256 * b)`, and the two
truncation facts `Nat.mod_mul_right_div_self` and `Nat.mod_mul_right_mod` turn that into
`256 * (n / 256 % b) + n % 256 = n % (256 * b)`. Without this, the induction over the
width reaches for an identity the core `Nat` library does not name. -/
theorem mod_mul_base (n b : Nat) : n % (256 * b) = n % 256 + 256 * (n / 256 % b) := by
  have h := Nat.div_add_mod (n % (256 * b)) 256
  rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod] at h
  omega

/-- The writer's big-endian loop, valued: folding its output from the right with the
reader's big-endian accumulator returns the number written into the field, modulo the
field's own bound `256 ^ width`. Each octet the loop wrote contributes its own digit,
which is exactly what the induction's step needs once `mod_mul_base` supplies the
carry. -/
theorem go_foldr_value : ∀ (width n : Nat),
    (beOctets.go width n).foldr (fun byte acc => byte.toNat + 256 * acc) 0 = n % 256 ^ width := by
  intro width
  induction width with
  | zero => intro n; simp [beOctets.go, Nat.mod_one]
  | succ k ih =>
    intro n
    rw [beOctets.go, List.foldr_cons, ih (n / 256)]
    have byteVal : (UInt8.ofNat (n % 256)).toNat = n % 256 := by simp
    rw [byteVal]
    have powComm : 256 ^ (k + 1) = 256 * 256 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [powComm, mod_mul_base n (256 ^ k)]

/-- The field's value, modulo the widest value a field of that width can hold.

Folding the written octets most significant first — which is how the reader's `takeBe`
folds what it read — returns `n % 256 ^ width`, because the loop writes `n % 256` into
its first octet, and `beOctets` reverses that loop so the most significant octet comes
first. -/
def BigEndianFieldValue : Prop :=
  ∀ (width n : Nat),
    (beOctets width n).foldl (fun acc byte => acc * 256 + byte.toNat) 0 = n % 256 ^ width

/-- The field's value, for a value that fits the field.

`filled`'s success supplies exactly the hypothesis `n < 256 ^ width`, which turns
`BigEndianFieldValue`'s modulo into an identity — so this is the form each integer case
uses, and the form the composition is waiting on. -/
def FieldValueRoundTrip : Prop :=
  ∀ (width n : Nat), n < 256 ^ width →
    (beOctets width n).foldl (fun acc byte => acc * 256 + byte.toNat) 0 = n

/-- `BigEndianFieldValue`, proved.

`beOctets` is the loop's output reversed, so the reader's left fold of the field is the
loop's right fold of its own output (`List.foldl_reverse`) — which `go_foldr_value`
values. This is the step that makes a field's *value* a fact about the octets rather
than about the fold: after it, an integer case is arithmetic. -/
theorem bigEndianFieldValue : BigEndianFieldValue := by
  intro width n
  have h := go_foldr_value width n
  rw [beOctets, List.foldl_reverse]
  simpa [Nat.add_comm, Nat.mul_comm] using h

/-- `FieldValueRoundTrip`, proved: a value that fits the field is the field's own value,
because `filled`'s hypothesis `n < 256 ^ width` turns the modulo into an identity. -/
theorem fieldValueRoundTrip : FieldValueRoundTrip := by
  intro width n h
  rw [bigEndianFieldValue, Nat.mod_eq_of_lt h]

end SpecAMQP.Proofs
