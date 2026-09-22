import Proofs.CodecRoundTripDescribed
import Proofs.ExceptMap

/-!
# The value codec's round trip: R5, the narrowest form

The four rungs below this one each prove an agreement: a write and a read-back are equal.
R5 is different in kind. `Contracts/Codec.lean`'s second law, `NarrowestEncoding`, is an
*inequality between two encodings of the same value* — for any buffer that decodes in full,
there is a canonical encoding of the value that is no longer than the buffer was. Nothing in
it says the reader recovers the writer's octets; it says something about the *choice rule*.

So the argument is not about agreement but about the choice. `widthChoice` is the rule, and
it was proved at both of its sides in R3: the narrow form is taken exactly when every
quantity the field carries fits in one octet. What R5 adds is the order-theoretic half of
that: among the widths the declared surface offers, the chosen one is the *smallest* that
carries the value. `widthChoice_le_of_fits` is that fact, and it is the whole of the rule's
content as an inequality — the choice is 1 only if one octet suffices, and 4 only when one
does not, so nothing narrower could have carried the same quantities.

## What is stated

`NarrowestEncoding`, stated exactly as the contract states it, over the specification's own
`encodeValue`/`decodeValue`.

**What the remaining argument needs, and from where.** To go from the rule to the law, a
proof has to know not what the *writer* chose but what the *reader consumed*: the law
compares the writer's canonical octets against an arbitrary accepted encoding, so it must
know that an accepted encoding carried the same quantities in a field of one of the two
widths the table offers, and at a size no smaller than the width the rule picks. That is a
set of reader-side lemmas, per family, derived from `takeBe`/`takeBytes`' own consumption
rather than from the writer's behaviour — the reader's dispatch is a function of the
accepted buffer's first octet, the same table decision the writer consults, so a proof of
the law can case on that octet and read the field's width off it without any API change.
They are proof-internal and they compose into the global statement.

**The law is not weakened, and it carries no hypothesis.** `NarrowestEncoding` is stated
exactly as the contract states it. What is missing is a rung of reader-consumption lemmas,
not a fact the reader withholds: "the accepted encoding's size is at least the canonical
size", once per family, is the work this rung leaves named rather than a reason to restate
the law per family.

## What is proved

* `widthChoice_le_of_fits` — the rule as an inequality: any width the table offers that
  carries every quantity is at least the width the rule chooses.
* `widthChoice_narrow_iff` — the rule read as an order: the chosen width is one octet
  exactly when one octet carries every quantity. This is what makes the wide choice
  **forced rather than preferred**: it is not a style the writer could reverse, it is what
  is left when one octet does not suffice, and `widthChoice_le_of_fits` is the same fact
  seen as an inequality. A reader who does not see this stated will assume the writer had a
  choice, which is exactly what "narrowest" denies.
* `lengthPrefixed_canonical_size` — the canonical size for a variable-width family, which is
  the right-hand side a per-family instance of the law compares against.
-/
namespace SpecAMQP.Proofs

open SpecAMQP.Spec.Codec
open SpecAMQP.Spec.ReadLaws
open SpecAMQP.Harness (Octets)

/-! ## The rule as an inequality -/

/-- **The chosen width is the smallest the table offers that carries the quantities.**

The declared surface offers two widths, one octet and four. If a width among them carries
every quantity the field must hold, then the rule's choice is no wider than that width: the
narrow choice is taken when one octet suffices, and the wide one only when it does not.

This is the order-theoretic content of the narrowest-form rule, and it is what an
inequality between two encodings needs from the choice — an agreement proof never consults
it. -/
theorem widthChoice_le_of_fits (quantities : List Nat) (w : Nat) (hw : w = 1 ∨ w = 4)
    (hfits : ∀ q ∈ quantities, q < 2 ^ (8 * w)) : widthChoice quantities ≤ w := by
  by_cases hall : quantities.all (fun q => q ≤ 255)
  · rw [widthChoice_narrow quantities hall]
    rcases hw with rfl | rfl <;> omega
  · rw [widthChoice_wide quantities (by simpa using hall)]
    rcases hw with rfl | rfl
    · -- one octet carries every quantity, so `all` could not have been false
      exfalso
      have hone : quantities.all (fun q => q ≤ 255) = true := by
        apply List.all_eq_true.mpr
        intro q hq
        have hq' := hfits q hq
        have h256 : (2 : Nat) ^ (8 * 1) = 256 := by decide
        rw [h256] at hq'
        have hbound : q ≤ 255 := by omega
        simpa using hbound
      exact hall hone
    · omega

/-- **The rule read as an order.** The narrow width is chosen exactly when one octet carries
every quantity, so the wide choice is not a preference the writer could reverse: it is what
is left when one octet does not suffice. -/
theorem widthChoice_narrow_iff (quantities : List Nat) :
    widthChoice quantities = 1 ↔ quantities.all (fun q => q ≤ 255) = true := by
  constructor
  · intro h
    by_cases hall : quantities.all (fun q => q ≤ 255)
    · exact hall
    · rw [widthChoice_wide quantities (by simpa using hall)] at h
      exact absurd h (by decide)
  · intro hall
    exact widthChoice_narrow quantities hall

/-- **The canonical size of a variable-width family.** The writer's octets are the narrowest
length field that carries the payload's length, then the payload, so the size the law
compares against is the field's width plus the payload's own octets — R2's size fact, under
R2's own rule. -/
theorem lengthPrefixed_canonical_size (payload : List UInt8) :
    (beOctets (lengthWidthOf payload.length) payload.length ++ payload).length =
      lengthWidthOf payload.length + payload.length := by
  simp [List.length_append, beOctets_length]

/-! ## The reader on arbitrary accepted octets

Everything below is a fact about the *reader*, on octets the writer did not necessarily
produce. The four agreement rungs never needed one: each of them compares the reader's
result with the writer's own output, so the octets it reasons about are the writer's by
construction. The narrowest-form law is a statement about the *choice rule* rather than
about agreement — it compares the writer's canonical octets with an arbitrary accepted
encoding — so it is the first claim that needs the reader measured on its own. That is why
these lemmas live here and not in `Spec/ReadLaws.lean`: they are about the choice, not
about the codec's behaviour, and the module that proves a law about the choice is where a
reader of this ladder will look for them.
-/

/-- **A big-endian fold of `words` octets is bounded by `256 ^ words`.**

The induction under `takeBe_lt`, generalised to an arbitrary accumulator because the loop
carries one: after `words` octets the accumulator is below `(init + 1) * 256 ^ words`, since
each octet multiplies by 256 and adds less than 256. -/
theorem foldl_be_bound (bytes : List UInt8) (init : Nat) :
    bytes.foldl (fun acc byte => acc * 256 + byte.toNat) init < (init + 1) * 256 ^ bytes.length := by
  induction bytes generalizing init with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one]; omega
  | cons x xs ih =>
    rw [List.length_cons, List.foldl_cons]
    have hx : x.toNat < 256 := x.toNat_lt
    calc xs.foldl (fun acc byte => acc * 256 + byte.toNat) (init * 256 + x.toNat)
        < (init * 256 + x.toNat + 1) * 256 ^ xs.length := ih (init * 256 + x.toNat)
      _ ≤ ((init + 1) * 256) * 256 ^ xs.length := by
          have hstep : init * 256 + x.toNat + 1 ≤ (init + 1) * 256 := by omega
          exact Nat.mul_le_mul_right _ hstep
      _ = (init + 1) * (256 ^ xs.length * 256) := by
          rw [Nat.mul_assoc, Nat.mul_comm 256 (256 ^ xs.length)]
      _ = (init + 1) * 256 ^ (xs.length + 1) := by rw [Nat.pow_succ]

/-- **A field's value is bounded by its own width.**

`takeBe width` folds the `width` octets it took, so what it returns is below
`256 ^ width`: a length read from a one-octet field is at most 255, and one read from a
four-octet field is below `2 ^ 32`. This is the reader's counterpart of the writer's
`filled` check, and it is the fact a narrowest-form argument about an *accepted* encoding
needs — the quantity it compares is one the reader read from a field of some width, and
this is what bounds it by that width.

The offset's check is not a hypothesis: `takeBe` is a `do`-block over `takeBytes`, so the
field's absence is a refusal of that block, and a refusal contradicts the success this
statement is handed. `Proofs/ExceptMap.lean`'s `except_bind_error` is what reduces that
`do`-block at the refusal and lets the contradiction be seen. -/
theorem takeBe_lt (width : Nat) (c : Cursor)
    (v : Nat) (c' : Cursor) (hv : takeBe width c = .ok (v, c')) : v < 256 ^ width := by
  by_cases h : c.pos + width ≤ c.data.size
  · rw [takeBe_eq_fold width c h] at hv
    have hval : beValue ((c.data.toList.drop c.pos).take width) = v :=
      congrArg Prod.fst (Except.ok.inj hv)
    have hlen : ((c.data.toList.drop c.pos).take width).length ≤ width := by
      rw [List.length_take]
      exact Nat.min_le_left _ _
    rw [← hval, beValue]
    have hbound : ((c.data.toList.drop c.pos).take width).foldl
        (fun acc byte => acc * 256 + byte.toNat) 0 <
          256 ^ ((c.data.toList.drop c.pos).take width).length := by
      simpa using foldl_be_bound ((c.data.toList.drop c.pos).take width) 0
    exact Nat.lt_of_lt_of_le hbound
      (Nat.pow_le_pow_right (by decide : (0 : Nat) < 256) hlen)
  · -- the field is not there, so the reader refuses and nothing was accepted
    simp only [takeBe, takeBytes, if_neg h, except_bind_error] at hv
    exact absurd hv (by simp)

/-! ## The first family's consumption lemma

The law needs, per family, that an accepted encoding's size is at least the canonical size.
For the variable-width families the argument is short and it uses both lemmas above plus
R2's and R3's rule: an accepted encoding's length field has one of the table's two widths
(`w = 1` or `w = 4`), it carries the payload's length (`takeBe_lt` bounds that length by
`w`), and the rule's width for that length is no wider than `w` (`widthChoice_le_of_fits`) —
so the canonical encoding, which is the rule's field plus the same payload, is no longer than
the accepted one, which is the accepted field plus that payload.

What is *not* here is the step that reads those two facts off an accepted buffer: that its
field's width is one of the two the table offers, and that the octets after the field are the
payload. That is the dispatch step, and it is where the law's own quantifier over all values
is discharged; the table it consults is data this repository exposes
(`Spec.Codec.dataDecl`, `Generated.Oasis.encodingOf`), so a fact about it is a fact this
repository can state rather than an assumption. -/

/-- **The rule's width is no wider than the field an accepted encoding used.**

If a length is carried by a field of width `w`, and `w` is one of the two widths the table
offers, then the width the rule picks for that length is at most `w`. This is
`widthChoice_le_of_fits` at this family's single quantity. -/
theorem lengthWidthOf_le_of_field (length w : Nat) (hw : w = 1 ∨ w = 4)
    (hcarries : length < 2 ^ (8 * w)) : lengthWidthOf length ≤ w := by
  rw [lengthWidthOf_eq_widthChoice]
  exact widthChoice_le_of_fits [length] w hw (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hcarries)

/-- **An accepted variable-width encoding is no shorter than the canonical one.**

The accepted encoding is a field of width `w` and then the payload; the canonical encoding
is the rule's field and then the same payload. Since the rule's width is no wider than `w`,
the canonical size is no larger — which is the inequality the law needs for this family,
against the canonical size R2's `lengthPrefixed_canonical_size` computes. -/
theorem variable_family_canonical_le (length w : Nat) (hw : w = 1 ∨ w = 4)
    (hcarries : length < 2 ^ (8 * w)) :
    lengthWidthOf length + length ≤ w + length := by
  have := lengthWidthOf_le_of_field length w hw hcarries
  omega

/-! ## The compound families and the described case

The same argument as the variable-width family, at their own quantities and constructor
octets.

A list, map or array declares a *size* — the octets after the size field — and a *count*, so
the rule's decision for it is `sizeWidthOf size count`, proved in R3 to be `widthChoice` over
both quantities. `compound_canonical_le` is therefore the variable family's inequality with
two quantities instead of one, and it covers all three compound forms at once, because all
three frame their body the same way: a size field, then `size` octets. The element
constructor an array adds lives *inside* those `size` octets, which is why it does not appear
in the comparison — a fact worth seeing, since it is the reason one theorem covers arrays and
lists together.

**The described case takes no instance at all, and that is R4's finding showing up as
arithmetic.** R4 established that a described value consults no choice rule, because its
framing carries no quantity. Here that is visible as `described_canonical_le`, which needs
no `widthChoice` lemma: the framing is one prefix octet, and the descriptor and the value
each contribute their own canonical size against their own accepted size, so the case is
purely additive. A family whose consumption lemma is a monotonicity of `+` is the concrete
form of "adds no new choice". -/

/-- **The rule's width is no wider than the field an accepted compound used.**

`sizeWidthOf` at two quantities — the size and the count the same field must carry — is
`widthChoice_le_of_fits` at that list. -/
theorem sizeWidthOf_le_of_field (size count w : Nat) (hw : w = 1 ∨ w = 4)
    (hcarries : size < 2 ^ (8 * w) ∧ count < 2 ^ (8 * w)) : sizeWidthOf size count ≤ w := by
  rw [sizeWidthOf_eq_widthChoice]
  exact widthChoice_le_of_fits [size, count] w hw (by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hcarries.1
    · exact hcarries.2)

/-- **An accepted compound encoding is no shorter than the canonical one.**

Both frame the same way — a size field and then `size` octets — so the comparison is the
widths, and the rule's is no wider. One theorem for lists, maps and arrays alike: an array's
element constructor is inside the octets its size counts, so it appears on neither side of
the comparison. -/
theorem compound_canonical_le (size count w : Nat) (hw : w = 1 ∨ w = 4)
    (hcarries : size < 2 ^ (8 * w) ∧ count < 2 ^ (8 * w)) :
    sizeWidthOf size count + size ≤ w + size := by
  have := sizeWidthOf_le_of_field size count w hw hcarries
  omega

/-- **The described case needs no width comparison.** A described value's framing is one
prefix octet and the two encodings; the canonical framing is shorter exactly when the
descriptor's and the value's own canonical encodings are, which is the case analysis R4
stated. This is the family whose consumption lemma mentions no field width at all — the
concrete form of "a described value consults no choice rule". -/
theorem described_canonical_le (descriptorCanonical valueCanonical descriptorAccepted
    valueAccepted : Nat) (hd : descriptorCanonical ≤ descriptorAccepted)
    (hv : valueCanonical ≤ valueAccepted) :
    1 + descriptorCanonical + valueCanonical ≤ 1 + descriptorAccepted + valueAccepted := by
  omega

/-! ## What the reader consumed

The third thing the global step needs is a fact about the *reader's cursor* rather than
about the table: that a field read advances the cursor by the field's width (`takeBe_eq_fold`
gives both the fold and the advance), and that a payload read advances it by the payload's own
length and no more. `takeBytes_advances` is the second of those — the reader's own account of
how far it moved, which is what lets an accepted encoding's size be written as the field plus
the quantity the family inequalities compare.

Neither carries a precondition: a refusal is what the reader's success rules out, and the case
split that reads that off is now available, because `Proofs/ExceptMap.lean` hands `simp` the
`Except` reduction that was missing — the `>>=` a `do`-block desugars to. Before that lemma a
successful read's own refusal branch could not be discharged, so both statements carried the
cursor's check as a hypothesis rather than deriving it; the check is no longer needed, and no
consumption site has to supply it. -/

/-- **Reading `n` octets advances the cursor by `n` and yields `n` of them.**

The reader's own account of its movement: `takeBytes n` at an offset that holds `n` octets
returns a cursor at `pos + n` and a buffer of exactly `n` octets. This is what an accepted
encoding's size is made of — a field, then a payload of the payload's own length.

The offset's check is not a hypothesis: if the octets were not there, `takeBytes` would refuse,
and its refusal contradicts the hypothesis that it succeeded. -/
theorem takeBytes_advances (n : Nat) (c : Cursor)
    (bytes : Octets) (c' : Cursor) (hb : takeBytes n c = .ok (bytes, c')) :
    c'.pos = c.pos + n ∧ bytes.size = n := by
  by_cases h : c.pos + n ≤ c.data.size
  · simp only [takeBytes, h, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hb
    obtain ⟨hbytes, hcursor⟩ := hb
    refine ⟨?_, ?_⟩
    · rw [← hcursor]
    · rw [← hbytes, Array.size_extract]
      omega
  · -- the reader refuses, so nothing was accepted
    simp only [takeBytes, if_neg h] at hb
    exact absurd hb (by simp)

/-! ## The rung's claim -/

/-- **R5: the writer's encoding is no longer than anything the reader accepts.**

Stated exactly as `Contracts/Codec.lean` states it: for any buffer that decodes in full, the
value it decodes to has a canonical encoding that is no longer than that buffer. This is the
one claim in the ladder that is not an agreement between a write and a read-back, and it is
the only one whose proof needs the *reader's* accepted widths rather than the writer's
chosen one. -/
def NarrowestEncoding : Prop :=
  ∀ (bytes : Octets) (value : Value) (consumed : Nat),
    decodeValue bytes = .ok (value, consumed) →
    consumed = bytes.size →
    ∃ canonical, encodeValue value = .ok canonical ∧ canonical.size ≤ bytes.size

end SpecAMQP.Proofs
