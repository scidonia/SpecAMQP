import Proofs.CodecRoundTripDescribed

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
proof has to know that *the reader accepts the wide forms at all*: the law compares the
writer's canonical octets against an arbitrary accepted encoding, so it must know that an
accepted encoding of a given value carries the same quantities in a field of one of the
widths the table offers. That is a fact about the reader — R2's `lengthPrefixed` and R3's
compound case both exercise it — and it is not proved by the four rungs below, which reason
about the writer's own output. It is stated here as the hypothesis it is rather than assumed,
in the same way the frame round trip carries the value law as a hypothesis.

**Per family, not globally — and the honest form of that.** The rule is proved for the
quantities a field carries, and the canonical size is known per family (R2's
`lengthPrefixed_ok`, R3's `compoundOctets_ok_length` and `arrayOctets_ok_length`). What is
*not* yet available is a single statement of the reader's accepted widths covering all
families at once, which is what a global `NarrowestEncoding` needs. R5 therefore proves the
rule's inequality and the canonical sizes, and states the law; the step between them is the
reader-acceptance fact, named rather than elided.

## What is proved

* `widthChoice_le_of_fits` — the rule as an inequality: any width the table offers that
  carries every quantity is at least the width the rule chooses.
* `widthChoice_narrow_iff` — the rule read as an order: the chosen width is one octet
  exactly when one octet carries every quantity, so the wide choice is forced rather than
  optional.
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
