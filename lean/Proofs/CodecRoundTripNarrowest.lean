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
open SpecAMQP.Generated.Oasis (Category EncodingDecl encodings encodingOf)
open SpecAMQP.Spec.Value (Constructor classify)
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

/-! ## The dispatch step, specified

What is left for the law is a case analysis over `readValue`'s own dispatch, and it must
reconcile three things — the family lemmas above are *within-family* inequalities about a
size, while the law quantifies over all values and compares `canonical.size ≤ bytes.size`:

1. **which family the accepted buffer's first octet selects** — a fact about the declared
   surface, `Spec.Codec.dataDecl` for the row an octet names;
2. **that family's field width**, which for the two width-choosing families is one or four —
   again a table fact, since the widths are the rows the surface declares;
3. **that the accepted size is the field plus the quantity the family's inequality talks
   about** — the reader's own arithmetic, which is now in hand: `takeBe_advances` gives the
   field read's advance out of the read's own success, `takeBytes_advances` gives a payload
   read's advance and its size, and `takeBe_lt` bounds the length a field carried. The
   variable-width family's instance of that step is `readVariable_consumes` below, and
   `readVariable_canonical_le` is it composed with the family inequality.

Two things here look like blockers and are not. A proof that seems to need the cursor's check
as a hypothesis is a proof whose earlier statement is not in the shape it should be: `takeBe_lt`,
`takeBe_advances` and `takeBytes_advances` all take only the *result* of the read and derive
the check from it, so supplying the check means something upstream was stated wrong. And
`lengthPrefixed_ok` is already the success form — `out.length = decl.width + payload.length`
from `lengthPrefixed decl payload = .ok out` — so a family's step needs no fit hypothesis about
the payload's length: the write's own success *is* the hypothesis, and that is what the law's
statement supplies.

The first lemma is therefore the second family's reading-off step, and it is landed below:
`readVariable_consumes` reads the accepted size off the reader's own consumption — the row's
width plus the field's length — and `readVariable_canonical_le` is it composed with the family
inequality, through `variable_row_width` for the row's width. `readVariable_ok` is the row's read
taken apart, which is what the other families' steps will want too.

What is landed below for the other families is the same reading-off step at their own framing —
`readCompound_consumes` and `readArrayData_consumes`, which get the accepted size out of the
reader's own measurement rather than out of the items' arithmetic, and `readValue_described`,
which is the described case's one octet and two reads — together with the dispatch itself:
`decodeValue_entry` puts `decodeValue` in the reader's own terms, `readValue_dispatch` reads the
octet, its classification, the row the surface assigned it and the reader call that produced the
value off an accepted buffer, and the row lemmas above it (`dataDecl_ok_mem`,
`declInRange_category`, the four `dataDecl_category_of_*`) are what make the row's category and
its table membership available.

Three things remain, and each is named rather than assumed.

**The measurement-to-advance step.** The compound and array readings report their size as the
reader computed it — `c'.pos - start = size` — and turning that into an advance,
`c'.pos = start + size`, needs one fact about the reader this module does not yet have: that a
read never moves its cursor backwards. `readValue`, `readCompound`, `readArrayData`, `readItems`,
`readElements` and `readElementsLoop` are mutually recursive, so that fact is a mutual induction
over the cluster. It is a fact the specification can state and this repository can prove; it is
named here because the two steps above are honest without it and would be dishonest with it
assumed.

**The fixed family's reading-off step.** `readScalarData`'s fixed half (`readFixed`) has no
reading-off step in this module yet — its accepted size is the row's own width — and it is the
family whose canonical comparison needs the writer's table lookup to agree with the reader's row,
which is a table fact of the same kind as `variable_row_width`.

**The per-family size comparisons.** The reading-off steps give each family's accepted numbers;
comparing them with the canonical size the writer would produce needs the value-to-payload links,
and for the two text families that is where the gap below bites.

One fact the law needs is **not** available in this closure, and it is named rather than assumed:
the writer's payload for `string` and `symbol` is `text.toUTF8.toList`, while the reader's payload
is the octets `utf8Of` decoded, so comparing the two families' canonical size against an accepted
size needs "octets that decode to a text re-encode to those octets" — a fact about the standard
library's UTF-8 reader (`String.fromUTF8?` / `String.toUTF8`). Core states no such theorem, and
batteries does not either. The `binary` family needs no such fact, so its size comparison is the
one this module's lemmas close outright.
-/

/-! ## The variable family's reading-off step

Three things, in the order the dispatch needs them: the field read's advance without its check
(`takeBe_advances` — the fact `takeBe_eq_fold` could only state with the offset's check as a
hypothesis, derived here from the read's own success), the row's read taken apart
(`readVariable_ok`), and the recorded reading-off step itself (`readVariable_consumes`: the
accepted size is the row's width plus the payload's length, that length is below `256 ^ width`,
and the value carries the payload the reader took).

The table's half is `variable_row_width`: a row whose owner is one of the three variable-width
families has one of the table's two widths. That is a fact about the declared surface rather
than about the reader, and it is decided over the generated table — the same rows `encodingOf`
returns, so no code is transcribed here.

`readVariable_canonical_le` is those three composed: the canonical size the family's inequality
compares against is no larger than what the read consumed. What it is *not* is the law: it says
nothing about the writer's octets, which is the step below it. -/

/-- **A successful field read advances the cursor by the field's width.**

`takeBe` is a `do`-block over `takeBytes`, so its success is `takeBytes`' success and the cursor
it returns is the one `takeBytes` returned. The offset's check is not a precondition: where the
octets are not there the block refuses, and a refusal contradicts the success this statement is
given. `takeBe_eq_fold` states the same advance, but only at an offset whose check is already in
hand; this is the form a composition site wants, because the reader's own success is what it
has. -/
theorem takeBe_advances (width : Nat) (c : Cursor) (v : Nat) (c' : Cursor)
    (hv : takeBe width c = .ok (v, c')) : c'.pos = c.pos + width := by
  by_cases h : c.pos + width ≤ c.data.size
  · simp only [takeBe, takeBytes, if_pos h, except_bind_ok] at hv
    have hcur : (⟨c.data, c.pos + width⟩ : Cursor) = c' := (Prod.mk.inj (Except.ok.inj hv)).2
    rw [← hcur]
  · simp only [takeBe, takeBytes, if_neg h, except_bind_error] at hv
    exact absurd hv (by simp)

/-- **The payload a variable-width row's value carries.**

The reader's three cases, as a statement rather than as the `match` they come from: a `binary`
value *is* the octets the row took, and a `string` or `symbol` value is what those octets decode
to under the codec's own UTF-8 reader. Saying it this way lets the family's size argument name
the payload — the quantity both the writer's `lengthPrefixed` and the reader's field talk about —
without going through the text. -/
def ValueCarries (value : Value) (payload : Octets) : Prop :=
  value = .binary payload ∨
    (∃ text : String, value = .string text ∧ utf8Of payload "string" = .ok text) ∨
      (∃ text : String, value = .symbol text ∧ utf8Of payload "symbol" = .ok text)

/-- **A variable-width row's read, taken apart.**

The row reads a field, then that many octets, then hands both to its owner's case. Inverting that
is two cases on the `do`-block's left sides — which is what `Proofs/ExceptMap.lean`'s reductions
make possible without the offset's check — and one case on the owner the row names. Each case's
equations are *obtained* rather than substituted, so the components the conclusion names are the
same terms the caller will use: a `cases hb : e` inside the goal would rewrite `e` away and leave
the fact about `e` unusable in the very place it is needed. -/
theorem readVariable_ok (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor)
    (h : readVariable decl c = .ok (value, c')) :
    ∃ length : Nat, ∃ c₁ : Cursor, ∃ payload : Octets, ∃ c₂ : Cursor,
      takeBe decl.width c = .ok (length, c₁) ∧
      takeBytes length c₁ = .ok (payload, c₂) ∧
      c₂ = c' ∧ ValueCarries value payload := by
  obtain ⟨length, c₁, hbe⟩ : ∃ l : Nat, ∃ cc : Cursor, takeBe decl.width c = .ok (l, cc) := by
    cases hb : takeBe decl.width c with
    | error e =>
      exfalso
      simp only [readVariable, hb, except_bind_error] at h
      exact absurd h (by simp)
    | ok v => exact ⟨v.1, v.2, rfl⟩
  unfold readVariable at h
  rw [hbe] at h
  simp only [except_bind_ok] at h
  obtain ⟨payload, c₂, hbp⟩ : ∃ p : Octets, ∃ cc : Cursor, takeBytes length c₁ = .ok (p, cc) := by
    cases hb : takeBytes length c₁ with
    | error e =>
      exfalso
      simp only [hb, except_bind_error] at h
      exact absurd h (by simp)
    | ok w => exact ⟨w.1, w.2, rfl⟩
  rw [hbp] at h
  simp only [except_bind_ok] at h
  have hrec : c₂ = c' ∧ ValueCarries value payload := by
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.2, Or.inl h.1.symm⟩
    · cases hu : utf8Of payload "string" with
      | error e => simp only [hu, except_bind_error] at h; exact absurd h (by simp)
      | ok text =>
        simp only [hu, except_bind_ok, except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨h.2, Or.inr (Or.inl ⟨text, h.1.symm, hu⟩)⟩
    · cases hu : utf8Of payload "symbol" with
      | error e => simp only [hu, except_bind_error] at h; exact absurd h (by simp)
      | ok text =>
        simp only [hu, except_bind_ok, except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨h.2, Or.inr (Or.inr ⟨text, h.1.symm, hu⟩)⟩
    · -- the row's owner is none of the three, so the reader refused
      simp at h
  exact ⟨length, c₁, payload, c₂, hbe, hbp, hrec.1, hrec.2⟩

/-- **The variable family's reading-off step.**

An accepted read from a variable-width row consumed the row's width plus the length its field
carried, that length is below `256 ^ width` (so an accepted field carries a quantity the rule can
compare against), and the value carries exactly the payload the reader took — the octets the
field's length counts. This is the fact the dispatch was missing: it reads the reader's own
numbers off the reader's own consumption, and it is composed of `takeBe_advances`,
`takeBytes_advances` and `takeBe_lt`, none of which needs the offset's check. -/
theorem readVariable_consumes (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor)
    (h : readVariable decl c = .ok (value, c')) :
    ∃ length : Nat, ∃ payload : Octets,
      payload.size = length ∧
      length < 2 ^ (8 * decl.width) ∧
      c'.pos = c.pos + decl.width + length ∧
      ValueCarries value payload := by
  obtain ⟨length, c₁, payload, c₂, hbe, hbp, hc, hcarries⟩ := readVariable_ok decl c value c' h
  obtain ⟨hpos, hsize⟩ := takeBytes_advances length c₁ payload c₂ hbp
  refine ⟨length, payload, hsize, ?_, ?_, hcarries⟩
  · rw [two_pow_eight_mul]
    exact takeBe_lt decl.width c length c₁ hbe
  have hfield : c₁.pos = c.pos + decl.width := takeBe_advances decl.width c length c₁ hbe
  rw [← hc]
  omega

/-- **The widths a variable-width row offers, decided over the table.**

The declared surface assigns each variable-width family two rows, one of one octet and one of
four, and this is that fact read off the generated table rather than transcribed: the rows whose
owner is one of the three families all have one of the two widths. -/
theorem variable_owners_have_two_widths :
    (encodings.filter (fun decl => decl.owner = "binary" ∨ decl.owner = "string" ∨
      decl.owner = "symbol")).all (fun decl => decl.width = 1 ∨ decl.width = 4) = true := by
  decide

/-- **A row of a variable-width family has one of the table's two widths.** -/
theorem variable_row_width (decl : EncodingDecl) (hmem : decl ∈ encodings)
    (howner : decl.owner = "binary" ∨ decl.owner = "string" ∨ decl.owner = "symbol") :
    decl.width = 1 ∨ decl.width = 4 := by
  have hall := variable_owners_have_two_widths
  rw [List.all_eq_true] at hall
  have hfilter : decl ∈ encodings.filter (fun decl => decl.owner = "binary" ∨
      decl.owner = "string" ∨ decl.owner = "symbol") := by
    rw [List.mem_filter]
    exact ⟨hmem, by simpa using howner⟩
  simpa using hall decl hfilter

/-- **An accepted variable-width read is no shorter than the canonical encoding of what it
read.**

The composition the dispatch needs for this family: the size the reader consumed is the row's
width plus the payload's length, the canonical size for that payload is the rule's width plus the
same length (`lengthPrefixed_canonical_size`), and the rule's width is no wider than the row's
(`variable_family_canonical_le` at `variable_row_width`). -/
theorem readVariable_canonical_le (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor)
    (h : readVariable decl c = .ok (value, c')) (hmem : decl ∈ encodings)
    (howner : decl.owner = "binary" ∨ decl.owner = "string" ∨ decl.owner = "symbol") :
    ∃ length : Nat, ∃ payload : Octets,
      payload.size = length ∧
      ValueCarries value payload ∧
      lengthWidthOf length + length ≤ c'.pos - c.pos := by
  obtain ⟨length, payload, hsize, hbound, hpos, hcarries⟩ :=
    readVariable_consumes decl c value c' h
  refine ⟨length, payload, hsize, hcarries, ?_⟩
  have hsub : c'.pos - c.pos = decl.width + length := by omega
  rw [hsub]
  exact variable_family_canonical_le length decl.width
    (variable_row_width decl hmem howner) hbound

/-! ## The compound families' and the described case's reading-off steps

The same three things as the variable family's, at their own framing. A compound declares a
*size* and a *count*, and the reader checks the octets it measured against the size it read —
so `readCompound_consumes` gets the accepted size out of that check rather than out of the
items' arithmetic: the check *is* the measurement, and the items themselves need not be taken
apart. The array case is the same with its constructor octet and its count ceiling inside the
window, and its element lookup is not inverted either: the accepted size is what the check says
regardless of which rows the constructor named.

The described case takes no field at all. `readValue_described` is its reading-off step: an
accepted described value is one prefix octet and two recursively read values, which is the
additivity `described_canonical_le` already turns into the case's inequality. -/

/-- **The shape a compound read's items take in its value.** A `list` row's value is the items
themselves, a `map` row's is those items paired, and an `array` row's is the items under the one
constructor octet the array declared — the three cases of `readCompound`/`readArrayData`, as a
statement rather than as the `match` they come from. -/
def CompoundCarries (value : Value) (items : List Value) : Prop :=
  value = .list items ∨ value = .map (pairUp items) ∨
    ∃ constructor : UInt8, value = .array constructor items

/-- **A compound row's read, read off its own measurement.**

An accepted compound decoding read a size field and a count field, both below `256 ^ width`, and
the octets it then measured — everything after the size field, up to where the value ended — are
exactly the `size` the field declared.

The measurement is the equation the reader itself checked (`measured = size`), so the size is not
inferred from the items: it is read off the identical quantity the reader computed. Turning that
subtraction into an addition needs one fact about the reader which this module does not yet have
— that a read never moves its cursor backwards (`readValue` and the loops are mutually recursive,
so it is a mutual induction), which is also why `readItems` is not taken apart here: the items'
values are not needed to state the framing, only to bound the body recursively later. -/
theorem readCompound_consumes (fuel : Nat) (decl : EncodingDecl) (c : Cursor) (value : Value)
    (c' : Cursor) (h : readCompound fuel decl c = .ok (value, c')) :
    ∃ size count : Nat, ∃ items : List Value, ∃ start : Cursor,
      start.pos = c.pos + decl.width ∧
      c'.pos - start.pos = size ∧
      size < 2 ^ (8 * decl.width) ∧
      count < 2 ^ (8 * decl.width) ∧
      CompoundCarries value items := by
  obtain ⟨size, c₁, hbs⟩ : ∃ s : Nat, ∃ cc : Cursor, takeBe decl.width c = .ok (s, cc) := by
    cases hb : takeBe decl.width c with
    | error e =>
      exfalso
      simp only [readCompound, hb, except_bind_error] at h
      exact absurd h (by simp)
    | ok v => exact ⟨v.1, v.2, rfl⟩
  unfold readCompound at h
  rw [hbs] at h
  simp only [except_bind_ok] at h
  obtain ⟨count, c₂, hbc⟩ : ∃ n : Nat, ∃ cc : Cursor, takeBe decl.width c₁ = .ok (n, cc) := by
    cases hb : takeBe decl.width c₁ with
    | error e =>
      exfalso
      simp only [hb, except_bind_error] at h
      exact absurd h (by simp)
    | ok v => exact ⟨v.1, v.2, rfl⟩
  rw [hbc] at h
  simp only [except_bind_ok] at h
  have hsize : size < 2 ^ (8 * decl.width) := by
    rw [two_pow_eight_mul]
    exact takeBe_lt decl.width c size c₁ hbs
  have hcount : count < 2 ^ (8 * decl.width) := by
    rw [two_pow_eight_mul]
    exact takeBe_lt decl.width c₁ count c₂ hbc
  have hstart : c₁.pos = c.pos + decl.width := takeBe_advances decl.width c size c₁ hbs
  -- the count's read leaves the cursor where the measurement's window starts
  split at h
  · -- list
    obtain ⟨items, c₃, hbi⟩ :
        ∃ l : List Value, ∃ cc : Cursor, readItems fuel count c₂ = .ok (l, cc) := by
      cases hb : readItems fuel count c₂ with
      | error e =>
        exfalso
        simp only [hb, except_bind_error] at h
        exact absurd h (by simp)
      | ok v => exact ⟨v.1, v.2, rfl⟩
    rw [hbi] at h
    simp only [except_bind_ok] at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      refine ⟨size, count, items, c₁, hstart, ?_, hsize, hcount, Or.inl h.1.symm⟩
      rw [← h.2]
      assumption
    · simp at h
  · -- map
    split at h
    · simp at h
    · obtain ⟨items, c₃, hbi⟩ :
          ∃ l : List Value, ∃ cc : Cursor, readItems fuel count c₂ = .ok (l, cc) := by
        cases hb : readItems fuel count c₂ with
        | error e =>
          exfalso
          simp only [hb, except_bind_error] at h
          exact absurd h (by simp)
        | ok v => exact ⟨v.1, v.2, rfl⟩
      rw [hbi] at h
      simp only [except_bind_ok] at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        refine ⟨size, count, items, c₁, hstart, ?_, hsize, hcount, Or.inr (Or.inl h.1.symm)⟩
        rw [← h.2]
        assumption
      · simp at h
  · -- an owner that is not a compound form
    simp at h

/-- **An array row's read, read off its own measurement.**

The same as `readCompound_consumes` with the array's own two additions inside the window: a count
the reader refuses above `arrayElementLimit`, and one constructor octet whose row is looked up.
Neither has to be taken apart — the accepted size is what the measurement says, whatever the
elements turned out to be — and the count ceiling comes out of the check rather than out of the
elements' count, so the element lookup is never inverted here. -/
theorem readArrayData_consumes (fuel : Nat) (decl : EncodingDecl) (c : Cursor) (value : Value)
    (c' : Cursor) (h : readArrayData fuel decl c = .ok (value, c')) :
    ∃ size count : Nat, ∃ constructor : UInt8, ∃ items : List Value, ∃ start : Cursor,
      start.pos = c.pos + decl.width ∧
      c'.pos - start.pos = size ∧
      size < 2 ^ (8 * decl.width) ∧
      count < 2 ^ (8 * decl.width) ∧
      count ≤ arrayElementLimit ∧
      value = .array constructor items := by
  cases fuel with
  | zero =>
    simp only [readArrayData] at h
    exact absurd h (by simp)
  | succ f =>
    obtain ⟨size, c₁, hbs⟩ : ∃ s : Nat, ∃ cc : Cursor, takeBe decl.width c = .ok (s, cc) := by
      cases hb : takeBe decl.width c with
      | error e =>
        exfalso
        simp only [readArrayData, hb, except_bind_error] at h
        exact absurd h (by simp)
      | ok v => exact ⟨v.1, v.2, rfl⟩
    unfold readArrayData at h
    rw [hbs] at h
    simp only [except_bind_ok] at h
    obtain ⟨count, c₂, hbc⟩ : ∃ n : Nat, ∃ cc : Cursor, takeBe decl.width c₁ = .ok (n, cc) := by
      cases hb : takeBe decl.width c₁ with
      | error e =>
        exfalso
        simp only [hb, except_bind_error] at h
        exact absurd h (by simp)
      | ok v => exact ⟨v.1, v.2, rfl⟩
    rw [hbc] at h
    simp only [except_bind_ok] at h
    have hsize : size < 2 ^ (8 * decl.width) := by
      rw [two_pow_eight_mul]
      exact takeBe_lt decl.width c size c₁ hbs
    have hcount : count < 2 ^ (8 * decl.width) := by
      rw [two_pow_eight_mul]
      exact takeBe_lt decl.width c₁ count c₂ hbc
    have hstart : c₁.pos = c.pos + decl.width := takeBe_advances decl.width c size c₁ hbs
    split at h
    · -- above the reader's ceiling
      simp at h
    · obtain ⟨constructor, c₃, hbu⟩ : ∃ b : UInt8, ∃ cc : Cursor, takeU8 c₂ = .ok (b, cc) := by
        cases hb : takeU8 c₂ with
        | error e =>
          exfalso
          simp only [hb, except_bind_error] at h
          exact absurd h (by simp)
        | ok v => exact ⟨v.1, v.2, rfl⟩
      rw [hbu] at h
      simp only [except_bind_ok] at h
      obtain ⟨elementDecl, hbe⟩ : ∃ d : Option EncodingDecl, elementDecl? constructor = .ok d := by
        cases hb : elementDecl? constructor with
        | error e =>
          exfalso
          simp only [hb, except_bind_error] at h
          exact absurd h (by simp)
        | ok v => exact ⟨v, rfl⟩
      rw [hbe] at h
      simp only [except_bind_ok] at h
      obtain ⟨items, c₅, hbl⟩ :
          ∃ l : List Value, ∃ cc : Cursor,
            readElements f elementDecl count c₃ = .ok (l, cc) := by
        cases hb : readElements f elementDecl count c₃ with
        | error e =>
          exfalso
          simp only [hb, except_bind_error] at h
          exact absurd h (by simp)
        | ok v => exact ⟨v.1, v.2, rfl⟩
      rw [hbl] at h
      simp only [except_bind_ok] at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        refine ⟨size, count, constructor, items, c₁, hstart, ?_, hsize, hcount, ?_, h.1.symm⟩
        · rw [← h.2]
          assumption
        · omega
      · simp at h

/-- **An accepted described value is one octet and two reads.**

`readValue`'s descriptor case is the one branch that consults no row at all: the prefix octet
says a described value follows, and then a descriptor and a value are read one after the other.
This is that decomposition — the prefix octet, its one-octet advance, and the two recursive
reads — which is the additivity `described_canonical_le` turns into the case's inequality, and
why R4 could say a described value consults no choice rule.

The classification is a *hypothesis* rather than something read out of the accepted value: the
caller is the dispatch, which cases on the octet's classification anyway, and a statement that
recovered it from the result would have to rule out the other five branches by showing that no
other reader ever returns a described value — five obligations bought for no use. -/
theorem readValue_described (fuel : Nat) (c : Cursor) (code : UInt8) (c₁ : Cursor)
    (hbu : takeU8 c = .ok (code, c₁)) (hclass : classify code.toNat = .descriptor)
    (value : Value) (c' : Cursor) (h : readValue (fuel + 1) c = .ok (value, c')) :
    ∃ descriptor inner : Value, ∃ c₂ c₃ : Cursor,
      value = .described descriptor inner ∧
      c₁.pos = c.pos + 1 ∧
      readValue fuel c₁ = .ok (descriptor, c₂) ∧
      readValue fuel c₂ = .ok (inner, c₃) ∧ c₃ = c' := by
  obtain ⟨descriptor, c₂, hbd⟩ :
      ∃ v : Value, ∃ cc : Cursor, readValue fuel c₁ = .ok (v, cc) := by
    unfold readValue at h
    rw [hbu] at h
    simp only [except_bind_ok, hclass] at h
    cases hb : readValue fuel c₁ with
    | error e =>
      exfalso
      simp only [hb, except_bind_error] at h
      exact absurd h (by simp)
    | ok v => exact ⟨v.1, v.2, rfl⟩
  unfold readValue at h
  rw [hbu] at h
  simp only [except_bind_ok, hclass] at h
  rw [hbd] at h
  simp only [except_bind_ok] at h
  obtain ⟨inner, c₃, hbv⟩ :
      ∃ v : Value, ∃ cc : Cursor, readValue fuel c₂ = .ok (v, cc) := by
    cases hb : readValue fuel c₂ with
    | error e =>
      exfalso
      simp only [hb, except_bind_error] at h
      exact absurd h (by simp)
    | ok v => exact ⟨v.1, v.2, rfl⟩
  rw [hbv] at h
  simp only [except_bind_ok, except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
  have hone : c₁.pos = c.pos + 1 := by
    simp only [takeU8] at hbu
    split at hbu
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hbu
      rw [← hbu.2]
    · simp at hbu
  exact ⟨descriptor, inner, c₂, c₃, h.1.symm, hone, hbd, hbv, h.2⟩

/-! ## The dispatch: which family an accepted buffer's first octet selects

The law quantifies over all values, so its proof has to read the reader's own dispatch off the
accepted buffer: the first octet, the classification that octet's grammar gives it, and — for
every category that consults a row — the row the declared surface assigns it. These are the two
facts that step needs, plus the entry point that puts `decodeValue` in the reader's own terms. -/

/-- **`decodeValue`'s entry point.** The decoder is `readValue` at the whole buffer, with the
buffer's length as its fuel, and the count it reports is the cursor's final position — so an
accepted decode is an accepted `readValue` from the buffer's start, and the count is where that
read ended. -/
theorem decodeValue_entry (bytes : Octets) (value : Value) (consumed : Nat)
    (h : decodeValue bytes = .ok (value, consumed)) :
    ∃ c : Cursor, readValue bytes.size ⟨bytes, 0⟩ = .ok (value, c) ∧ c.pos = consumed := by
  unfold decodeValue at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨_, by rw [← h.1]; assumption, h.2⟩
  · simp at h

/-- **The row a range check returns has the category the range gave it.** `declInRange` looks the
octet up in the generated table and refuses a row whose category is not the range's, so an
accepted row's category is the range's — the reason an octet's classification and the row it
selects agree, which is what lets the reader's category dispatch be read off the octet. -/
theorem declInRange_category {code : UInt8} {cat : Category} {w : Nat} {decl : EncodingDecl}
    (h : declInRange code cat w = .ok decl) : decl.category = cat := by
  unfold declInRange at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Except.ok.injEq] at h
      rw [← h]
      assumption
    · exact absurd h (by simp)

/-- **The row a range check returns is the row the table's lookup found.** -/
theorem declInRange_encodingOf {code : UInt8} {cat : Category} {w : Nat} {decl : EncodingDecl}
    (h : declInRange code cat w = .ok decl) : encodingOf code.toNat = some decl := by
  unfold declInRange at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Except.ok.injEq] at h
      rw [← h]
      assumption
    · exact absurd h (by simp)

/-- **A lookup that found a row found one of the table's own.** -/
theorem mem_of_encodingOf {code : Nat} {decl : EncodingDecl} (h : encodingOf code = some decl) :
    decl ∈ encodings := by
  unfold encodingOf at h
  exact List.mem_of_find?_eq_some h

/-- **A row the surface assigned is a row of the surface.** `dataDecl` refuses an octet the
generated table assigns no encoding and otherwise returns the row `encodingOf` found, so a row it
returns is one of the table's — the fact a table lemma about rows needs from a lookup, and the
reason the width facts below can be decided over the table rather than stated about an opaque
row. -/
theorem dataDecl_ok_mem {code : UInt8} {decl : EncodingDecl} (h : dataDecl code = .ok decl) :
    decl ∈ encodings := by
  unfold dataDecl at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  all_goals exact mem_of_encodingOf (declInRange_encodingOf h)

/-- **The row an octet's classification selects has that category.** With the octet's own
classification in hand, `dataDecl` returns the range check's row, so the row's category is the
classification's — `declInRange_category` at the range the classification names. -/
theorem dataDecl_category_of_fixed {code : UInt8} {w : Nat} {decl : EncodingDecl}
    (hcl : classify code.toNat = .fixed w) (h : dataDecl code = .ok decl) :
    decl.category = .fixed := by
  unfold dataDecl at h
  simp only [hcl] at h
  exact declInRange_category h

/-- As `dataDecl_category_of_fixed`, for the variable range. -/
theorem dataDecl_category_of_variable {code : UInt8} {w : Nat} {decl : EncodingDecl}
    (hcl : classify code.toNat = .variable w) (h : dataDecl code = .ok decl) :
    decl.category = .variable := by
  unfold dataDecl at h
  simp only [hcl] at h
  exact declInRange_category h

/-- As `dataDecl_category_of_fixed`, for the compound range. -/
theorem dataDecl_category_of_compound {code : UInt8} {w : Nat} {decl : EncodingDecl}
    (hcl : classify code.toNat = .compound w) (h : dataDecl code = .ok decl) :
    decl.category = .compound := by
  unfold dataDecl at h
  simp only [hcl] at h
  exact declInRange_category h

/-- As `dataDecl_category_of_fixed`, for the array range. -/
theorem dataDecl_category_of_array {code : UInt8} {w : Nat} {decl : EncodingDecl}
    (hcl : classify code.toNat = .array w) (h : dataDecl code = .ok decl) :
    decl.category = .array := by
  unfold dataDecl at h
  simp only [hcl] at h
  exact declInRange_category h

/-- **The reader's dispatch, read off the accepted buffer.**

An accepted `readValue` read a constructor octet and classified it, and what follows is one of the
reader's five cases: the descriptor prefix and two recursive reads, or a row of the declared
surface with the reader its category selects. This is the inversion the law's case analysis needs
— the octet, its classification, the row and its category membership, and the reader call that
produced the value — and it carries the row's *membership* because every table fact about a row
(a width, a family) is decided over `encodings`.

The row branches carry the category the classification gave, through `declInRange`'s own check:
`dataDecl` refuses a row whose category is not the range's, so the octet's classification and the
row it selected cannot disagree. That is what lets the category dispatch below be read off the
octet rather than assumed. -/
theorem readValue_dispatch (fuel : Nat) (c : Cursor) (value : Value) (c' : Cursor)
    (h0 : readValue (fuel + 1) c = .ok (value, c')) :
    ∃ code : UInt8, ∃ c₁ : Cursor, takeU8 c = .ok (code, c₁) ∧
      ((classify code.toNat = .descriptor ∧
          ∃ descriptor inner : Value, ∃ c₂ c₃ : Cursor,
            value = .described descriptor inner ∧ c₁.pos = c.pos + 1 ∧
            readValue fuel c₁ = .ok (descriptor, c₂) ∧
            readValue fuel c₂ = .ok (inner, c₃) ∧ c₃ = c') ∨
        ((∃ w : Nat, classify code.toNat = .fixed w ∨ classify code.toNat = .variable w) ∧
          ∃ decl : EncodingDecl, decl ∈ encodings ∧ dataDecl code = .ok decl ∧
            readScalarData decl c₁ = .ok (value, c')) ∨
        ((∃ w : Nat, classify code.toNat = .compound w) ∧
          ∃ decl : EncodingDecl, decl ∈ encodings ∧ dataDecl code = .ok decl ∧
            readCompound fuel decl c₁ = .ok (value, c')) ∨
        ((∃ w : Nat, classify code.toNat = .array w) ∧
          ∃ decl : EncodingDecl, decl ∈ encodings ∧ dataDecl code = .ok decl ∧
            readArrayData fuel decl c₁ = .ok (value, c'))) := by
  obtain ⟨code, c₁, hbu⟩ : ∃ b : UInt8, ∃ cc : Cursor, takeU8 c = .ok (b, cc) := by
    cases hb : takeU8 c with
    | error e =>
      exfalso
      simp only [readValue, hb, except_bind_error] at h0
      exact absurd h0 (by simp)
    | ok v => exact ⟨v.1, v.2, rfl⟩
  refine ⟨code, c₁, hbu, ?_⟩
  have h := h0
  unfold readValue at h
  rw [hbu] at h
  simp only [except_bind_ok] at h
  split at h
  · obtain ⟨descriptor, inner, c₂, c₃, hval, hone, hbd, hbv, hc⟩ :=
      readValue_described fuel c code c₁ hbu (by assumption) value c' h0
    exact Or.inl ⟨by assumption, descriptor, inner, c₂, c₃, hval, hone, hbd, hbv, hc⟩
  · exact absurd h (by simp)
  · -- the fixed range: a row whose category is the range's, read as a scalar
    obtain ⟨decl, hbd, hrest⟩ : ∃ d : EncodingDecl, dataDecl code = .ok d ∧
        readScalarData d c₁ = .ok (value, c') := by
      cases hb : dataDecl code with
      | error e =>
        exfalso
        simp only [hb, except_bind_error] at h
        exact absurd h (by simp)
      | ok v =>
        rw [hb] at h
        simp only [except_bind_ok, dataDecl_category_of_fixed (code := code) (w := _)
          (decl := v) (by assumption) hb] at h
        exact ⟨v, rfl, h⟩
    exact Or.inr (Or.inl ⟨⟨_, Or.inl (by assumption)⟩, decl, dataDecl_ok_mem hbd, hbd, hrest⟩)
  · -- the variable range
    obtain ⟨decl, hbd, hrest⟩ : ∃ d : EncodingDecl, dataDecl code = .ok d ∧
        readScalarData d c₁ = .ok (value, c') := by
      cases hb : dataDecl code with
      | error e =>
        exfalso
        simp only [hb, except_bind_error] at h
        exact absurd h (by simp)
      | ok v =>
        rw [hb] at h
        simp only [except_bind_ok, dataDecl_category_of_variable (code := code) (w := _)
          (decl := v) (by assumption) hb] at h
        exact ⟨v, rfl, h⟩
    exact Or.inr (Or.inl ⟨⟨_, Or.inr (by assumption)⟩, decl, dataDecl_ok_mem hbd, hbd, hrest⟩)
  · -- the compound range
    obtain ⟨decl, hbd, hrest⟩ : ∃ d : EncodingDecl, dataDecl code = .ok d ∧
        readCompound fuel d c₁ = .ok (value, c') := by
      cases hb : dataDecl code with
      | error e =>
        exfalso
        simp only [hb, except_bind_error] at h
        exact absurd h (by simp)
      | ok v =>
        rw [hb] at h
        simp only [except_bind_ok, dataDecl_category_of_compound (code := code) (w := _)
          (decl := v) (by assumption) hb] at h
        exact ⟨v, rfl, h⟩
    exact Or.inr (Or.inr (Or.inl ⟨⟨_, by assumption⟩, decl, dataDecl_ok_mem hbd, hbd, hrest⟩))
  · -- the array range
    obtain ⟨decl, hbd, hrest⟩ : ∃ d : EncodingDecl, dataDecl code = .ok d ∧
        readArrayData fuel d c₁ = .ok (value, c') := by
      cases hb : dataDecl code with
      | error e =>
        exfalso
        simp only [hb, except_bind_error] at h
        exact absurd h (by simp)
      | ok v =>
        rw [hb] at h
        simp only [except_bind_ok, dataDecl_category_of_array (code := code) (w := _)
          (decl := v) (by assumption) hb] at h
        exact ⟨v, rfl, h⟩
    exact Or.inr (Or.inr (Or.inr ⟨⟨_, by assumption⟩, decl, dataDecl_ok_mem hbd, hbd, hrest⟩))

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
