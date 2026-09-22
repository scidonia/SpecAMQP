import Proofs.ReadProgress
import Contracts.Codec

/-!
# The narrowest-form law's assembly

`Contracts/Codec.lean`'s `NarrowestEncoding` says the writer never spends more octets than an
accepted encoding of the same value. What the rungs below this file establish is the vocabulary to
prove it: the reader's own consumption per family, the rule read as an order, and the arithmetic
per family. This module writes down the *composition* — the law's full logical structure with each
family's comparison appearing as one named hypothesis — so the repository holds the shape of the
argument rather than an absence, and so the remaining work is measured as a list of declarations
rather than as a distance.

## Why the hypotheses are stated at the reader's own level

Each hypothesis is one family's comparison in the form the law's own quantifier needs: an accepted
read of that family, at an arbitrary cursor and fuel, has a canonical encoding of the value no
longer than the octets the read consumed (plus the constructor octet, where the family's reader is
reached through one — the tag is consumed by `readValue` before the family's reader is called, so
the family's own consumption is one octet short of the law's). Stating them at the reader's level
rather than over a whole buffer is what makes them independently checkable and composable: the
recursive families' comparisons take their sub-reads' comparisons as hypotheses, so one induction
over the reader's cluster turns all of them into theorems, and that induction needs no fact about
the *buffer* — it needs exactly these statements at smaller fuel.

## What this module does *not* assume

Nothing about the reader: `readValue_dispatch` (from the narrowest rung) reads the accepted
buffer's first octet, and the four cases below are its four branches. The law's statement is
untouched: what is proved here is that it follows from those hypotheses, at the statement
`Contracts/Codec.lean` gives it.

## The two text families

`string` and `symbol` are the two hypotheses a proof cannot yet discharge. Their comparisons need
the payload the writer produces (`text.toUTF8.toList`) to be the payload the reader read, which is
the UTF-8 round trip `String.fromUTF8? text.toUTF8 = some text` — not available in the pinned
closure, as `Proofs/ReadProgress.lean`'s sibling probe recorded — so they stand here as hypotheses
while the other five families' comparisons are separate declarations.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Spec.Codec
open SpecAMQP.Generated.Oasis (EncodingDecl encodings)
open SpecAMQP.Harness (Octets)

/-! ## Two reader facts the dispatch needs -/

/-- **`takeU8` advances the cursor by one octet.** The read of the frame's or value's first octet
is where the constructor octet comes from, and every family's consumption is measured from *after*
it: this is what turns the dispatched read's consumption into the law's, which counts the tag. -/
theorem takeU8_advances (c : Cursor) (code : UInt8) (c' : Cursor)
    (h : takeU8 c = .ok (code, c')) : c'.pos = c.pos + 1 := by
  simp only [takeU8] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  · exact absurd h (by simp)

/-- **A scalar read's row is a fixed or a variable one.** `readScalarData` dispatches on the row's
category and refuses the two recursive categories, so an accepted scalar read tells the assembly
which family comparison to apply. -/
theorem readScalarData_category (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor)
    (h : readScalarData decl c = .ok (value, c')) :
    decl.category = .fixed ∨ decl.category = .variable := by
  unfold readScalarData at h
  split at h
  · exact Or.inl (by assumption)
  · exact Or.inr (by assumption)
  · exact absurd h (by simp)

/-- **A variable-width read's row is one of the three variable owners.** The reader's own three
cases: `binary`, `string` and `symbol` are the owners it reads, and any other owner is refused, so
an accepted variable read names one of them. This is what lets the assembly choose between the
three variable-family comparisons rather than splitting on an owner it knows nothing about. -/
theorem readVariable_owner (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor)
    (h : readVariable decl c = .ok (value, c')) :
    decl.owner = "binary" ∨ decl.owner = "string" ∨ decl.owner = "symbol" := by
  obtain ⟨length, c₁, payload, c₂, hbe, hbp, hc, hcarries⟩ := readVariable_ok decl c value c' h
  unfold readVariable at h
  rw [hbe] at h
  simp only [except_bind_ok] at h
  -- the `do` block's `let (length, c) <- ...` leaves the pair match unreduced
  try dsimp only at h
  rw [hbp] at h
  simp only [except_bind_ok] at h
  split at h <;> try (split at h)
  · exact Or.inl (by assumption)
  · exact Or.inr (Or.inl (by assumption))
  · exact Or.inr (Or.inr (by assumption))
  · exact absurd h (by simp)

/-! ## The assembly -/

/-- **The narrowest-form law, from the seven families' comparisons.**

The law as `Contracts/Codec.lean` states it, proved from one comparison per family. The argument is
the dispatch: an accepted buffer that decodes in full is an accepted `readValue` from the buffer's
start, whose first octet names exactly one of the four reader categories, and each category's case
is its family's comparison plus the arithmetic that turns the family's consumption into the law's
(the constructor octet the caller consumed, and the cursor equality the decode hands back).

The hypotheses are the remaining distance and nothing else: five of them can be discharged from
facts already in the tree (the fixed family's per-owner rule, the binary variable family's, and the
compounds', arrays' and described case's arithmetic at their sub-reads' comparisons), and the two
text families' need the UTF-8 round trip the pinned closure does not carry. -/
theorem narrowest_encoding_of_comparisons
    (hfixed : ∀ (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor),
      decl ∈ encodings → decl.category = .fixed →
      readScalarData decl c = .ok (value, c') →
      ∃ canonical : Octets, encodeValue value = .ok canonical ∧
        canonical.size ≤ 1 + (c'.pos - c.pos))
    (hbinary : ∀ (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor),
      decl ∈ encodings → decl.owner = "binary" →
      readScalarData decl c = .ok (value, c') →
      ∃ canonical : Octets, encodeValue value = .ok canonical ∧
        canonical.size ≤ 1 + (c'.pos - c.pos))
    (hstring : ∀ (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor),
      decl ∈ encodings → decl.owner = "string" →
      readScalarData decl c = .ok (value, c') →
      ∃ canonical : Octets, encodeValue value = .ok canonical ∧
        canonical.size ≤ 1 + (c'.pos - c.pos))
    (hsymbol : ∀ (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor),
      decl ∈ encodings → decl.owner = "symbol" →
      readScalarData decl c = .ok (value, c') →
      ∃ canonical : Octets, encodeValue value = .ok canonical ∧
        canonical.size ≤ 1 + (c'.pos - c.pos))
    (hcompound : ∀ (fuel : Nat) (decl : EncodingDecl) (c : Cursor) (value : Value)
      (c' : Cursor), readCompound fuel decl c = .ok (value, c') →
      ∃ canonical : Octets, encodeValue value = .ok canonical ∧
        canonical.size ≤ 1 + (c'.pos - c.pos))
    (harray : ∀ (fuel : Nat) (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor),
      readArrayData fuel decl c = .ok (value, c') →
      ∃ canonical : Octets, encodeValue value = .ok canonical ∧
        canonical.size ≤ 1 + (c'.pos - c.pos))
    (hdescribed : ∀ (fuel : Nat) (c : Cursor) (descriptor inner : Value) (c₂ c₃ : Cursor),
      readValue fuel c = .ok (descriptor, c₂) → readValue fuel c₂ = .ok (inner, c₃) →
      ∃ canonical : Octets, encodeValue (.described descriptor inner) = .ok canonical ∧
        canonical.size ≤ 1 + (c₃.pos - c.pos)) :
    SpecAMQP.Contracts.NarrowestEncoding := by
  intro bytes value consumed hdecode hfull
  -- the decode hands back the reader's cursor position as the consumed count
  unfold decodeValue at hdecode
  split at hdecode
  · rename_i v c hread
    simp only [Except.ok.injEq, Prod.mk.injEq] at hdecode
    obtain ⟨hval, hcons⟩ := hdecode
    -- the read's own value is the one the decode reports: eliminate the case binding for it
    subst v
    -- the read started at the buffer's own start and consumed the whole buffer
    have hend : c.pos = bytes.size := by omega
    cases hs : bytes.size with
    | zero =>
      -- the depth budget is the number of octets, so a zero-length buffer is refused
      rw [hs] at hread
      simp only [readValue] at hread
      exact absurd hread (by simp)
    | succ n =>
      rw [hs] at hread
      obtain ⟨code, c₁, hbu, hcases⟩ := readValue_dispatch n ⟨bytes, 0⟩ value c hread
      have htag : c₁.pos = 0 + 1 := takeU8_advances ⟨bytes, 0⟩ code c₁ hbu
      rcases hcases with
        ⟨hclass, descriptor, inner, c₂, c₃, hval, hone, hd, hi, hc⟩ |
        ⟨hclass, decl, hmem, hdd, hsc⟩ |
        ⟨hclass, decl, hmem, hdd, hco⟩ |
        ⟨hclass, decl, hmem, hdd, har⟩
      · -- a described value: its own framing and the two sub-values
        subst hval
        obtain ⟨canonical, henc, hsize⟩ := hdescribed n c₁ descriptor inner c₂ c₃ hd hi
        have hcpos : c₃.pos = c.pos := by rw [hc]
        exact ⟨canonical, henc, by omega⟩
      · -- a scalar row: one of the four scalar families, measured after the tag
        rcases readScalarData_category decl c₁ value c hsc with hcat | hcat
        · obtain ⟨canonical, henc, hsize⟩ := hfixed decl c₁ value c hmem hcat hsc
          exact ⟨canonical, henc, by omega⟩
        · have hvar : readVariable decl c₁ = .ok (value, c) := by
            unfold readScalarData at hsc
            rw [hcat] at hsc
            exact hsc
          by_cases hbin : decl.owner = "binary"
          · obtain ⟨canonical, henc, hsize⟩ := hbinary decl c₁ value c hmem hbin hsc
            exact ⟨canonical, henc, by omega⟩
          · by_cases hstr : decl.owner = "string"
            · obtain ⟨canonical, henc, hsize⟩ := hstring decl c₁ value c hmem hstr hsc
              exact ⟨canonical, henc, by omega⟩
            · have hsym : decl.owner = "symbol" := by
                rcases readVariable_owner decl c₁ value c hvar with h | h | h
                · exact absurd h hbin
                · exact absurd h hstr
                · exact h
              obtain ⟨canonical, henc, hsize⟩ := hsymbol decl c₁ value c hmem hsym hsc
              exact ⟨canonical, henc, by omega⟩
      · -- a compound value: its own size and count
        obtain ⟨canonical, henc, hsize⟩ := hcompound n decl c₁ value c hco
        exact ⟨canonical, henc, by omega⟩
      · -- an array: its size, count and element constructor
        obtain ⟨canonical, henc, hsize⟩ := harray n decl c₁ value c har
        exact ⟨canonical, henc, by omega⟩
  · exact absurd hdecode (by simp)

end SpecAMQP.Proofs
