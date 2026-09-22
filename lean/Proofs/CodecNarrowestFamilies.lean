import Proofs.CodecNarrowestAssembly

/-!
# The per-family comparisons

`Proofs/CodecNarrowestAssembly.lean` states the narrowest-form law as following from one comparison
per family. This module discharges the families that need no fact beyond the tree, starting with the
binary variable family. Nothing here changes the law's statement or any definition: each comparison
is a declaration that discharges one of the assembly's hypotheses.

## What a family's comparison needs, and what a narrowing would do

The comparison for a family is: an accepted read from one of its rows has a canonical encoding no
longer than the tag plus the octets the read consumed. Three ingredients per family — the reader's
own account of what it read (`…_consumes`), the table facts that make the writer's row lookup
succeed at the width it asks for, and the rule as an order (`lengthWidthOf_le_of_field` and its
compound twin). The interesting part of each is what happens if the comparison is *weakened*: the
one read off an accepted buffer, the tag is genuinely spent (forgetting it makes the family
comparisons loose by exactly the constructor octet), and the "there is a canonical encoding" half is
never vacuous because the writer refuses values whose row is missing from the table.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Spec.Codec
open SpecAMQP.Generated.Oasis (EncodingDecl encodings)
open SpecAMQP.Harness (Octets)

/-! ## The table, read rather than transcribed -/

/-- **The rows the binary writer asks for are in the declared surface.** The writer selects its row
by owner and width and asks for width 1 or width 4 depending on the payload's length. Decided over
the generated encodings: a table missing one of those rows would make the writer refuse a value the
reader had just accepted, which is the failure a comparison must exclude. -/
theorem binary_rows_exist :
    (match rowOf "binary" 1 with | .ok _ => true | .error _ => false) = true ∧
    (match rowOf "binary" 4 with | .ok _ => true | .error _ => false) = true := by
  decide

/-- **The writer's row for a binary payload exists, at the width it asked for.** The existential
form of `binary_rows_exist`, so the writer's `do` block can be read off; `rowOf_mem` says the row
found is the table's own and declares the width that was asked for. -/
theorem rowOf_binary_width (w : Nat) (hw : w = 1 ∨ w = 4) :
    ∃ decl' : EncodingDecl, rowOf "binary" w = .ok decl' ∧ decl'.width = w := by
  rcases hw with rfl | rfl
  · cases hb : rowOf "binary" 1 with
    | error e =>
      have hall := binary_rows_exist.1
      rw [hb] at hall
      simp at hall
    | ok d => exact ⟨d, rfl, rowOf_width "binary" _ d hb⟩
  · cases hb : rowOf "binary" 4 with
    | error e =>
      have hall := binary_rows_exist.2
      rw [hb] at hall
      simp at hall
    | ok d => exact ⟨d, rfl, rowOf_width "binary" _ d hb⟩

/-- **Every row the table declares for `binary` is a variable-width one.** The reader dispatches on
the row's category, so a comparison about an accepted binary read has to know which reader ran:
`binary` is a variable-width owner in the declared surface, read off the table. -/
theorem binary_rows_are_variable :
    (encodings.filter (fun decl => decl.owner == "binary")).all
      (fun decl => decl.category == .variable) = true := by
  decide

/-- **A row the table declares for `binary` declares a variable-width encoding.** -/
theorem binary_row_variable (decl : EncodingDecl) (hmem : decl ∈ encodings)
    (howner : decl.owner = "binary") : decl.category = .variable := by
  have hall := binary_rows_are_variable
  rw [List.all_eq_true] at hall
  have hmem' : decl ∈ encodings.filter (fun d => d.owner == "binary") := by
    rw [List.mem_filter]
    exact ⟨hmem, by simpa using howner⟩
  have h := hall decl hmem'
  simpa using h

/-! ## The reader's own account of a binary read -/

/-- **An accepted binary read, in the reader's own terms.** The row's width, the length its field
carried, the payload those octets were, and the value the owner case built — the value pinned to
`.binary payload` because that is the branch the reader's owner match took. The four facts are read
off `readVariable_ok` and the reader's own consumption, so nothing about an arbitrary buffer is
assumed. -/
theorem readVariable_binary_value (decl : EncodingDecl) (c : Cursor) (value : Value) (c' : Cursor)
    (h : readVariable decl c = .ok (value, c')) (howner : decl.owner = "binary") :
    ∃ length : Nat, ∃ payload : Octets,
      payload.size = length ∧
      value = .binary payload ∧
      length < 2 ^ (8 * decl.width) ∧
      c'.pos = c.pos + decl.width + length := by
  obtain ⟨length, c₁, payload, c₂, hbe, hbp, hc, hcarries⟩ := readVariable_ok decl c value c' h
  have hshape : value = .binary payload := by
    unfold readVariable at h
    rw [hbe] at h
    simp only [except_bind_ok] at h
    try dsimp only at h
    rw [hbp] at h
    simp only [except_bind_ok] at h
    try dsimp only at h
    simp only [howner] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  obtain ⟨hadv, hsize⟩ := takeBytes_advances length c₁ payload c₂ hbp
  have hfield : c₁.pos = c.pos + decl.width := takeBe_advances decl.width c length c₁ hbe
  refine ⟨length, payload, hsize, hshape, ?_, ?_⟩
  · rw [two_pow_eight_mul]
    exact takeBe_lt decl.width c length c₁ hbe
  · rw [← hc, hadv, hfield]

/-! ## The writer's own account of a binary value -/

/-- **The octets the writer spends on a binary payload.** The writer's row lookup, its variable-data
case and its length prefix, in one step: given the row it asks for (with the owner the row is looked
up by and the category the writer dispatches on), the writer's octets are the row's constructor
octet followed by what `lengthPrefixed` produced. Stated separately from the comparison so that the
comparison's argument is the widths and not the writer's `do`-block structure. -/
theorem writeValue_binary (payload : Octets) (decl' : EncodingDecl) (field : List UInt8)
    (hrow : rowOf "binary" (if payload.size ≤ 255 then 1 else 4) = .ok decl')
    (howner : decl'.owner = "binary") (hcat : decl'.category = .variable)
    (hlp : lengthPrefixed decl' payload.toList = .ok field) :
    writeValue (.binary payload) = .ok (tagOf decl' ++ field) := by
  simp only [writeValue, hrow, emitScalar, writeVariableData, howner, hcat, hlp,
    except_bind_ok, except_pure_ok]

/-! ## The comparison -/

/-- **An accepted binary encoding is no shorter than the canonical one.**

The family's comparison in the form the assembly consumes. The canonical octets are the row the
writer asks for, its length field and then the payload; the accepted octets are the row's width, the
length field and then the same payload; and the rule's width is no wider than the row's, so the
comparison is the widths.

Two things about the statement's strength, since a narrowing is the thing to check here. Dropping
the `1 +` would make it false: the tag is genuinely spent on the accepted side and genuinely written
on the canonical side, so the comparison is between `1 + width'` and `1 + width` and not between the
widths alone. And the existential is not vacuous — the writer's row lookup is a real obligation,
which is what the decided table fact above is for; without it the comparison would be about a
writer that refuses the value the reader accepted.
-/
theorem readScalarData_binary_canonical_le (decl : EncodingDecl) (c : Cursor) (value : Value)
    (c' : Cursor) (hmem : decl ∈ encodings) (howner : decl.owner = "binary")
    (h : readScalarData decl c = .ok (value, c')) :
    ∃ canonical : Octets, encodeValue value = .ok canonical ∧
      canonical.size ≤ 1 + (c'.pos - c.pos) := by
  -- the row is a variable-width one, so the family's reader is `readVariable`
  have hcat := binary_row_variable decl hmem howner
  have hvar : readVariable decl c = .ok (value, c') := by
    unfold readScalarData at h
    rw [hcat] at h
    exact h
  obtain ⟨length, payload, hsize, hshape, hbound, hpos⟩ :=
    readVariable_binary_value decl c value c' hvar howner
  -- the width the writer will ask for is one of the table's two, and the row is there
  have hwidth : decl.width = 1 ∨ decl.width = 4 :=
    variable_row_width decl hmem (Or.inl howner)
  have hw : lengthWidthOf payload.size = 1 ∨ lengthWidthOf payload.size = 4 := by
    unfold lengthWidthOf
    split <;> simp
  obtain ⟨decl', hrow, hdecl'⟩ := rowOf_binary_width _ hw
  have hrowIf : rowOf "binary" (if payload.size ≤ 255 then 1 else 4) = .ok decl' := by
    simpa only [lengthWidthOf] using hrow
  have hrowMem := rowOf_mem hrow
  have howner' : decl'.owner = "binary" := hrowMem.2.1
  have hcat' : decl'.category = .variable := binary_row_variable decl' hrowMem.1 howner'
  -- the rule's width is no wider than the row the reader consumed
  have hcarries : lengthWidthOf payload.size ≤ decl.width :=
    lengthWidthOf_le_of_field payload.size decl.width hwidth (by simpa [hsize] using hbound)
  -- and it carries the length it was chosen for, which is what makes the writer's field fit
  have hcarry : payload.size < 2 ^ (8 * lengthWidthOf payload.size) := by
    by_cases h255 : payload.size ≤ 255
    · rw [lengthWidthOf_narrow payload.size h255]
      have h256 : (2 : Nat) ^ (8 * 1) = 256 := by decide
      rw [h256]
      omega
    · rw [lengthWidthOf_wide payload.size (by omega)]
      have hb : payload.size < 2 ^ (8 * decl.width) := by simpa [hsize] using hbound
      have h256 : (2 : Nat) ^ (8 * 1) = 256 := by decide
      have hbig : (2 : Nat) ^ (8 * 4) = 4294967296 := by decide
      rcases hwidth with h1 | h4
      · rw [h1, h256] at hb
        omega
      · rw [h4] at hb
        rw [hbig] at hb ⊢
        exact hb
  have hfield : lengthPrefixed decl' payload.toList = .ok (beOctets decl'.width payload.toList.length
      ++ payload.toList) :=
    lengthPrefixed_eq decl' payload.toList (by
      rw [hdecl']
      simpa [Array.length_toList] using hcarry)
  refine ⟨(tagOf decl' ++ (beOctets decl'.width payload.toList.length ++ payload.toList)).toArray,
    ?_, ?_⟩
  · rw [encodeValue, hshape]
    rw [writeValue_binary payload decl' _ hrowIf howner' hcat' hfield]
    simp only [except_bind_ok, except_pure_ok]
  · -- the goal counts the canonical octets; `hcarries` is about the payload's size, so the
    -- reader's own identity for it must be rewritten in the same direction as the goal's
    rw [hsize] at hcarries
    simp only [List.size_toArray, List.length_append, beOctets_length, tagOf,
      List.length_singleton, Array.length_toList, hsize, hdecl']
    omega

end SpecAMQP.Proofs
