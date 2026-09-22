import Proofs.CodecRoundTripNarrowest

/-!
# The reader never moves its cursor backwards

The narrowest-form rung reads the reader's consumption off the reader's own measurement: a
compound's `SIZE` counts the octets after it, and the reader compares that number against
`c.pos - start`, the window it actually read. A *measurement*, though, is not an *advance*: a
subtraction truncated at zero would report a size for a cursor that went backwards, so nothing
in the measurement form says the window's end is past its start. This module is the fact that
makes the measurement usable as a size — every reader in the value cluster leaves its cursor at
or after where it found it — and therefore converts the window statements into advances of the
form `c'.pos = start + size`, which is what a proof comparing sizes can add up.

## Why the induction is joint

`readValue`, `readItems`, `readCompound`, `readArrayData`, `readElements` and `readElementsLoop`
are one `mutual` block, and their progress facts cannot be separated: at fuel `n + 1` a clause
may call an *earlier* clause at its *own* fuel (`readCompound` reads `readItems` at the same
fuel, and the array loop reads the compound and array readers at the same fuel), and any clause
may call another at the predecessor fuel. So the six facts are proved as one package by
induction on the fuel, each step establishing the six clauses in dependency order — value,
items, compound, array, elements, elements loop — and reaching for the induction hypothesis
whenever a call has a smaller fuel. Only the array loop needs a second induction, on its count,
because its recursive call keeps the fuel and decreases the count.

## The two mechanical facts a reader of this file needs

`exists_of_bind_ok` recovers the left side of an accepted bind, which is what lets these proofs
read the reader's own calls off an accepted result rather than re-deriving each `do`-block. Its
continuation is left as written, so a `do`-block's `let (a, b) ← …` pattern is still an
unreduced `match` on a pair; the `dsimp` that follows each use is what reduces it (and is written
`try dsimp`, because where there is no redex to reduce it has nothing to do). Without it a
following `split at h` splits that pair match instead of the reader's own decision, and the
resulting branch is the one a proof is not written for.

Nothing about the buffer beyond what `takeBytes_advances`, `takeBe_advances`, the rung's
`readFixed_consumes` and that rung's `readVariable_consumes` state is assumed here: the scalar
readers' advances are those two reading-off steps, and the rest is the primitive `take`
functions' own arithmetic.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Spec.Codec
open SpecAMQP.Generated.Oasis (EncodingDecl)
open SpecAMQP.Harness (Octets)

/-! ## An accepted bind, taken apart

`except_bind_ok` reduces an accepted bind whose left side is already written as a literal. A
proof that starts from *the whole read having accepted* has the inverse problem: it must recover
the left side's value and the continuation's equation. This is that inverse. -/
theorem exists_of_bind_ok {ε α β : Type _} {f : Except ε α} {g : α → Except ε β} {b : β}
    (h : (f >>= g) = .ok b) : ∃ a, f = .ok a ∧ g a = .ok b := by
  cases f with
  | error e =>
    simp only [except_bind_error] at h
    exact absurd h (by simp)
  | ok a => exact ⟨a, rfl, by simpa only [except_bind_ok] using h⟩

/-! ## The cursor primitives and the scalar readers -/

/-- **`takeBytes` never moves its cursor backwards.** Stated as the advance the primitive already
has: the cursor it returns is the one it was given, shifted by the width it took. -/
theorem takeBytes_progress (n : Nat) (c : Cursor) (bytes : Octets) (c' : Cursor)
    (h : takeBytes n c = .ok (bytes, c')) : c.pos ≤ c'.pos := by
  have hadv := (takeBytes_advances n c bytes c' h).1
  omega

/-- **`takeBe` never moves its cursor backwards.** -/
theorem takeBe_progress (width : Nat) (c : Cursor) (v : Nat) (c' : Cursor)
    (h : takeBe width c = .ok (v, c')) : c.pos ≤ c'.pos := by
  have hadv := takeBe_advances width c v c' h
  omega

/-- **`takeU8` never moves its cursor backwards.** One octet is taken where the buffer has one,
and the cursor that comes back is one past the one that went in. -/
theorem takeU8_progress (c : Cursor) (code : UInt8) (c' : Cursor)
    (h : takeU8 c = .ok (code, c')) : c.pos ≤ c'.pos := by
  simp only [takeU8] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    have hpos : c'.pos = c.pos + 1 := by rw [← h.2]
    omega
  · exact absurd h (by simp)

/-- **A fixed-width row's read advances by the row's width.** -/
theorem readFixed_progress (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readFixed decl c = .ok (v, c')) : c.pos ≤ c'.pos := by
  have hadv := readFixed_consumes decl c v c' h
  omega

/-- **A variable-width row's read advances by the row's width plus its length field.** -/
theorem readVariable_progress (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readVariable decl c = .ok (v, c')) : c.pos ≤ c'.pos := by
  obtain ⟨length, payload, hsize, hbound, hpos, hcarries⟩ :=
    readVariable_consumes decl c v c' h
  omega

/-- **A scalar row's read advances, whichever of the two categories it declares.** -/
theorem readScalarData_progress (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readScalarData decl c = .ok (v, c')) : c.pos ≤ c'.pos := by
  rcases readScalarData_consumes decl c v c' h with ⟨hcat, hpos⟩ | ⟨hcat, length, payload,
    hsize, hbound, hpos, hcarries⟩
  · omega
  · omega

/-! ## The cluster -/

/-- **Every reader in the value cluster leaves its cursor at or after where it found it.**

Six clauses, one per reader of the `mutual` block, in the order a step proves them: the value
reader, the item loop, the compound reader, the array reader, the array's element entry point and
its element loop. A caller with an accepted read of any of the six gets `c.pos ≤ c'.pos`. -/
theorem readValue_progress : ∀ (fuel : Nat),
    (∀ (c : Cursor) (v : Value) (c' : Cursor), readValue fuel c = .ok (v, c') → c.pos ≤ c'.pos) ∧
    (∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
      readItems fuel count c = .ok (items, c') → c.pos ≤ c'.pos) ∧
    (∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
      readCompound fuel decl c = .ok (v, c') → c.pos ≤ c'.pos) ∧
    (∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
      readArrayData fuel decl c = .ok (v, c') → c.pos ≤ c'.pos) ∧
    (∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor) (items : List Value)
      (c' : Cursor), readElements fuel elementDecl count c = .ok (items, c') → c.pos ≤ c'.pos) ∧
    (∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor) (items : List Value)
      (c' : Cursor), readElementsLoop fuel elementDecl count c = .ok (items, c') →
        c.pos ≤ c'.pos) := by
  intro fuel
  induction fuel with
  | zero =>
    -- At fuel 0 the value, item, array and element readers refuse outright; the compound reader
    -- still reads its two size fields and then refuses at the item loop, and the element loop's
    -- zero-count case accepts without reading anything.
    have hValue : ∀ (c : Cursor) (v : Value) (c' : Cursor),
        readValue 0 c = .ok (v, c') → c.pos ≤ c'.pos := by
      intro c v c' h
      simp only [readValue] at h
      exact absurd h (by simp)
    have hItems : ∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
        readItems 0 count c = .ok (items, c') → c.pos ≤ c'.pos := by
      intro count c items c' h
      simp only [readItems] at h
      exact absurd h (by simp)
    have hCompound : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readCompound 0 decl c = .ok (v, c') → c.pos ≤ c'.pos := by
      intro decl c v c' h
      unfold readCompound at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p1 := takeBe_progress decl.width c size c₁ h1
      have p2 := takeBe_progress decl.width c₁ count c₂ h2
      split at h
      · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p3 := hItems count c₂ items c₃ h3
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          omega
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
          try dsimp only at h
          have p3 := hItems count c₂ items c₃ h3
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]
            omega
          · exact absurd h (by simp)
      · exact absurd h (by simp)
    have hArrayData : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readArrayData 0 decl c = .ok (v, c') → c.pos ≤ c'.pos := by
      intro decl c v c' h
      simp only [readArrayData] at h
      exact absurd h (by simp)
    have hElements : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElements 0 elementDecl count c = .ok (items, c') → c.pos ≤ c'.pos := by
      intro elementDecl count c items c' h
      simp only [readElements] at h
      exact absurd h (by simp)
    have hElementsLoop : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElementsLoop 0 elementDecl count c = .ok (items, c') → c.pos ≤ c'.pos := by
      intro elementDecl count
      induction count with
      | zero =>
        intro c items c' h
        simp only [readElementsLoop] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        have hpos : c'.pos = c.pos := by rw [h.2]
        omega
      | succ k ihk =>
        intro c items c' h
        unfold readElementsLoop at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p1 : c.pos ≤ c₁.pos := by
          -- The element read is a decision on the element declaration, whose `some` case is a
          -- second decision on the row's category. The alternatives below are matched by type
          -- rather than by position, so the two splits need not be counted.
          split at h1 <;> try (split at h1)
          all_goals first
            | (obtain ⟨⟨descriptor, ca⟩, hd, h1⟩ := exists_of_bind_ok h1
               try dsimp only at h1
               obtain ⟨⟨inner, cb⟩, hi, h1⟩ := exists_of_bind_ok h1
               try dsimp only at h1
               have pa := hValue c descriptor ca hd
               have pb := hValue ca inner cb hi
               simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h1
               rw [← h1.2]
               omega)
            | (have := readScalarData_progress _ c item c₁ h1
               omega)
            | (have := hCompound _ c item c₁ h1
               omega)
            | (have := hArrayData _ c item c₁ h1
               omega)
        have p2 := ihk c₁ rest c₂ h2
        simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        omega
    exact ⟨hValue, hItems, hCompound, hArrayData, hElements, hElementsLoop⟩
  | succ n ih =>
    obtain ⟨ihValue, ihItems, ihCompound, ihArrayData, ihElements, ihElementsLoop⟩ := ih
    have hValue : ∀ (c : Cursor) (v : Value) (c' : Cursor),
        readValue (n + 1) c = .ok (v, c') → c.pos ≤ c'.pos := by
      intro c v c' h
      unfold readValue at h
      obtain ⟨⟨code, c₁⟩, hu, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p0 := takeU8_progress c code c₁ hu
      split at h
      -- The classification is an or-pattern over the four reader categories, so `split` gives one
      -- goal per category: the alternatives below are matched by type rather than by position.
      all_goals first
        | (-- the descriptor prefix: two values, both at the predecessor fuel
           obtain ⟨⟨descriptor, c₂⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           obtain ⟨⟨inner, c₃⟩, h2, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           have p1 := ihValue c₁ descriptor c₂ h1
           have p2 := ihValue c₂ inner c₃ h2
           simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
           rw [← h.2]
           omega)
        | (-- a category's row, and the reader that category selects
           obtain ⟨decl, hd, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           split at h <;> try (split at h)
           all_goals first
             | (have := readScalarData_progress decl c₁ v c' h
                omega)
             | (have := ihCompound decl c₁ v c' h
                omega)
             | (have := ihArrayData decl c₁ v c' h
                omega))
        | exact absurd h (by simp)
    have hItems : ∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
        readItems (n + 1) count c = .ok (items, c') → c.pos ≤ c'.pos := by
      intro count
      cases count with
      | zero =>
        intro c items c' h
        simp only [readItems] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        have hpos : c'.pos = c.pos := by rw [h.2]
        omega
      | succ k =>
        intro c items c' h
        unfold readItems at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p1 := ihValue c item c₁ h1
        have p2 := ihItems k c₁ rest c₂ h2
        simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        omega
    have hCompound : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readCompound (n + 1) decl c = .ok (v, c') → c.pos ≤ c'.pos := by
      intro decl c v c' h
      unfold readCompound at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p1 := takeBe_progress decl.width c size c₁ h1
      have p2 := takeBe_progress decl.width c₁ count c₂ h2
      split at h
      · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p3 := hItems count c₂ items c₃ h3
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          omega
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
          try dsimp only at h
          have p3 := hItems count c₂ items c₃ h3
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]
            omega
          · exact absurd h (by simp)
      · exact absurd h (by simp)
    have hArrayData : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readArrayData (n + 1) decl c = .ok (v, c') → c.pos ≤ c'.pos := by
      intro decl c v c' h
      unfold readArrayData at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p1 := takeBe_progress decl.width c size c₁ h1
      have p2 := takeBe_progress decl.width c₁ count c₂ h2
      split at h
      · exact absurd h (by simp)
      · obtain ⟨⟨constructor, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p3 := takeU8_progress c₂ constructor c₃ h3
        obtain ⟨elementDecl, h4, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨items, c₄⟩, h5, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p4 := ihElements elementDecl count c₃ items c₄ h5
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          omega
        · exact absurd h (by simp)
    have hElements : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElements (n + 1) elementDecl count c = .ok (items, c') → c.pos ≤ c'.pos := by
      intro elementDecl count c items c' h
      simp only [readElements] at h
      exact ihElementsLoop elementDecl count c items c' h
    have hElementsLoop : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElementsLoop (n + 1) elementDecl count c = .ok (items, c') → c.pos ≤ c'.pos := by
      intro elementDecl count
      induction count with
      | zero =>
        intro c items c' h
        simp only [readElementsLoop] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        have hpos : c'.pos = c.pos := by rw [h.2]
        omega
      | succ k ihk =>
        intro c items c' h
        unfold readElementsLoop at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p1 : c.pos ≤ c₁.pos := by
          -- The element read is a decision on the element declaration, whose `some` case is a
          -- second decision on the row's category. The alternatives below are matched by type
          -- rather than by position, so the two splits need not be counted.
          split at h1 <;> try (split at h1)
          all_goals first
            | (obtain ⟨⟨descriptor, ca⟩, hd, h1⟩ := exists_of_bind_ok h1
               try dsimp only at h1
               obtain ⟨⟨inner, cb⟩, hi, h1⟩ := exists_of_bind_ok h1
               try dsimp only at h1
               have pa := hValue c descriptor ca hd
               have pb := hValue ca inner cb hi
               simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h1
               rw [← h1.2]
               omega)
            | (have := readScalarData_progress _ c item c₁ h1
               omega)
            | (have := hCompound _ c item c₁ h1
               omega)
            | (have := hArrayData _ c item c₁ h1
               omega)
        have p2 := ihk c₁ rest c₂ h2
        simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        omega
    exact ⟨hValue, hItems, hCompound, hArrayData, hElements, hElementsLoop⟩

/-! ## The measured windows, as advances

What the law's size comparisons need, read off the rung's measurements plus the progress fact
above: the window's end is its start *plus* the declared size, with no truncation left in it. -/

/-- **A compound row's window is an advance.** The rung's `readCompound_consumes` states the
window as `c'.pos - start = size`, a subtraction that would report `size` for a cursor that moved
backwards — so the measurement alone does not say the window's end is past its start. The tail is
what says it: the count field and the item loop both advance (`takeBe_progress` and the progress
fact above), so the window's start is at or before its end and the measurement is an addition.
With that, the accepted size can be added up against the canonical encoding's. -/
theorem readCompound_advance (fuel : Nat) (decl : EncodingDecl) (c : Cursor) (value : Value)
    (c' : Cursor) (h : readCompound fuel decl c = .ok (value, c')) :
    ∃ size count : Nat, ∃ items : List Value, ∃ start : Cursor,
      start.pos = c.pos + decl.width ∧
      c'.pos = start.pos + size ∧
      size < 2 ^ (8 * decl.width) ∧
      count < 2 ^ (8 * decl.width) ∧
      CompoundCarries value items := by
  obtain ⟨size, count, items, start, hstart, hmeasure, hsize, hcount, hcarries⟩ :=
    readCompound_consumes fuel decl c value c' h
  refine ⟨size, count, items, start, hstart, ?_, hsize, hcount, hcarries⟩
  unfold readCompound at h
  obtain ⟨⟨size', s₁⟩, h1, h⟩ := exists_of_bind_ok h
  try dsimp only at h
  obtain ⟨⟨count', c₂⟩, h2, h⟩ := exists_of_bind_ok h
  try dsimp only at h
  have hs₁ : s₁.pos = start.pos := by rw [takeBe_advances decl.width c size' s₁ h1, hstart]
  have p1 : start.pos ≤ c₂.pos := by
    rw [← hs₁]
    exact takeBe_progress decl.width s₁ count' c₂ h2
  split at h
  · obtain ⟨⟨items', c₃⟩, h3, h⟩ := exists_of_bind_ok h
    try dsimp only at h
    have p2 : c₂.pos ≤ c₃.pos := (readValue_progress fuel).2.1 count' c₂ items' c₃ h3
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      have hc : c'.pos = c₃.pos := by rw [← h.2]
      rw [hc] at hmeasure
      omega
    · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · obtain ⟨⟨items', c₃⟩, h3, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p2 : c₂.pos ≤ c₃.pos := (readValue_progress fuel).2.1 count' c₂ items' c₃ h3
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        have hc : c'.pos = c₃.pos := by rw [← h.2]
        rw [hc] at hmeasure
        omega
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **An array row's window is an advance.** The companion of `readCompound_advance`: the tail
here is the count field, the element constructor and the element loop, each of which advances, so
the measurement's window is an addition as well. -/
theorem readArrayData_advance (fuel : Nat) (decl : EncodingDecl) (c : Cursor) (value : Value)
    (c' : Cursor) (h : readArrayData fuel decl c = .ok (value, c')) :
    ∃ size count : Nat, ∃ constructor : UInt8, ∃ items : List Value, ∃ start : Cursor,
      start.pos = c.pos + decl.width ∧
      c'.pos = start.pos + size ∧
      size < 2 ^ (8 * decl.width) ∧
      count < 2 ^ (8 * decl.width) ∧
      count ≤ arrayElementLimit ∧
      value = .array constructor items := by
  obtain ⟨size, count, constructor, items, start, hstart, hmeasure, hsize, hcount, hlimit,
    hvalue⟩ := readArrayData_consumes fuel decl c value c' h
  refine ⟨size, count, constructor, items, start, hstart, ?_, hsize, hcount, hlimit, hvalue⟩
  cases fuel with
  | zero =>
    -- at fuel 0 the reader refuses before reading anything
    simp only [readArrayData] at h
    exact absurd h (by simp)
  | succ f =>
    unfold readArrayData at h
    obtain ⟨⟨size', s₁⟩, h1, h⟩ := exists_of_bind_ok h
    try dsimp only at h
    obtain ⟨⟨count', c₂⟩, h2, h⟩ := exists_of_bind_ok h
    try dsimp only at h
    have hs₁ : s₁.pos = start.pos := by rw [takeBe_advances decl.width c size' s₁ h1, hstart]
    have p1 : start.pos ≤ c₂.pos := by
      rw [← hs₁]
      exact takeBe_progress decl.width s₁ count' c₂ h2
    split at h
    · exact absurd h (by simp)
    · obtain ⟨⟨constructor', c₃⟩, h3, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p2 : c₂.pos ≤ c₃.pos := takeU8_progress c₂ constructor' c₃ h3
      obtain ⟨elementDecl, h4, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨items', c₄⟩, h5, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p3 : c₃.pos ≤ c₄.pos :=
        (readValue_progress f).2.2.2.2.1 elementDecl count' c₃ items' c₄ h5
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        have hc : c'.pos = c₄.pos := by rw [← h.2]
        rw [hc] at hmeasure
        omega
      · exact absurd h (by simp)

end SpecAMQP.Proofs
