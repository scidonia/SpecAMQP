import Contracts.Conformance
import Proofs.ValueCarrierAgreement
import Proofs.FrameConformance
import Proofs.ReadProgress
import Proofs.FrameSendConformance
import Spec.Codec
import Ref.Value

/-!
# The wire readers' agreement

`Proofs.FrameConformance.ValueLayersAgree` is the value layer's claim in the *wire* vocabulary: what
the reference's reader reads off a buffer, the specification's reader reads too - the same octets
consumed and bodies the frame layer views the same way - or a refusal of the same class. This module
is that claim's development, and the claim is **proved**: `valueLayersAgree` below is a theorem of
`Proofs.FrameConformance.ValueLayersAgree` with no hypotheses, so the frame layer's
`frame_conformance_public` now applies to `specFrame`/`refFrame` without one. Nothing in it is
conditional on `ElementsDecideAt` or `ElementsDecideBelow` or on any other named hypothesis about the
readers: both are discharged by `elementsDecideBelow_all` / `elementsDecideAt_all`, which are read off
the same induction that produces the value law. Landed: the formulation (with the fuel bound
its truth needs), the base case, the octet step and its payload bridges, the branch *pattern*, and
**38 of the 40 arms** — the described branch and every row that reads no recursive value: the five
other zero-width rows, the one-octet payloads, the wide unsigned and `char` widths, the seven *signed*
widths, the six opaque widths, and the six variable rows — together with the four *recursive* arms
that read a compound or a map (`arm_0xC0`, `arm_0xC1`, `arm_0xD0`, `arm_0xD1`). Also landed: the
fuel-irrelevance family (`fuelIrrelevant_all`, with its six reader clauses), which is the fact the
loop relations need — the specification's reader answers the same at every fuel above the octet bound,
so its item loop can be put on the reference's footing one fuel lower. The loop relations have landed
in turn: the item loop at one fuel on both sides (`ItemsAgree`, `readItems_loop`), the compound body on
the list rows and on the map rows (`readCompound_list_body`, `readCompound_map_body`), and the
**element loop's one-fuel offset** (`ElementsLoopAgrees`, `elementsLoop_agrees` — the reference's
`readElements (g + 1)` against the specification's `readElementsLoop g`, by induction on the element
count) with the array body it feeds (`readArray_body`, `readArrayData` against `readArray` and both
of its smallest fuels closed by the octet bound). The tool that made the offset provable is the
readers' *position* invariance (`readRows_le_size` with `readScalarData_le` and
`specElementData_le`): a zero-width element row reads nothing through `takeBytes 0`, which succeeds
exactly when the cursor is inside the buffer, and an array of zero-width values is read at exactly
that cursor. The **element decision** (`ElementDataAgrees`) has landed in turn: all **forty
constructor rows** are proved — one theorem per octet, `element_0x00` through `element_0xF0`, over the
three stems `elementData_ok` / `elementData_step` / `elementData_var` — and the dispatcher
`elementsDecideAt_of_upTo` turns them into the named hypothesis `ElementsDecideAt` that
`elementsLoop_agrees` and `readArray_body` take. The two array arms (`0xE0`, `0xF0`) have followed —
they are the array body at the fuel the octet hands down — and so has the **value law's dispatch**:
`wireAgrees_succ` takes the octet on both sides and applies the octet's own arm, over the forty octets
the reference's reader assigns (`wireCtors`), with the unassigned family for the rest. The **fuel
induction** is `wireInvariant`, `WireAgreesUpTo n ∧ ElementsDecideBelow n` by `Nat.rec`, from which
`wireAgrees_all`, `elementsDecideBelow_all` and `elementsDecideAt_all` are read off; the **entry
point** is `valueLayersAgree` at `fuel = region.size` with both initial cursors, where the bound is
`region.size - 0 ≤ region.size` and the consumed cursor is the two readers' own entry point. The
claim is therefore reached and `ValueLayersAgree` is discharged.
What each owes and how it is
proved is stated where it belongs rather than in a list here: see the octet step's arithmetic, and
`arm_0x00`'s docstring for the pattern the branches follow.

## The element decision is not independent of the value law, and neither is the induction

The plan's ordering — the element decision first, then the arms, then the induction — is not the
dependency order, and a successor should not start from it. Four of the forty element rows are
*container* rows, and an element that is a compound, an array or a described value is read by the
same body a value-level row is: `element_0xC0` and its three neighbours call
`readCompound_list_body` / `readCompound_map_body`, which take `WireAgreesUpTo (g - 2)`, and
`element_0x00` calls `WireAgrees g` twice. So `ElementsDecideAt g` rests on the value law at the
fuels *beneath* `g` — and `element_0xE0` / `element_0xF0` rest on `ElementsDecideBelow g`, which is
the same decision family one fuel down. The two families therefore have to be proved together, as the
joint invariant `WireAgreesUpTo n ∧ ElementsDecideBelow n` that `wireInvariant` inducts over: the
element decision at every fuel below `n` supplies the array rows, the value law at every fuel up to
`n` supplies the compound and described rows, and the value law at `n + 1` is then read off the same
two. `elementsDecideAt_of_upTo` is the dispatch with exactly those two hypotheses, and both are
supplied at the one place the induction uses it — so it is not a conditional left standing, it is a
step of the induction that produces the value law itself.

## What the compound and array rows owe, and the fuel asymmetry that shapes them

The tools the loop relations need are landed — `pairUp_agrees` (the two artefacts' map pairings),
`specElementData` with `specElementData_loop` and `specElementData_progress` (the specification's
element read, named as a reader so the element count can be inducted on), the reference's own cursor
advances, the element-constructor bridge (`elementDecl?_isSome`, `elementDecl?_of_assigned`,
`elementDecl?_refusal`), and the refusal families for an octet the declared surface does not assign
(`encodingOf_none_of_not_assigned`, `ref_readValue_unassigned`, `spec_readValue_unassigned`,
`dataDecl_of_unassigned`). The loop relations followed, by the route below rather than at one fuel,
because of a finding that shapes them rather than a missing lemma — the plan owner's response to it is
the irrelevance family landed at the end of this module:

**The two artefacts spend fuel differently on a compound's header.** The reference's `readCompound`
matches on `fuel + 1`, so it spends one unit on its own header and reads its items at `readItems
(F - 1)`; the specification's `readValue` is where that unit was spent, and its `readCompound` passes
its own fuel through, reading its items at `readItems F`. At one value-level fuel the two item loops
therefore sit **one apart**, and the offset *compounds*: an item that is itself a compound puts its
own items one further apart again, so the difference is `1` per nesting level and grows without bound
as the input nests. `split`-free measurement of the two: `readItems 3 1` and `readItems 2 1` are the
item loops of the two artefacts on the same value-level fuel, and at fuel zero they are not even the
same function — `Ref.readItems 0 0 c` refuses where `Spec.readItems 1 0 c` accepts — so no statement
of the form "ref `readItems j` ↔ spec `readItems j`" can be proved from the readers as they are.

Two designs close the gap, and a successor should pick one deliberately. **The plan owner chose the
first** (`4c3c4a0`), and the account below is what designing it showed:

* **The specification's fuel is irrelevant above the bound.** A fuel unit is spent only where a reader
  *descends*, and a descent consumes octets (a described value behind one constructor octet, a
  compound's items behind two size fields, an array's elements behind a size field, a count field and
  a constructor). So at a cursor whose remaining octets the fuel covers, one unit more of fuel changes
  no answer — and the item loops can then be put on one footing by converting the specification's fuel
  down. This is the cheaper design and it needs *no* per-octet work: the specification's dispatch is
  on `classify code.toNat` and on the generated table, so its cases are six, and the four width cases
  are uniform in the row (`specElementData` is exactly the reader's own decision, so a whole width
  case is one application of the element clause). **Implemented** at the end of this module
  (`fuelIrrelevant_all` and its six corollaries), with the guards that designing it established. What
  designing it established, and what a successor should not have to rediscover:
  - It must be stated as an *agreement* and not an equality (a refusal's prose names the cursor it was
    refused at), and each clause must carry the *buffer invariance* of its read as well as its answer
    — `c₂.data = c.data`. The arms supply that per row from the primitive lemmas; the loops need it for
    the bound arithmetic, because the tail of an item loop is read at a cursor the item read advanced,
    so the bound at the tail is only expressible through the buffer the read handed back.
  - It is a joint induction over the six readers, and the level's clauses must be proved in dependency
    order: the value reader descends into the compound, the array and the element decision at one fuel
    less, so those three come from the induction hypothesis; the compound's items are read at the
    *same* fuel the compound was, and the element decision's data likewise, so the item clause and the
    element clause are read at the same level as the clauses that call them; the element loop is its
    decision and then itself, the latter by a count induction.
  - Two clauses are false as stated at the boundary and need a guard. The item loop's is false from
    fuel zero to one at a *zero count* (`Ref.readItems 0 0` refuses where `Spec.readItems 1 0`
    accepts), which no octet bound excludes; it is stated from fuel one, and the middle layer never
    needs it lower because a compound's items are only reached behind a readable header. The compound
    reader's is false at fuel zero for a declaration of width **zero** (the header consumes nothing, so
    the two fuels' item loops are reached and they differ at a zero count); the declared surface's
    compound rows are one and four octets wide, so no reader reaches one, but the *statement* has to
    carry that width — or the family has to be stated per category — and any successor that omits it
    will find the clause unprovable rather than false-by-assumption.
  - Two `split` behaviours decide how the value clause's width case is written, measured rather than
    guessed. `split at h` on a match whose scrutinee is a variable *substitutes* that variable
    everywhere, the goal included (and leaves the catch-all's negations), so the compound reader's
    owner match — a `String`-literal match — costs one `split at h` and nothing else. But `split`
    *cannot* reach a match under a bind's continuation: the width case's `match decl.category` sits
    inside `dataDecl code >>= fun decl => …`, and the fix is to destruct the read's own equation first
    (`dataDecl code = .ok decl`, then `split at h` for the category), then rewrite the goal's copy of
    the bind with the same two facts. Following that order, the width case needs no width hypothesis of
    its own; the compound clause's boundary guard is supplied at the branch rather than threaded
    through the value clause.
  - At the entry fuel the claim is not in doubt: an entry-point differential over **101,585** buffers
    (70,644 up to length 3 over a 41-octet alphabet spanning every category, 30,941 up to length 4
    over a 13-octet alphabet chosen for compounds, arrays and described values) reports **zero**
    divergences in shape, consumed count, body view and reason class — so the offset is an accounting
    difference between the readers, not a behavioural one.
* **The value relation is stated at a fuel pair.** State the middle layer with the reference's fuel
  and the specification's as parameters and carry the offset symbolically. This needs no new fact, but
  it needs the *scalar* rows re-proved at shifted fuel pairs, since the landed arms relate the two
  readers at one fuel: forty branches of the same size as the arms, or the arms restated with a second
  fuel parameter. The plan owner rejected it for that reason: it invalidates landed work by
  construction and buys nothing the first design does not.

## Why a fuel-indexed formulation, and what it carries

The two readers are the same shape: each is `readValue fuel cursor`, the entry points feed it the
*buffer's size* as the fuel ("every descent spends at least one octet of it"), and both start at
`⟨bytes, 0⟩`. So the contract's claim is this one at `fuel = bytes.size`, at the initial cursors - no
arbitrary fuwel to reconcile, unlike the corpus-vocabulary side.

What the formulation carries that the corpus side did not is the **cursor**: the two `Cursor`
structures are separate declarations with the same fields, so the relation is `CursorAgrees` (same
buffer, same position) and the induction hypothesis must preserve it through the descent, not merely
carry the value. That is where "the same octets consumed" comes from.

## The described branch, and the statement it needs first

`wireDescribed` (`0x00`) is the first branch that consumes the induction hypothesis, and reading it
shows the statement must be *strengthened* before it can be proved: a `.described` body's view is
`some (typeOfDescriptor descriptor)`, so agreeing on views is not enough — the two *descriptors* must
correspond, which is exactly `BodiesAgree` (`FrameSendConformance.lean`), the relation the corpus
side already uses between the two value types. The success conjunct should therefore carry
`BodiesAgree body other`, and the contract's view equality is then *derived* from it:

* `typeOfDescriptor` inspects only `.ulong` and `.symbol` descriptors, and both readers run `find?`
  over the **same generated table** — `Spec/Frame.lean:76` and `Ref/Frame.lean:39` both
  `open SpecAMQP.Generated.Oasis (TypeDecl types)`. There is no second table to compare, only the
  representation difference inside the predicate (`code` against `code.toNat`), which is the same
  `BodiesAgree` obligation at the descriptor.
* So `BodiesAgree body other → specBodyView body = refBodyView other` is a case analysis on the
  body, with the `.described` case asking the descriptor lemma above.

A later reader may wonder why the statement below says the view rather than `BodiesAgree`: it is the
contract's spelling, kept so the claim is the contract's own, and the strengthening is the route to
proving it.

`bodyView_of_BodiesAgree`'s state, so a successor starts where this stopped rather than re-deriving
it: `typeOfDescriptor_agrees` **closes 623 of its 625 goals** with a case-driven closer —

```lean
cases d <;> cases d' <;>
  simp only [BodiesAgree, SpecAMQP.Spec.Frame.typeOfDescriptor,
    SpecAMQP.Ref.Frame.typeOfDescriptor] at h ⊢ <;>
  try rfl <;> simp_all
```

— and the two that remain are `.ulong/.ulong` and `.symbol/.symbol`, where `h` is the payload
equality and the goal is
`types.find? (fun entry => … == n) = types.find? (fun entry => … == n.toNat)`: equal once the
equality is rewritten *under the predicate's binder*, which is why a top-level `rw [h]` does not
reach it — enter the binder first (`congr 1`, then `funext entry`, then `rw [h]`).

Two shapes to avoid, both measured. A `match d, d' with` prologue before the `cases` abstracts the
two values, so the wildcard's `cases` acts on names the goal no longer mentions and fails with the
values still symbolic — the case-driven form above is the one that works even though the prologue
reads better. And one `simp` call over the 25×25 product exceeds the heartbeat budget while 625 goals
with the targeted `simp only` chain above close in about ten seconds: the budget is per-invocation,
so a fixed term per goal is cheap at any count and a search is expensive at one.

## What the view weakens to

`specBodyView`/`refBodyView` look at a body only to ask *which described type it announces*
(`some (typeOfDescriptor descriptor)` for a `.described`, `none` otherwise). So the success conjunct
is far weaker than body equality: the same consumed octets, and the same descriptor type where the
body is described. Proving agreement *through* those views rather than through the values is what
makes the claim tractable, and it is what the contract asks for.

## The branches, and the bridge that turns out to be them

The specification dispatches on `classify code.toNat` and then on generated tables (`dataDecl`,
`elementDecl?`, the declared category), while the reference matches the constructor octet as a
*literal* — inline in its own `readValue`, with no table object to compare against. So there is no
separate bridge to build ahead of the branches: the two dispatches meet at the branch, and the
per-octet correspondence *is* the branch lemma. What the tables do offer is cheap resolution of
their own side, which is what a branch needs first:

```lean
example : (SpecAMQP.Spec.Codec.dataDecl 0x40).map (fun d => (d.width, d.owner)) =
    .ok (0, "null") := by decide
example : (SpecAMQP.Spec.Codec.dataDecl 0x01).isOk = false := by decide
example : (SpecAMQP.Spec.Value.classify 0x40 : SpecAMQP.Spec.Value.Constructor) = .fixed 0 := by
  decide
```

Ordinary `decide`, not `native_decide`: the lookups are computable and finite, so the trust base is
unchanged. Each branch then owes three things — the constructor octet, the declared form, and the
recursion at the fuel beneath — with `CursorAgrees` carried through the descent, and the branches
group by form: described (`0x00`), the four scalar categories (fixed widths 0/1/2/4/8/16, variable
1/4), compound (`list`, `map`), and array. `wireDescribed` and the compound ones are the only
branches that consume the induction hypothesis; the scalars and the refusals close against the
literal alone.
-/

open Lean (Json)

namespace SpecAMQP.Proofs

/-- The two wire cursors agree when they are the same buffer at the same position. -/
def CursorAgrees (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  c.data = c'.data ∧ c.pos = c'.pos

/-- **The two conjuncts of the claim at one fuel**, as a proposition in its own right, so that a
branch lemma can state what it owes without repeating them and the fuel induction can pass a whole
branch's obligation around as one term.

The success conjunct carries `BodiesAgree`, which is *stronger* than the contract's view equality and
is what the route needs: a described body's view is `some (typeOfDescriptor descriptor)`, so the two
descriptors must correspond, and `BodiesAgree` is exactly the relation that says so - the same one
the corpus side uses between the two value types. `bodyView_of_BodiesAgree` below recovers the
contract's spelling, so the claim is still the contract's own.

It also carries `c₂.data = c.data`: a read hands its own buffer back, so the *octets the fuel has to
cover* do not change as the induction descends. That component is what lets one read's bound become
the next read's bound — a described value reads its descriptor and then its value at *one* fuel, and
the second read's cursor is a position further on in the same buffer, so `d.pos ≤ d₂.pos`
(`ReadProgress`'s `readValue_progress`) with the buffer fixed is exactly the inequality the bound
needs. Without it the induction cannot relate one read's budget to the next's. -/
def StepAgrees (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (other : SpecAMQP.Ref.Value) (c₂' : SpecAMQP.Ref.Cursor),
      SpecAMQP.Ref.readValue fuel c' = .ok (other, c₂') →
      ∃ (body : SpecAMQP.Spec.Codec.Value) (c₂ : SpecAMQP.Spec.Codec.Cursor),
        SpecAMQP.Spec.Codec.readValue fuel c = .ok (body, c₂) ∧
        CursorAgrees c₂ c₂' ∧ c₂.data = c.data ∧ BodiesAgree body other) ∧
  (∀ (failure : SpecAMQP.Ref.DecodeError),
      SpecAMQP.Ref.readValue fuel c' = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
        SpecAMQP.Spec.Codec.readValue fuel c = .error refusal ∧
        (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- **The wire readers' agreement at a given fuel**, in the contract's direction, for cursors that
still hold the octets the fuel has to cover.

The bound `c.data.size - c.pos ≤ fuel` is not a convenience: **without it the statement is false**,
and the array's element loop is what refutes it. The two readers spend fuel differently on their way
into an array's elements — the specification's `readArrayData f` consumes one fuel entering its
element loop (`readElements (f - 1)` and then `readElementsLoop (f - 2)`) while the reference's
`readElements f` reads its first element at `f` — so for a fuel smaller than the octets left at the
cursor the two disagree: on `#[0xE0, 0x02, 0x00, 0x40]` at `⟨bytes, 0⟩` the reference answers `ok`
at fuel 2 where the specification answers `truncated`. What makes them agree is exactly the relation
the bound states, and at the entry point it holds for free: both entry points read at
`readValue bytes.size ⟨bytes, 0⟩`, and `bytes.size - 0 ≤ bytes.size`.

A fuel is only ever a bound on a reader's *recursion*, so the bound is what a reader needs: every
descent spends at least one octet, and a reader spends fuel only by descending, which is what the
branch lemmas show one branch at a time.

What is **not** true, and what this docstring said until the compound rows were attempted, is that the
two readers spend the same fuel for the same descent. The reference's `readCompound` matches on
`fuel + 1` and so spends one unit on its own header, while the specification's `readValue` already
spent that unit and its `readCompound` passes its own fuel through: the reference's `readCompound F`
reads `readItems (F - 1)` where the specification's reads `readItems F`. The two *item loops* therefore
sit one fuel apart at one value-level fuel, and the difference is visible in the loops themselves —
`Ref.readItems 0 0 c` refuses where `Spec.readItems 1 0 c` accepts, so no statement of the form
"ref `readItems j` ↔ spec `readItems j`" is provable from the readers as they are. The offset is an
accounting difference and not a behavioural one — both readers answer identically at the fuel the
contract uses, which is what the entry-point differential measures — and what closes it is the fact
that the specification's fuel is irrelevant above the bound; the module header's section on the
compound and array rows states that fact and the design it wants.

A law
quantified over every fuel a cursor can be paired with is a *different* law from the one the contract
asks for, and not a stronger one. -/
def WireAgrees (fuel : Nat) : Prop :=
  ∀ (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor), CursorAgrees c c' →
    c.data.size - c.pos ≤ fuel → StepAgrees fuel c c'

/-- **The base case.** At fuel 0 both readers refuse, with the same class: there is nothing to read
before the input ends. -/
theorem wireAgrees_zero : WireAgrees 0 := by
  intro c c' _ _hb
  refine ⟨?_, ?_⟩
  · intro other c₂' h
    simp only [SpecAMQP.Ref.readValue] at h
    exact absurd h (by simp)
  · intro failure h
    simp only [SpecAMQP.Ref.readValue] at h
    refine ⟨SpecAMQP.Spec.Codec.refusal "truncated" "the input ends before the value does", ?_, ?_⟩
    · simp only [SpecAMQP.Spec.Codec.readValue]
    · injection h with hf
      subst hf
      rfl

/-- **One octet, taken by two cursors that agree.** The same octet comes off the same buffer and the
cursors advance together — a cursor with nothing left fails on both sides with the same class — so every
branch of the induction begins here.

The cursors are destructured before the equalities are used, because `c.data[c.pos]` is a dependent
lookup: rewriting `c.data` under it is not type-correct, while `cases` on the equalities of the
destructured fields substitutes and leaves the lookup well-typed. -/
theorem takeU8_agrees {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (b : UInt8) (d' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeU8 c' = .ok (b, d')) :
    ∃ d : SpecAMQP.Spec.Codec.Cursor,
      SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d) ∧ CursorAgrees d d' := by
  cases c with | mk data pos =>
  cases c' with | mk data' pos' =>
  obtain ⟨hd, hp⟩ := hc
  cases hd
  cases hp
  by_cases hlt : pos < data.size
  · have hlt' : pos < data.size := hlt
    rw [SpecAMQP.Spec.Codec.takeU8, dif_pos hlt]
    rw [SpecAMQP.Ref.takeU8, dif_pos hlt'] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hc'⟩ := h
    subst hb
    refine ⟨⟨data, pos + 1⟩, rfl, ?_⟩
    rw [← hc']
    exact ⟨rfl, rfl⟩
  · have hlt' : ¬ (pos < data.size) := hlt
    rw [SpecAMQP.Ref.takeU8, dif_neg hlt'] at h
    exact absurd h (by simp)

/-- The failure half of the same step: a cursor that has run out refuses on both sides, with the same
class. -/
theorem takeU8_fails {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (failure : SpecAMQP.Ref.DecodeError)
    (h : SpecAMQP.Ref.takeU8 c' = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeU8 c = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  cases c with | mk data pos =>
  cases c' with | mk data' pos' =>
  obtain ⟨hd, hp⟩ := hc
  cases hd
  cases hp
  by_cases hlt : pos < data.size
  · have hlt' : pos < data.size := hlt
    rw [SpecAMQP.Ref.takeU8, dif_pos hlt'] at h
    exact absurd h (by simp)
  · have hlt' : ¬ (pos < data.size) := hlt
    rw [SpecAMQP.Ref.takeU8, dif_neg hlt'] at h
    rw [SpecAMQP.Spec.Codec.takeU8, dif_neg hlt]
    simp only [Except.error.injEq] at h
    subst h
    exact ⟨SpecAMQP.Spec.Codec.refusal "truncated"
      s!"no octet at offset {pos} of {data.size}", rfl, rfl⟩

/-- The description a body announces agrees when the bodies agree: `typeOfDescriptor` inspects only
`ulong` and `symbol` descriptors, and both readers run `find?` over the *same* generated table, so the
only obligation is the representational one `BodiesAgree` already carries. Stated case-driven rather
than with a `match` prologue: the prologue abstracts the two values, and `cases` then acts on names the
goal no longer mentions.

The two payload cases are the whole content: the tables are the same object, so the goals differ only
in the predicate's payload — `n` against `n.toNat`, a string against the same string — and rewriting
the `BodiesAgree` payload equality *under* the `find?` predicate's binder identifies them. -/
theorem typeOfDescriptor_agrees {d : SpecAMQP.Spec.Codec.Value} {d' : SpecAMQP.Ref.Value}
    (h : BodiesAgree d d') :
    SpecAMQP.Spec.Frame.typeOfDescriptor d = SpecAMQP.Ref.Frame.typeOfDescriptor d' := by
  cases d <;> cases d' <;>
    simp only [BodiesAgree, SpecAMQP.Spec.Frame.typeOfDescriptor,
      SpecAMQP.Ref.Frame.typeOfDescriptor] at h ⊢
  all_goals
    first
      | rfl
      | (congr 1
         funext entry
         rw [h]
         rfl)

/-- **The contract's view equality, from the strengthened conjunct.** A described body's view is its
descriptor's type; everything else views as `none`. -/
theorem bodyView_of_BodiesAgree {body : SpecAMQP.Spec.Codec.Value} {other : SpecAMQP.Ref.Value}
    (h : BodiesAgree body other) : specBodyView body = refBodyView other := by
  cases body <;> cases other <;>
    simp only [BodiesAgree, specBodyView, refBodyView] at h ⊢
  all_goals
    first
      | rfl
      | (rw [typeOfDescriptor_agrees h.1])

/-! ## The octet step's arithmetic, shared by every branch

A branch's proof begins by taking the octet and then reading a payload, and the two artefacts' payload
readers are different functions that compute the same thing: the reference takes its octets one at a
time (`takeU8`, `takeBeU`, `takeBytes`) while the specification accumulates a big-endian foldl over
the octets a declared width gives. What a branch needs first is the bridge between those, and what a
branch's fuel bound needs from a step is where the step left the cursor, which is why the `_data`
lemmas below sit beside the advances the round-trip rungs already state.

Three environment facts are worth recording here, because each costs an iteration otherwise. `simp`
cannot reduce an `Except` bind at all unless it is given the two lemmas that reduce it, so those two
(`Proofs/ExceptMap`'s `except_bind_ok` and `except_bind_error`) are named at every step that has to
see inside a `do` block, and `exists_of_bind_ok` recovers a bind's left side where a proof starts
from the whole read having accepted. The specification's `takeU8` is a *dependent* `if` while its
`takeBytes`/`takeBe` are not, so the three reduce through `dif_pos` and `if_pos` respectively. And a
`BodiesAgree` obligation between width-carrying carriers is an identity exactly on the width's range,
which is what `Proofs/CodecRoundTripNarrowest`'s `takeBe_lt` supplies. -/

/-- **A one-octet payload folds to the octet it holds.** The width-one rows read one octet and
accumulate it, so the foldl is that octet as a number — the fact that puts the specification's
one-octet fixed read and the reference's `takeU8` on one value. -/
theorem foldl_extract_one (a : Array UInt8) (i : Nat) (h : i < a.size) :
    (a.extract i (i + 1)).foldl (fun acc b => acc * 256 + b.toNat) 0 = a[i].toNat := by
  rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_take_drop]
  have hsub : i + 1 - i = 1 := by omega
  rw [hsub, List.drop_eq_getElem_cons (l := a.toList) (by simpa using h),
    List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  simp

/-- A step hands back the buffer it was given: the two cursors share the input rather than copying
it, so a read moves the position and leaves the data alone. Together with the advances the round-trip
rungs state (`takeBytes_advances`, `takeBe_advances`, and `takeU8`'s own record) this is what a
branch's fuel bound descends through. -/
theorem spec_takeU8_data {c d : SpecAMQP.Spec.Codec.Cursor} {b : UInt8}
    (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d)) : d.data = c.data := by
  have hpos : c.pos < c.data.size := by
    by_contra hlt
    unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_neg hlt] at h
    exact absurd h (by simp)
  unfold SpecAMQP.Spec.Codec.takeU8 at h
  rw [dif_pos hpos] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hd⟩ := h
  subst hd
  rfl

/-- The same for a payload read. -/
theorem spec_takeBytes_data {n : Nat} {c d : SpecAMQP.Spec.Codec.Cursor} {bytes : Array UInt8}
    (h : SpecAMQP.Spec.Codec.takeBytes n c = .ok (bytes, d)) : d.data = c.data := by
  unfold SpecAMQP.Spec.Codec.takeBytes at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hd⟩ := h
    subst hd
    rfl
  · exact absurd h (by simp)

/-- The same for a big-endian field: the foldl adds a value, not a buffer. -/
theorem spec_takeBe_data {w : Nat} {c d : SpecAMQP.Spec.Codec.Cursor} {m : Nat}
    (h : SpecAMQP.Spec.Codec.takeBe w c = .ok (m, d)) : d.data = c.data := by
  unfold SpecAMQP.Spec.Codec.takeBe at h
  obtain ⟨⟨bytes, d'⟩, hb, h⟩ := exists_of_bind_ok h
  dsimp only at h
  have hpair : (bytes.foldl (fun acc b => acc * 256 + b.toNat) 0, d') = (m, d) := Except.ok.inj h
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨-, hd⟩ := hpair
  subst hd
  exact spec_takeBytes_data hb

/-! ## Taking the payload through two cursors that agree -/

/-- `n` octets, taken by two cursors that agree: the same payload comes off the same buffer and the
cursors advance together. This is `takeU8_agrees` one width up, and every payload read a branch
performs goes through it. -/
theorem takeBytes_agrees {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (n : Nat) (bytes : Array UInt8) (d' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeBytes n c' = .ok (bytes, d')) :
    ∃ d : SpecAMQP.Spec.Codec.Cursor,
      SpecAMQP.Spec.Codec.takeBytes n c = .ok (bytes, d) ∧ CursorAgrees d d' := by
  cases c with | mk data pos =>
  cases c' with | mk data' pos' =>
  obtain ⟨hd, hp⟩ := hc
  cases hd
  cases hp
  by_cases hle : pos + n ≤ data.size
  · have hle' : pos + n ≤ data.size := hle
    rw [SpecAMQP.Spec.Codec.takeBytes, if_pos hle]
    rw [SpecAMQP.Ref.takeBytes, if_pos hle'] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hd'⟩ := h
    subst hb
    exact ⟨⟨data, pos + n⟩, rfl, by rw [← hd']; exact ⟨rfl, rfl⟩⟩
  · have hle' : ¬ (pos + n ≤ data.size) := hle
    rw [SpecAMQP.Ref.takeBytes, if_neg hle'] at h
    exact absurd h (by simp)

/-- The failure half of the same step: the same buffer runs out on both sides, with the same class. -/
theorem takeBytes_fails {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (n : Nat) (failure : SpecAMQP.Ref.DecodeError)
    (h : SpecAMQP.Ref.takeBytes n c' = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeBytes n c = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  cases c with | mk data pos =>
  cases c' with | mk data' pos' =>
  obtain ⟨hd, hp⟩ := hc
  cases hd
  cases hp
  by_cases hle : pos + n ≤ data.size
  · have hle' : pos + n ≤ data.size := hle
    rw [SpecAMQP.Ref.takeBytes, if_pos hle'] at h
    exact absurd h (by simp)
  · have hle' : ¬ (pos + n ≤ data.size) := hle
    rw [SpecAMQP.Ref.takeBytes, if_neg hle'] at h
    rw [SpecAMQP.Spec.Codec.takeBytes, if_neg hle]
    simp only [Except.error.injEq] at h
    subst h
    exact ⟨SpecAMQP.Spec.Codec.refusal "truncated"
      s!"{n} octet(s) needed at offset {pos} of {data.size}", rfl, rfl⟩

/-- A field the payload reader failed on is a field the foldl over that payload failed on, with the
same refusal: the foldl adds nothing to a read that did not happen. -/
theorem spec_takeBe_error (c : SpecAMQP.Spec.Codec.Cursor) (w : Nat)
    (refusal : SpecAMQP.Spec.Codec.Refusal) :
    SpecAMQP.Spec.Codec.takeBe w c = .error refusal ↔
      SpecAMQP.Spec.Codec.takeBytes w c = .error refusal := by
  constructor
  · intro h
    unfold SpecAMQP.Spec.Codec.takeBe at h
    cases hb : SpecAMQP.Spec.Codec.takeBytes w c with
    | error e =>
      rw [hb] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      rw [h]
    | ok p => rw [hb] at h; rw [except_bind_ok] at h; exact absurd h (by simp)
  · intro h
    unfold SpecAMQP.Spec.Codec.takeBe
    rw [h, except_bind_error]

/-- A big-endian field of `w` octets, read by two cursors that agree. Both readers are the same foldl
over the same payload, so a branch that has taken the payload through `takeBytes_agrees` gets the
field's value on both sides at once. -/
theorem takeBe_agrees {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (w : Nat) (m : Nat) (d' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeBeU w c' = .ok (m, d')) :
    ∃ d : SpecAMQP.Spec.Codec.Cursor,
      SpecAMQP.Spec.Codec.takeBe w c = .ok (m, d) ∧ CursorAgrees d d' := by
  unfold SpecAMQP.Ref.takeBeU at h
  obtain ⟨⟨bytes, d₁'⟩, hb, h⟩ := exists_of_bind_ok h
  dsimp only at h
  have hpair : (bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0, d₁') = (m, d') :=
    Except.ok.inj h
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hm, hd₁⟩ := hpair
  subst hm
  subst hd₁
  obtain ⟨d₁, hsb, hd₁⟩ := takeBytes_agrees hc w bytes d₁' hb
  refine ⟨d₁, ?_, hd₁⟩
  unfold SpecAMQP.Spec.Codec.takeBe
  rw [hsb, except_bind_ok]
  dsimp only
  rfl

/-- The failure half of the big-endian field. -/
theorem takeBe_fails {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (w : Nat) (failure : SpecAMQP.Ref.DecodeError)
    (h : SpecAMQP.Ref.takeBeU w c' = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeBe w c = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  unfold SpecAMQP.Ref.takeBeU at h
  cases hb : SpecAMQP.Ref.takeBytes w c' with
  | error e =>
    rw [hb] at h
    rw [except_bind_error] at h
    simp only [Except.error.injEq] at h
    subst h
    obtain ⟨refusal, hspec, hcl⟩ := takeBytes_fails hc w e hb
    exact ⟨refusal, (spec_takeBe_error c w refusal).mpr hspec, hcl⟩
  | ok p =>
    rw [hb] at h
    rw [except_bind_ok] at h
    exact absurd h (by simp)

/-! ## The width-one bridge -/

/-- **The specification's one-octet payload read, in the octet step's own vocabulary.** A width-one
row reads one octet and accumulates it, so a branch that has the octet has the payload and the foldl
too. The payload is the `extract` that `takeBytes` returns rather than the octet itself, which is why
the bridge carries the foldl equation and not an array equality: what a value needs is the *number*,
and which array held it is the reader's own business. -/
theorem spec_takeBytes_one_of_takeU8 (d : SpecAMQP.Spec.Codec.Cursor) (b : UInt8)
    (d₂ : SpecAMQP.Spec.Codec.Cursor)
    (h : SpecAMQP.Spec.Codec.takeU8 d = .ok (b, d₂)) :
    SpecAMQP.Spec.Codec.takeBytes 1 d = .ok (d.data.extract d.pos (d.pos + 1), d₂) ∧
      (d.data.extract d.pos (d.pos + 1)).foldl (fun acc x => acc * 256 + x.toNat) 0 = b.toNat := by
  have hpos : d.pos < d.data.size := by
    by_contra hlt
    unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_neg hlt] at h
    exact absurd h (by simp)
  have hb : b = d.data[d.pos]'hpos := by
    unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_pos hpos] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  have hd₂ : d₂ = ⟨d.data, d.pos + 1⟩ := by
    unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_pos hpos] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  subst hb
  subst hd₂
  constructor
  · unfold SpecAMQP.Spec.Codec.takeBytes
    rw [if_pos (by omega : d.pos + 1 ≤ d.data.size)]
  · exact foldl_extract_one d.data d.pos hpos

/-- The width-one bridge in the form a branch wants: the field's value. -/
theorem spec_takeBe_one_of_takeU8 (d : SpecAMQP.Spec.Codec.Cursor) (b : UInt8)
    (d₂ : SpecAMQP.Spec.Codec.Cursor)
    (h : SpecAMQP.Spec.Codec.takeU8 d = .ok (b, d₂)) :
    SpecAMQP.Spec.Codec.takeBe 1 d = .ok (b.toNat, d₂) := by
  obtain ⟨hbytes, hfold⟩ := spec_takeBytes_one_of_takeU8 d b d₂ h
  unfold SpecAMQP.Spec.Codec.takeBe
  rw [hbytes, except_bind_ok]
  dsimp only
  rw [hfold]
  rfl

/-- A successful octet step's cursor is inside its buffer: the step took an octet from it. A
zero-width row reads *nothing* through `takeBytes 0`, and that read still needs the position to be
inside the buffer, so this is what a zero-width branch carries. -/
theorem spec_takeU8_lt {c : SpecAMQP.Spec.Codec.Cursor} {b : UInt8}
    {d : SpecAMQP.Spec.Codec.Cursor} (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d)) :
    c.pos < c.data.size := by
  by_contra hlt
  unfold SpecAMQP.Spec.Codec.takeU8 at h
  rw [dif_neg hlt] at h
  exact absurd h (by simp)

/-- An octet step leaves its cursor inside the buffer, which is what the zero-width rows' read of
nothing needs. -/
theorem spec_takeU8_next_le {c : SpecAMQP.Spec.Codec.Cursor} {b : UInt8}
    {d : SpecAMQP.Spec.Codec.Cursor} (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d)) :
    d.pos ≤ d.data.size := by
  have hlt : c.pos < c.data.size := spec_takeU8_lt h
  unfold SpecAMQP.Spec.Codec.takeU8 at h
  rw [dif_pos hlt] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hd⟩ := h
  subst hd
  dsimp only
  omega

/-- A payload read leaves its cursor inside the buffer: it asked for `n` octets at a position whose
remaining octets covered them, and its cursor is that position plus `n`. The companion of
`spec_takeU8_next_le` for the reads the rows perform. -/
theorem spec_takeBytes_le {n : Nat} {c d : SpecAMQP.Spec.Codec.Cursor} {bytes : Array UInt8}
    (h : SpecAMQP.Spec.Codec.takeBytes n c = .ok (bytes, d)) : d.pos ≤ d.data.size := by
  unfold SpecAMQP.Spec.Codec.takeBytes at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    dsimp only
    omega
  · exact absurd h (by simp)

/-- The same for a big-endian field, which reads through the payload read. -/
theorem spec_takeBe_le {w : Nat} {c d : SpecAMQP.Spec.Codec.Cursor} {v : Nat}
    (h : SpecAMQP.Spec.Codec.takeBe w c = .ok (v, d)) : d.pos ≤ d.data.size := by
  unfold SpecAMQP.Spec.Codec.takeBe at h
  obtain ⟨⟨bytes, d₁⟩, hb, h⟩ := exists_of_bind_ok h
  dsimp only at h
  rw [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact spec_takeBytes_le hb
theorem spec_takeBytes_zero (c : SpecAMQP.Spec.Codec.Cursor) (h : c.pos ≤ c.data.size) :
    SpecAMQP.Spec.Codec.takeBytes 0 c = .ok (#[], ⟨c.data, c.pos + 0⟩) := by
  have hempty : c.data.extract c.pos (c.pos + 0) = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    rw [Array.size_extract]
    omega
  unfold SpecAMQP.Spec.Codec.takeBytes
  rw [if_pos (by omega), hempty]

/-- A one-octet payload read fails exactly where the octet step fails, with the same class: the two
read the same octet, and each refuses it in its own words. -/
theorem spec_takeBytes_one_class {c : SpecAMQP.Spec.Codec.Cursor}
    (refusal : SpecAMQP.Spec.Codec.Refusal)
    (h : SpecAMQP.Spec.Codec.takeU8 c = .error refusal) :
    ∃ refusal' : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeBytes 1 c = .error refusal' ∧
      refusal'.reasonClass = refusal.reasonClass := by
  by_cases hlt : c.pos < c.data.size
  · unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_pos hlt] at h
    exact absurd h (by simp)
  · unfold SpecAMQP.Spec.Codec.takeU8 at h
    rw [dif_neg hlt] at h
    simp only [Except.error.injEq] at h
    subst h
    unfold SpecAMQP.Spec.Codec.takeBytes
    rw [if_neg (by omega)]
    exact ⟨_, rfl, rfl⟩

/-- The failure half of the width-one bridge: a payload read the reference fails, the specification
fails with the same class. -/
theorem spec_takeBytes_one_fails {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (failure : SpecAMQP.Ref.DecodeError)
    (h : SpecAMQP.Ref.takeU8 c' = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.takeBytes 1 c = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  obtain ⟨refusal, hspec, hcl⟩ := takeU8_fails hc failure h
  obtain ⟨refusal', hbytes, hcl'⟩ := spec_takeBytes_one_class refusal hspec
  exact ⟨refusal', hbytes, by rw [hcl, hcl']⟩

/-- **One value read's budget is the next read's.** A read leaves its cursor further on in the same
buffer, so the octets left at the cursor it hands back are no more than the octets left at the one it
was given — which is what lets a branch that reads twice at one fuel pass the bound along. The buffer
equality is the success conjunct's own, so this is stated against that component rather than against a
reader of its own. -/
theorem bound_of_read {fuel : Nat} {c d₂ : SpecAMQP.Spec.Codec.Cursor}
    {v : SpecAMQP.Spec.Codec.Value} (h : SpecAMQP.Spec.Codec.readValue fuel c = .ok (v, d₂))
    (hdata : d₂.data = c.data) (hb : c.data.size - c.pos ≤ fuel) :
    d₂.data.size - d₂.pos ≤ fuel := by
  have hpos := (readValue_progress fuel).1 c v d₂ h
  have hsize : d₂.data.size = c.data.size := by rw [hdata]
  omega

/-! ## The described branch (`0x00`), and the pattern the rest follow

A branch lemma is stated against the octet *step* rather than against the reader: what a dispatch
gives its arms is a pair of cursors that agree and one octet that both readers took, and what a
branch owes is `StepAgrees` one fuel up. The arm a reader selects is then its own, reduced by the
literal octet the statement names — which is why a branch lemma carries the octet in its hypotheses
and never in its statement, and why the branches below are written one octet at a time.

Three moves recur, and each cost an iteration to find. The specification's dispatch is on
`classify code.toNat` and its table lookups run `List.find?` over the generated surface, so a branch
resolves its own side with two `decide`-checked facts — the classification and the row — rather than
by `simp`: `decide` is ordinary evaluation over finite data, and the whole arm behind a lookup is a
`match` whose scrutinee only reduces once the row is named. The reference's dispatch is on the octet
itself and reduces by `rfl`. And every payload step is an `Except` bind, which the two lemmas in
`Proofs/ExceptMap` reduce and nothing else does. -/

/-- **The described branch (`0x00`).** The specification dispatches on the octet's *classification*
and the reference on the octet itself, and `classify 0 = descriptor` is exactly the octet `0x00`, so
the two readers run the same arm: a descriptor, then a value, then `.described`. Both reads are the
induction hypothesis one fuel down — the descriptor first, then the value at the cursor the first read
left — and the consumed octets agree because the hypothesis carries `CursorAgrees` through each of
them.

This is the branch the induction is shaped around: it is the only one that reads *two* values at one
fuel, which is why the success conjunct carries the buffer the reads share, and it is the pattern the
scalar branches follow with their reads replaced by a table lookup and the compound ones with theirs
replaced by a loop. -/
theorem arm_0x00 (fuel : Nat) (ih : WireAgrees fuel) (c : SpecAMQP.Spec.Codec.Cursor)
    (c' : SpecAMQP.Ref.Cursor) (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor)
    (hd : CursorAgrees d d') (hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x00, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x00, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0x00 : UInt8).toNat = .descriptor := by decide
  -- the arm each reader's own dispatch selects
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      (SpecAMQP.Spec.Codec.readValue fuel d) >>= (fun p =>
        (SpecAMQP.Spec.Codec.readValue fuel p.2) >>= (fun q =>
          .ok (.described p.1 q.1, q.2))) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      (SpecAMQP.Ref.readValue fuel d') >>= (fun p =>
        (SpecAMQP.Ref.readValue fuel p.2) >>= (fun q =>
          .ok (.described p.1 q.1, q.2))) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨⟨desc, d₂'⟩, h1, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨⟨val, d₃'⟩, h2, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨hother, hcur⟩ : .described desc val = other ∧ d₃' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    obtain ⟨sdesc, d₂, hs1, hc1, hdat1, hb1⟩ := (ih d d' hd hb).1 desc d₂' h1
    obtain ⟨sval, d₃, hs2, hc2, hdat2, hb2⟩ :=
      (ih d₂ d₂' hc1 (bound_of_read hs1 hdat1 hb)).1 val d₃' h2
    refine ⟨.described sdesc sval, d₃, ?_, hc2, ?_, ?_⟩
    · rw [hS, hs1, except_bind_ok, hs2, except_bind_ok]
    · rw [hdat2, hdat1, hdata]
    · unfold BodiesAgree
      exact ⟨hb1, hb2⟩
  · intro failure h
    rw [hR] at h
    cases h1 : SpecAMQP.Ref.readValue fuel d' with
    | error e =>
      rw [h1] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hspec, hcl⟩ := (ih d d' hd hb).2 e h1
      refine ⟨refusal, ?_, hcl⟩
      rw [hS, hspec, except_bind_error]
    | ok p =>
      obtain ⟨desc, d₂'⟩ := p
      rw [h1] at h
      rw [except_bind_ok] at h
      cases h2 : SpecAMQP.Ref.readValue fuel d₂' with
      | error e =>
        rw [h2] at h
        rw [except_bind_error] at h
        simp only [Except.error.injEq] at h
        subst h
        obtain ⟨sdesc, d₂, hs1, hc1, hdat1, -⟩ := (ih d d' hd hb).1 desc d₂' h1
        obtain ⟨refusal, hspec, hcl⟩ :=
          (ih d₂ d₂' hc1 (bound_of_read hs1 hdat1 hb)).2 e h2
        refine ⟨refusal, ?_, hcl⟩
        rw [hS, hs1, except_bind_ok, hspec, except_bind_error]
      | ok q =>
        rw [h2] at h
        rw [except_bind_ok] at h
        exact absurd h (by simp)

/-- **A zero-width row (`0x40`, `null`).** The table's row for this octet names `null` at no width,
so the specification reads no payload and answers the value the table names, while the reference
matches the octet and answers the same value. Nothing recurses, which is why the scalar branches
carry no bound: only the two tables have to be resolved. -/
theorem arm_0x40 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x40, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x40, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x40 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x40 : UInt8) =
      .ok ⟨64, none, SpecAMQP.Generated.Oasis.Category.fixed, 0, "null",
        "the null value"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.null, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    try dsimp only
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.null, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨hother, hcur⟩ : .null = other ∧ d' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    exact ⟨.null, d, hS, hd, spec_takeU8_data hs, by simp only [BodiesAgree]⟩
  · intro failure h
    rw [hR] at h
    exact absurd h (by simp)

/-- **A width-one row with a payload (`0x50`, `ubyte`).** The reference takes one octet and answers
it; the specification's row reads one octet through `takeBytes`, accumulates it, and answers the
number. The bridge is the whole content: the payload and the foldl are the octet the reference took,
so the two values agree on the nose, and the cursor the reference's payload read left is the one the
specification's row left. -/
theorem arm_0x50 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x50, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x50, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0x50 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x50 : UInt8) =
      .ok ⟨80, none, SpecAMQP.Generated.Oasis.Category.fixed, 1, "ubyte",
        "8-bit unsigned integer"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      (SpecAMQP.Spec.Codec.takeBytes 1 d) >>= (fun p =>
        .ok (.ubyte (p.1.foldl (fun acc x => acc * 256 + x.toNat) 0), p.2)) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      (SpecAMQP.Ref.takeU8 d') >>= (fun p => .ok (.ubyte p.1, p.2)) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨⟨b, d₂'⟩, h1, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨hother, hcur⟩ : .ubyte b = other ∧ d₂' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    obtain ⟨d₂, hsu8, hd₂⟩ := takeU8_agrees hd b d₂' h1
    obtain ⟨hbytes, hfold⟩ := spec_takeBytes_one_of_takeU8 d b d₂ hsu8
    refine ⟨.ubyte b.toNat, d₂, ?_, hd₂, ?_, ?_⟩
    · rw [hS, hbytes, except_bind_ok, hfold]
    · rw [spec_takeBytes_data hbytes, hdata]
    · simp only [BodiesAgree]
  · intro failure h
    rw [hR] at h
    cases h1 : SpecAMQP.Ref.takeU8 d' with
    | error e =>
      rw [h1] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hbytes, hcl⟩ := spec_takeBytes_one_fails hd e h1
      exact ⟨refusal, by rw [hS, hbytes, except_bind_error], hcl⟩
    | ok p =>
      rw [h1] at h
      rw [except_bind_ok] at h
      exact absurd h (by simp)
/-! ## The arm machinery: a step, a relation, and one stem per shape

Every arm still owed has the same skeleton — take the octet, read a payload, answer a value — and
differs from its neighbours only in the payload's shape and in the value. Twenty-four proofs of the
same two conjuncts would bury each arm's own content in boilerplate, so the skeleton is stated once
as a **step**: a reader whose value is an *intermediate* (an octet, a payload, a number) rather than
a body, with the relation between the two readers' intermediates made explicit. The relation is the
useful part: the two artefacts often read the same octets into different values — the
specification folds a payload into a number that the reference never forms bare — and a step
agreement is exactly the statement that lets one reader's octets be the other's number.

The instances below carry every fixed-width row. The relation each carries is the one its arm's
values need:

* `stepAgreesAll_takeBytes` — the opaque widths, where both readers hand the octets back and the
  relation is equality of arrays;
* `stepAgreesAll_takeBeNat` — the unsigned and `char` widths, where the specification folds the
  octets it read while the reference folds them inside `takeBeU`, so the relation is
  `payloadNat a = b`;
* `stepAgreesAll_takeU8Nat` — the one-octet payloads, the same relation at width one;
* `stepAgreesAll_takeBeEq`, `stepAgreesAll_takeBeOne` — the *variable* rows' length field, where both
  readers produce the same number (or the reference's octet is that number), because those rows read
  their length through `takeBe` rather than through the payload read a fixed row uses;
* `readersAgree_utf8` — the third reader of the two text families, where both readers decode the same
  octets with the same standard-library call and differ only in the refusal's prose. It is stated at
  the *reader* level rather than as a step, and that is not a matter of taste: a step agreement hands
  its intermediate back as one component of a pair, and re-pairing that component into the value the
  reader answers produces a term equal to the reader's own only through `>>=`'s associativity — not a
  definitional equality, and so not something a *hypothesis* can be checked against. The lesson is
  the same one the fuel bound taught: state the law at the shape the consumer has.

`readersAgreeAt_bind` is the composition the variable rows need — a length field, then the reader
below it — and the three stems turn a step plus a value into the `StepAgrees` an arm owes: `reader_of_ok` for the zero-width rows, `reader_of_step` for the payload rows, and
`reader_of_two_steps` for the variable ones. -/

/-- **The number the specification accumulates a payload's octets into.** Named because three of the
bridges below are stated in its terms and because it is the relation the number-carrying arms carry:
the reference's number and the specification's octets meet here. -/
def payloadNat (bytes : SpecAMQP.Harness.Octets) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- **Two readers' *steps* agree up to a relation on their values.** A step is a reader whose value is
an intermediate rather than a body; two steps agree when the reference's is a value the specification
also reaches, related to it by `R`, at a cursor the two agree on, with the same octets in hand. The
second conjunct is the refusal half, as in `StepAgrees`, and the buffer component is what an arm's
fuel bound descends through. -/
def StepAgreesAt {α β : Type} (R : α → β → Prop)
    (f : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor))
    (g : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (β × SpecAMQP.Ref.Cursor))
    (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (b : β) (d' : SpecAMQP.Ref.Cursor), g c' = .ok (b, d') →
      ∃ (a : α) (d : SpecAMQP.Spec.Codec.Cursor), f c = .ok (a, d) ∧ R a b ∧
        CursorAgrees d d' ∧ d.data = c.data) ∧
  (∀ failure : SpecAMQP.Ref.DecodeError, g c' = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal, f c = .error refusal ∧
        (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- The same obligation at every pair of agreeing cursors, which is the form a *nested* step needs:
an inner step starts from the cursors its outer step handed back, and those are known to agree only
from the outer step's own success. -/
def StepAgreesAll {α β : Type} (R : α → β → Prop)
    (f : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor))
    (g : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (β × SpecAMQP.Ref.Cursor)) : Prop :=
  ∀ (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor),
    CursorAgrees c c' → StepAgreesAt R f g c c'

/-- **A payload read took at most what it asked for.** `takeBytes` answers an `extract`, and an
extract is as long as the request or shorter; this is the first half of the bound a width-carrying
arm's value equation needs. -/
theorem spec_takeBytes_size_le {n : Nat} {c d : SpecAMQP.Spec.Codec.Cursor}
    {bytes : SpecAMQP.Harness.Octets}
    (h : SpecAMQP.Spec.Codec.takeBytes n c = .ok (bytes, d)) : bytes.size ≤ n := by
  unfold SpecAMQP.Spec.Codec.takeBytes at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, -⟩ := h
    subst hb
    rw [Array.size_extract]
    omega
  · exact absurd h (by simp)

/-- **A fold over a payload is bounded by the payload's own width.** The array form of
`CodecRoundTripNarrowest`'s `foldl_be_bound` at an empty accumulator: `w` octets accumulate to a
number below `256 ^ w`, which is the reader's own account of what a width-`w` field can carry. -/
theorem payloadNat_lt (bytes : SpecAMQP.Harness.Octets) :
    payloadNat bytes < 256 ^ bytes.size := by
  rw [payloadNat, ← Array.foldl_toList]
  simpa using foldl_be_bound bytes.toList 0

/-- The two facts a width-`w` payload's value equation needs, together: the payload is no longer than
the width asked for, and the fold over it is below `256` to its own length. -/
theorem payloadNat_lt_of_takeBytes {w : Nat} {c d : SpecAMQP.Spec.Codec.Cursor}
    {bytes : SpecAMQP.Harness.Octets}
    (h : SpecAMQP.Spec.Codec.takeBytes w c = .ok (bytes, d)) : payloadNat bytes < 256 ^ w :=
  calc payloadNat bytes < 256 ^ bytes.size := payloadNat_lt bytes
    _ ≤ 256 ^ w := Nat.pow_le_pow_right (by decide) (spec_takeBytes_size_le h)

/-- A successful payload read is a successful big-endian field read at the same cursor, answering the
number the fold gives. This is what puts a variable row's length step (which reads through `takeBe`)
and a fixed row's payload step (which reads through `takeBytes`) on one footing. -/
theorem spec_takeBe_of_takeBytes {w : Nat} {c d : SpecAMQP.Spec.Codec.Cursor}
    {bytes : SpecAMQP.Harness.Octets}
    (h : SpecAMQP.Spec.Codec.takeBytes w c = .ok (bytes, d)) :
    SpecAMQP.Spec.Codec.takeBe w c = .ok (payloadNat bytes, d) := by
  unfold SpecAMQP.Spec.Codec.takeBe
  rw [h, except_bind_ok]
  rfl

/-- **The payload step, octet for octet.** Both readers take the same `n` octets off the same buffer at
the same position; the relation is equality of the arrays, which is what the opaque rows' values wait
for. -/
theorem stepAgreesAll_takeBytes (n : Nat) :
    StepAgreesAll (fun a b : SpecAMQP.Harness.Octets => a = b)
      (SpecAMQP.Spec.Codec.takeBytes n) (SpecAMQP.Ref.takeBytes n) := by
  intro c c' hc
  constructor
  · intro b d' h
    obtain ⟨d, hspec, hcd⟩ := takeBytes_agrees hc n b d' h
    exact ⟨b, d, hspec, rfl, hcd, spec_takeBytes_data hspec⟩
  · intro failure h
    exact takeBytes_fails hc n failure h

/-- **The big-endian field step.** The reference folds the octets inside `takeBeU` and hands back a
number; the specification's fixed-width rows fold the same octets outside it, so the two steps are
related by `payloadNat a = b` rather than by an equality of arrays. -/
theorem stepAgreesAll_takeBeNat (w : Nat) :
    StepAgreesAll (fun (a : SpecAMQP.Harness.Octets) (b : Nat) => payloadNat a = b)
      (SpecAMQP.Spec.Codec.takeBytes w) (SpecAMQP.Ref.takeBeU w) := by
  intro c c' hc
  constructor
  · intro b d' h
    unfold SpecAMQP.Ref.takeBeU at h
    obtain ⟨⟨bytes, d₁'⟩, hb, h⟩ := exists_of_bind_ok h
    dsimp only at h
    rw [except_pure_ok] at h
    have hp : (payloadNat bytes, d₁') = (b, d') := Except.ok.inj h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hm, hd⟩ := hp
    subst hm
    subst hd
    obtain ⟨d, hspec, hcd⟩ := takeBytes_agrees hc w bytes d₁' hb
    exact ⟨bytes, d, hspec, rfl, hcd, spec_takeBytes_data hspec⟩
  · intro failure h
    unfold SpecAMQP.Ref.takeBeU at h
    cases hb : SpecAMQP.Ref.takeBytes w c' with
    | error e =>
      rw [hb] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      exact takeBytes_fails hc w e hb
    | ok p =>
      rw [hb] at h
      rw [except_bind_ok] at h
      exact absurd h (by simp)

/-- **The one-octet payload step.** The same relation at width one: the reference's `takeU8` hands back
the octet, and the landed width-one bridge says the octet it took is the fold the specification's
`takeBytes 1` performs. -/
theorem stepAgreesAll_takeU8Nat :
    StepAgreesAll (fun (a : SpecAMQP.Harness.Octets) (b : UInt8) => payloadNat a = b.toNat)
      (SpecAMQP.Spec.Codec.takeBytes 1) (SpecAMQP.Ref.takeU8) := by
  intro c c' hc
  constructor
  · intro b d' h
    obtain ⟨d₂, hsu8, hcd⟩ := takeU8_agrees hc b d' h
    obtain ⟨hbytes, hfold⟩ := spec_takeBytes_one_of_takeU8 c b d₂ hsu8
    exact ⟨c.data.extract c.pos (c.pos + 1), d₂, hbytes, by simpa only [payloadNat] using hfold,
      hcd, spec_takeBytes_data hbytes⟩
  · intro failure h
    exact spec_takeBytes_one_fails hc failure h

/-- **The variable rows' length step, four octets wide.** Both readers produce the same number, so the
relation is equality — the difference between the two `takeBe`s is only which of them folds. -/
theorem stepAgreesAll_takeBeEq (w : Nat) :
    StepAgreesAll (fun a b : Nat => a = b) (SpecAMQP.Spec.Codec.takeBe w)
      (SpecAMQP.Ref.takeBeU w) := by
  intro c c' hc
  constructor
  · intro b d' h
    unfold SpecAMQP.Ref.takeBeU at h
    obtain ⟨⟨bytes, d₁'⟩, hb, h⟩ := exists_of_bind_ok h
    dsimp only at h
    rw [except_pure_ok] at h
    have hp : (payloadNat bytes, d₁') = (b, d') := Except.ok.inj h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hm, hd⟩ := hp
    subst hm
    subst hd
    obtain ⟨d, hspec, hcd⟩ := takeBytes_agrees hc w bytes d₁' hb
    have hbe := spec_takeBe_of_takeBytes hspec
    exact ⟨payloadNat bytes, d, hbe, rfl, hcd, spec_takeBe_data hbe⟩
  · intro failure h
    unfold SpecAMQP.Ref.takeBeU at h
    cases hb : SpecAMQP.Ref.takeBytes w c' with
    | error e =>
      rw [hb] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hspec, hcl⟩ := takeBytes_fails hc w e hb
      exact ⟨refusal, (spec_takeBe_error c w refusal).mpr hspec, hcl⟩
    | ok p =>
      rw [hb] at h
      rw [except_bind_ok] at h
      exact absurd h (by simp)

/-- **The variable rows' length step, one octet wide.** Here the reference's octet reader is `takeU8`
while the specification's length field is `takeBe 1`, and the landed width-one bridge relates them:
the number the field carries is the octet's own value. -/
theorem stepAgreesAll_takeBeOne :
    StepAgreesAll (fun (a : Nat) (b : UInt8) => a = b.toNat) (SpecAMQP.Spec.Codec.takeBe 1)
      (SpecAMQP.Ref.takeU8) := by
  intro c c' hc
  constructor
  · intro b d' h
    obtain ⟨d₂, hsu8, hcd⟩ := takeU8_agrees hc b d' h
    have hbe := spec_takeBe_one_of_takeU8 c b d₂ hsu8
    exact ⟨b.toNat, d₂, hbe, rfl, hcd, spec_takeBe_data hbe⟩
  · intro failure h
    obtain ⟨refusal, hspec, hcl⟩ := takeU8_fails hc failure h
    obtain ⟨refusal', hbytes, hcl'⟩ := spec_takeBytes_one_class refusal hspec
    exact ⟨refusal', (spec_takeBe_error c 1 refusal').mpr hbytes, by rw [hcl, hcl']⟩

/-- **A payload the reference decodes is one the specification decodes**, to the same text: both
readers ask the same standard-library question of the same octets, so the success half of the bridge
is an identity. This is the wire-side counterpart of the corpus side's `fixedHex_ok_hexPayloadOf`. -/
theorem utf8Of_ok_of_decodeString {bytes : SpecAMQP.Ref.Octets} {kind : String} {text : String}
    (h : SpecAMQP.Ref.decodeString bytes kind = .ok text) :
    SpecAMQP.Spec.Codec.utf8Of bytes kind = .ok text := by
  unfold SpecAMQP.Ref.decodeString at h
  unfold SpecAMQP.Spec.Codec.utf8Of
  cases hu : String.fromUTF8? (ByteArray.mk bytes) with
  | none => simp only [hu] at h; exact absurd h (by simp)
  | some s => simp only [hu] at h ⊢; injection h with hb; subst hb; rfl

/-- The failure half: the same question refused by both, with the same class — the two readers differ
only in the prose of the refusal, which is why this is a class agreement rather than an equality. -/
theorem utf8Of_error_of_decodeString {bytes : SpecAMQP.Ref.Octets} {kind : String}
    {failure : SpecAMQP.Ref.DecodeError}
    (h : SpecAMQP.Ref.decodeString bytes kind = .error failure) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.utf8Of bytes kind = .error refusal ∧
      (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass := by
  unfold SpecAMQP.Ref.decodeString at h
  cases hu : String.fromUTF8? (ByteArray.mk bytes) with
  | none =>
    simp only [hu] at h
    injection h with hb
    subst hb
    refine ⟨SpecAMQP.Spec.Codec.refusal "malformed"
      s!"a {kind} payload of {bytes.size} octet(s) is not valid UTF-8", ?_, rfl⟩
    unfold SpecAMQP.Spec.Codec.utf8Of
    simp only [hu]
  | some s => simp only [hu] at h; exact absurd h (by simp)

/-- **Two readers agree at one cursor pair.** The two conjuncts of `StepAgrees`, for readers whose
fuel is already spent — which is what a step's *continuation* is, and what the composition below
produces. The value relation is `BodiesAgree`, as in `StepAgrees`, and the buffer component says a
reader hands back the buffer it was given. -/
def ReadersAgreeAt
    (Ks : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor))
    (Kr : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor))
    (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (other : SpecAMQP.Ref.Value) (c₂' : SpecAMQP.Ref.Cursor), Kr c' = .ok (other, c₂') →
      ∃ (body : SpecAMQP.Spec.Codec.Value) (c₂ : SpecAMQP.Spec.Codec.Cursor),
        Ks c = .ok (body, c₂) ∧ CursorAgrees c₂ c₂' ∧ c₂.data = c.data ∧ BodiesAgree body other) ∧
  (∀ failure : SpecAMQP.Ref.DecodeError, Kr c' = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal, Ks c = .error refusal ∧
        (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- The same obligation at every pair of agreeing cursors.

`private` because nothing outside this module names it, and because the name is already spoken for in
this namespace: `Proofs.ConnectionConformance`'s `ReadersAgree` is the frame layer's hypothesis and
`Contracts.ConnectionConformance` names it in that layer's acceptance declaration, so the wire side is
the one that has to move. -/
private def ReadersAgree
    (Ks : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor))
    (Kr : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor)) : Prop :=
  ∀ (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor),
    CursorAgrees c c' → ReadersAgreeAt Ks Kr c c'

/-- **The two text families' decode, at one payload.** The same octets, the same standard-library
test, the same string on success and the same class on refusal — stated as the *reader* each artefact
writes (`utf8Of` then a value, the reference's `decodeStringAt` two-step), because the value the two
readers answer is the text rather than the octets they took. `Sv`/`Rv` are the two artefacts'
spellings of the value that text makes, which is what lets `string` and `symbol` share this lemma.
The payload is an explicit argument because this reader is *indexed* by what the reader above it
took, and the same array on both sides is what that reader's own agreement already gave. -/
theorem readersAgree_utf8 (kind : String) (bytes : SpecAMQP.Harness.Octets)
    (Sv : String → SpecAMQP.Spec.Codec.Value) (Rv : String → SpecAMQP.Ref.Value)
    (hval : ∀ text : String, BodiesAgree (Sv text) (Rv text)) :
    ReadersAgree
      (fun f : SpecAMQP.Spec.Codec.Cursor =>
        SpecAMQP.Spec.Codec.utf8Of bytes kind >>= fun s => .ok (Sv s, f))
      (fun f' : SpecAMQP.Ref.Cursor =>
        SpecAMQP.Ref.decodeStringAt bytes kind f' >>= fun r => .ok (Rv r.1, r.2)) := by
  intro c c' hc
  constructor
  · intro other c₂' h
    dsimp only at h
    cases hd : SpecAMQP.Ref.decodeString bytes kind with
    | error e =>
      have hda : SpecAMQP.Ref.decodeStringAt bytes kind c' = .error e := by
        unfold SpecAMQP.Ref.decodeStringAt
        rw [hd]
      rw [hda] at h
      rw [except_bind_error] at h
      exact absurd h (by simp)
    | ok text =>
      have hda : SpecAMQP.Ref.decodeStringAt bytes kind c' = .ok (text, c') := by
        unfold SpecAMQP.Ref.decodeStringAt
        rw [hd]
      rw [hda] at h
      rw [except_bind_ok] at h
      dsimp only at h
      obtain ⟨hother, hcur⟩ : Rv text = other ∧ c' = c₂' := by
        have hp := Except.ok.inj h
        simpa only [Prod.mk.injEq] using hp
      subst hother
      subst hcur
      refine ⟨Sv text, c, ?_, hc, rfl, hval text⟩
      dsimp only
      rw [utf8Of_ok_of_decodeString hd, except_bind_ok]
  · intro failure h
    dsimp only at h
    cases hd : SpecAMQP.Ref.decodeString bytes kind with
    | ok text =>
      have hda : SpecAMQP.Ref.decodeStringAt bytes kind c' = .ok (text, c') := by
        unfold SpecAMQP.Ref.decodeStringAt
        rw [hd]
      rw [hda] at h
      rw [except_bind_ok] at h
      exact absurd h (by simp)
    | error e =>
      have hda : SpecAMQP.Ref.decodeStringAt bytes kind c' = .error e := by
        unfold SpecAMQP.Ref.decodeStringAt
        rw [hd]
      rw [hda] at h
      rw [except_bind_error] at h
      rw [Except.error.injEq] at h
      subst h
      obtain ⟨r, hspec, hcl⟩ := utf8Of_error_of_decodeString hd
      refine ⟨r, ?_, hcl⟩
      dsimp only
      rw [hspec, except_bind_error]
/-- **A row that reads nothing but its octet.** The two readers answer a value and hand their cursors
back; the value relation and the cursor agreement are the whole content, and the refusal half is
vacuous because neither reader refuses. -/
theorem reader_of_ok (fuel : Nat) {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    {d : SpecAMQP.Spec.Codec.Cursor} {d' : SpecAMQP.Ref.Cursor} (hd : CursorAgrees d d')
    (Sv : SpecAMQP.Spec.Codec.Value) (Rv : SpecAMQP.Ref.Value) (hval : BodiesAgree Sv Rv)
    (hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (Sv, d))
    (hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (Rv, d'))
    (hdata : d.data = c.data) : StepAgrees (fuel + 1) c c' := by
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨hother, hcur⟩ : Rv = other ∧ d' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    exact ⟨Sv, d, hS, hd, hdata, hval⟩
  · intro failure h
    rw [hR] at h
    exact absurd h (by simp)

/-- **A row that reads one payload.** The step hands the reference a value the specification reaches
too — related to it by `R` — and the arm answers a value from each; `hval` is the arm's own content,
and it is stated against the specification's *step success* because that is where a width-carrying
arm's bound on the number it read comes from: `R` alone cannot bound `payloadNat` of the payload a
reader happened to accept, but the read that accepted it can. -/
theorem reader_of_step {α β : Type} {R : α → β → Prop}
    {StepS : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor)}
    {StepR : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    {fuel : Nat} {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    {d : SpecAMQP.Spec.Codec.Cursor} {d' : SpecAMQP.Ref.Cursor}
    (hstep : StepAgreesAt R StepS StepR d d')
    (Sv : α → SpecAMQP.Spec.Codec.Value) (Rv : β → SpecAMQP.Ref.Value)
    (hval : ∀ (a : α) (b : β), R a b → ∀ f : SpecAMQP.Spec.Codec.Cursor,
      StepS d = .ok (a, f) → BodiesAgree (Sv a) (Rv b))
    (hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = StepS d >>= fun p => .ok (Sv p.1, p.2))
    (hR : SpecAMQP.Ref.readValue (fuel + 1) c' = StepR d' >>= fun p => .ok (Rv p.1, p.2))
    (hdata : d.data = c.data) : StepAgrees (fuel + 1) c c' := by
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨⟨b, d₂'⟩, hb, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨hother, hcur⟩ : Rv b = other ∧ d₂' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    obtain ⟨a, f₂, hf, hrel, hcd, hdat⟩ := hstep.1 b d₂' hb
    exact ⟨Sv a, f₂, by rw [hS, hf, except_bind_ok], hcd, by rw [hdat, hdata],
      hval a b hrel f₂ hf⟩
  · intro failure h
    rw [hR] at h
    cases hb : StepR d' with
    | error e =>
      rw [hb] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hspec, hcl⟩ := hstep.2 e hb
      exact ⟨refusal, by rw [hS, hspec, except_bind_error], hcl⟩
    | ok p =>
      rw [hb] at h
      rw [except_bind_ok] at h
      exact absurd h (by simp)

/-- **A step composed with a reader below it.** The step's success hands back a value and two agreeing
cursors, and the reader below is applied there; this is the same reduction as `stepAgreesAll_bind`,
one level down, and it is what a variable row's length-then-payload read is. -/
theorem readersAgreeAt_bind {α β : Type} {R : α → β → Prop}
    {StepS : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor)}
    {StepR : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    {d : SpecAMQP.Spec.Codec.Cursor} {d' : SpecAMQP.Ref.Cursor}
    (hstep : StepAgreesAt R StepS StepR d d')
    {Ks : α → SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor)}
    {Kr : β → SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor)}
    (hinner : ∀ (a : α) (b : β), R a b → ReadersAgree (Ks a) (Kr b)) :
    ReadersAgreeAt (fun c => StepS c >>= fun p => Ks p.1 p.2)
      (fun c' => StepR c' >>= fun p => Kr p.1 p.2) d d' := by
  constructor
  · intro other c₂' h
    dsimp only at h ⊢
    obtain ⟨⟨b, d₁'⟩, hb, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨a, d₁, hspec, hrel, hcd, hdat⟩ := hstep.1 b d₁' hb
    obtain ⟨body, d₂, hk, hcd2, hdat2, hba⟩ := (hinner a b hrel d₁ d₁' hcd).1 other c₂' h
    exact ⟨body, d₂, by rw [hspec, except_bind_ok, hk], hcd2, by rw [hdat2, hdat], hba⟩
  · intro failure h
    dsimp only at h ⊢
    cases hb : StepR d' with
    | error e =>
      rw [hb] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hspec, hcl⟩ := hstep.2 e hb
      exact ⟨refusal, by rw [hspec, except_bind_error], hcl⟩
    | ok p =>
      obtain ⟨b, d₁'⟩ := p
      rw [hb] at h
      rw [except_bind_ok] at h
      obtain ⟨a, d₁, hspec, hrel, hcd, -⟩ := hstep.1 b d₁' hb
      cases hb2 : Kr b d₁' with
      | error e =>
        rw [hb2] at h
        rw [Except.error.injEq] at h
        subst h
        obtain ⟨refusal, hspec2, hcl⟩ := (hinner a b hrel d₁ d₁' hcd).2 e hb2
        exact ⟨refusal, by rw [hspec, except_bind_ok, hspec2], hcl⟩
      | ok q =>
        rw [hb2] at h
        exact absurd h (by simp)

/-- The same, at every pair of agreeing cursors: the form an inner reader is *used* in. -/
theorem readersAgree_bind {α β : Type} {R : α → β → Prop}
    {StepS : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor)}
    {StepR : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    (hstep : StepAgreesAll R StepS StepR)
    {Ks : α → SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor)}
    {Kr : β → SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor)}
    (hinner : ∀ (a : α) (b : β), R a b → ReadersAgree (Ks a) (Kr b)) :
    ReadersAgree (fun c => StepS c >>= fun p => Ks p.1 p.2)
      (fun c' => StepR c' >>= fun p => Kr p.1 p.2) :=
  fun c c' hc => readersAgreeAt_bind (hstep c c' hc) hinner

/-- **A reader that answers a value and hands its cursor back.** The last step of every arm's chain:
the two readers have their payload and their value, nothing is consumed, and the agreement is the
value relation alone. -/
theorem readersAgree_ok (Sv : SpecAMQP.Spec.Codec.Value) (Rv : SpecAMQP.Ref.Value)
    (hval : BodiesAgree Sv Rv) :
    ReadersAgree (fun c => .ok (Sv, c)) (fun c' => .ok (Rv, c')) := by
  intro c c' hc
  constructor
  · intro other c₂' h
    obtain ⟨hother, hcur⟩ : Rv = other ∧ c' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    exact ⟨Sv, c, rfl, hc, rfl, hval⟩
  · intro failure h
    exact absurd h (by simp)

/-- **A variable row: a length field, then the payload that field announced.** The outer step's value
decides the inner reader's, and the inner reader's agreement holds at whatever cursors the outer step
left — which is why it is `ReadersAgree` rather than an obligation at `d`/`d'`. The rows that use this
stem are the six whose read is two steps deep: the payload step is the *whole* rest of the reader,
including the value it answers, so the composite is a reader rather than a step. -/
theorem reader_of_two_steps {α β : Type} {R : α → β → Prop}
    {Step1S : SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (α × SpecAMQP.Spec.Codec.Cursor)}
    {Step1R : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    {fuel : Nat} {c : SpecAMQP.Spec.Codec.Cursor} {c' : SpecAMQP.Ref.Cursor}
    {d : SpecAMQP.Spec.Codec.Cursor} {d' : SpecAMQP.Ref.Cursor}
    (Step2S : α → SpecAMQP.Spec.Codec.Cursor → Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor))
    (Step2R : β → SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor))
    (h1 : StepAgreesAt R Step1S Step1R d d')
    (hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = Step1S d >>= fun p => Step2S p.1 p.2)
    (hR : SpecAMQP.Ref.readValue (fuel + 1) c' = Step1R d' >>= fun p => Step2R p.1 p.2)
    (h2 : ∀ (a : α) (b : β), R a b → ReadersAgree (Step2S a) (Step2R b))
    (hdata : d.data = c.data) : StepAgrees (fuel + 1) c c' := by
  obtain ⟨hok, herr⟩ := readersAgreeAt_bind h1 h2
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨body, c₂, hr, hcd, hdat, hba⟩ := hok other c₂' h
    refine ⟨body, c₂, ?_, hcd, ?_, hba⟩
    · rw [hS]
      exact hr
    · rw [hdat, hdata]
  · intro failure h
    rw [hR] at h
    obtain ⟨refusal, hr, hcl⟩ := herr failure h
    exact ⟨refusal, by rw [hS]; exact hr, hcl⟩

/-! ## The fixed-width arms

Everything below is one row of the declared surface per theorem, and every one of them is the octet
step's hypothesis plus three `decide`-checked facts and an instance of a stem. What each row owes
that its neighbours do not is stated in its own docstring; the groups, and why each is the size it is:

* the zero-width rows (`0x41`–`0x45`) read no payload at all — the table names the value, and the
  reference matches the octet — so they go through `reader_of_ok` and owe only their row;
* the one-octet payloads (`0x52`, `0x53`, `0x56`) read their octet through the specification's
  `takeBytes 1` and the reference's `takeU8`, which is `stepAgreesAll_takeU8Nat`: the relation is
  `payloadNat` against the octet's own value, and the value equations are the width-carrying round
  trips `Proofs/ValueCarrierAgreement` states for the corpus side (`u8_toNat` and its siblings);
* the wide unsigned and `char` rows (`0x60`, `0x70`, `0x73`, `0x80`) read a big-endian field, so
  their relation is `payloadNat a = b` and their value equations need the number's *bound*, which is
  why `reader_of_step`'s value hypothesis is stated against the specification's own step success:
  `payloadNat_lt_of_takeBytes` reads the bound off the read;
* the opaque rows (`0x72`, `0x74`, `0x82`, `0x84`, `0x94`, `0x98`) carry their payload octets and
  compare nothing, so their relation is equality of arrays and their value equations are `rfl`.

What is deliberately *not* here: the seven signed rows, whose value equations need a
`SpecAMQP.Spec.Codec.signedOfOctets` round trip, and the compound and array rows, which need the loop relations. Both are
named in the module's header and in the plan rather than left to look finished. -/

/-- **The octet an 8-bit boolean carries is zero exactly when the octet is `0x00`.** The reference
compares the octet, the specification compares the number it folded the octet into, so this is the
`0x56` row's whole value equation. Stated through `UInt8.toNat_inj` rather than by case analysis on
the carrier, because the two `!=`s are `Bool`s and the bridge between them is the proposition. -/
theorem uint8_ne_zero_bool (b : UInt8) : (b.toNat != 0) = (b != 0x00) := by
  have key : b.toNat = 0 ↔ b = 0 := by
    rw [← show (0 : UInt8).toNat = 0 from rfl]
    exact UInt8.toNat_inj
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq]
  exact not_congr key

/-- **The `true` row (`0x41`).** The table names the boolean and declares no payload, so the
specification reads its zero octets and answers `true`; the reference matches the octet. -/
theorem arm_0x41 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x41, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x41, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x41 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x41 : UInt8) =
      .ok ⟨65, some "true", SpecAMQP.Generated.Oasis.Category.fixed, 0, "boolean",
        "the boolean value true"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.boolean true, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.boolean true, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree]) hS hR (spec_takeU8_data hs)

/-- **The `false` row (`0x42`).** The same row at the other boolean. -/
theorem arm_0x42 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x42, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x42, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x42 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x42 : UInt8) =
      .ok ⟨66, some "false", SpecAMQP.Generated.Oasis.Category.fixed, 0, "boolean",
        "the boolean value false"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.boolean false, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.boolean false, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree]) hS hR (spec_takeU8_data hs)

/-- **The `uint0` row (`0x43`).** The specification's fixed-width reader folds the zero octets it
took into the number zero and answers `uint 0`; the reference matches the octet and answers the same.
The fold over an empty payload is the accumulator, definitionally. -/
theorem arm_0x43 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x43, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x43, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x43 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x43 : UInt8) =
      .ok ⟨67, some "uint0", SpecAMQP.Generated.Oasis.Category.fixed, 0, "uint",
        "the uint value 0"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.uint 0, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.uint 0, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree]; decide) hS hR
    (spec_takeU8_data hs)

/-- **The `ulong0` row (`0x44`).** The same zero form at the wider type. -/
theorem arm_0x44 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x44, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x44, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x44 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x44 : UInt8) =
      .ok ⟨68, some "ulong0", SpecAMQP.Generated.Oasis.Category.fixed, 0, "ulong",
        "the ulong value 0"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.ulong 0, d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.ulong 0, d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree]; decide) hS hR
    (spec_takeU8_data hs)

/-- **The `list0` row (`0x45`).** The declared surface's zero-width `list`, which the specification's
fixed-width reader answers as the empty list without recursing — one of the six zero-width rows that
make an array of zero-width elements bounded by its count rather than by the buffer. -/
theorem arm_0x45 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x45, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x45, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x45 : UInt8).toNat = .fixed 0 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x45 : UInt8) =
      .ok ⟨69, some "list0", SpecAMQP.Generated.Oasis.Category.fixed, 0, "list",
        "the empty list (i.e. the list with no elements)"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .ok (.list [], d) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero d (spec_takeU8_next_le hs), except_bind_ok]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = .ok (.list [], d') := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_ok fuel hd _ _ (by simp only [BodiesAgree, BodiesAgreeList]) hS hR
    (spec_takeU8_data hs)

/-- **The `smalluint` row (`0x52`).** One octet, read as an unsigned integer: the specification folds
the octet it took and the reference keeps it as a `UInt8`, so the value equation is the width-carrying
round trip (`UInt8.toNat_toUInt32`). -/
theorem arm_0x52 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x52, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x52, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x52 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x52 : UInt8) =
      .ok ⟨82, some "smalluint", SpecAMQP.Generated.Oasis.Category.fixed, 1, "uint",
        "unsigned integer value in the range 0 to 255 inclusive"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p => .ok (.uint (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p => .ok (.uint p.1.toUInt32, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd) (fun bytes => .uint (payloadNat bytes))
    (fun b => .uint b.toUInt32)
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt8.toNat_toUInt32 b).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `smallulong` row (`0x53`).** The same one-octet payload at the wider type. -/
theorem arm_0x53 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x53, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x53, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x53 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x53 : UInt8) =
      .ok ⟨83, some "smallulong", SpecAMQP.Generated.Oasis.Category.fixed, 1, "ulong",
        "unsigned long value in the range 0 to 255 inclusive"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p => .ok (.ulong (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p => .ok (.ulong p.1.toUInt64, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd) (fun bytes => .ulong (payloadNat bytes))
    (fun b => .ulong b.toUInt64)
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt8.toNat_toUInt64 b).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `boolean` row at one octet (`0x56`).** The one row whose two readers compare the payload in
different spellings: the specification folds the octet and asks whether the *number* is zero, the
reference asks whether the *octet* is `0x00`. `uint8_ne_zero_bool` is the whole value equation. -/
theorem arm_0x56 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x56, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x56, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x56 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x56 : UInt8) =
      .ok ⟨86, none, SpecAMQP.Generated.Oasis.Category.fixed, 1, "boolean",
        "boolean with the octet 0x00 being false and octet 0x01 being true"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p => .ok (.boolean (payloadNat p.1 != 0), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p => .ok (.boolean (p.1 != 0x00), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd)
    (fun bytes => .boolean (payloadNat bytes != 0)) (fun b => .boolean (b != 0x00))
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact uint8_ne_zero_bool b)
    hS hR (spec_takeU8_data hs)

/-- **The `ushort` row (`0x60`).** Two octets folded into a number: the bound that makes the
specification's `Nat` the reference's `UInt16` is the read's own (`payloadNat_lt_of_takeBytes`), and
the value equation is the width-carrying round trip the corpus side states as `u16_toNat`. -/
theorem arm_0x60 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x60, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x60, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x60 : UInt8).toNat = .fixed 2 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x60 : UInt8) =
      .ok ⟨96, none, SpecAMQP.Generated.Oasis.Category.fixed, 2, "ushort",
        "16-bit unsigned integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 2 d >>= fun p => .ok (.ushort (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 2 d' >>= fun p => .ok (.ushort p.1.toUInt16, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 2 d d' hd) (fun bytes => .ushort (payloadNat bytes))
    (fun n => .ushort n.toUInt16)
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 16 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt16.toNat_ofNat_of_lt (n := b) hlt).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `uint` row (`0x70`).** The same fold at four octets. -/
theorem arm_0x70 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x70, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x70, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x70 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x70 : UInt8) =
      .ok ⟨112, none, SpecAMQP.Generated.Oasis.Category.fixed, 4, "uint",
        "32-bit unsigned integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p => .ok (.uint (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p => .ok (.uint p.1.toUInt32, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 4 d d' hd) (fun bytes => .uint (payloadNat bytes))
    (fun n => .uint n.toUInt32)
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 32 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt32.toNat_ofNat_of_lt (n := b) hlt).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `char` row (`0x73`).** The row the artifact frames as UTF-32BE, which this layer reads as
the number it is: the same fold and the same width-carrying round trip as `uint`, and no judgement
about whether the code point is assigned — that is the corpus vocabulary's business, not the wire's. -/
theorem arm_0x73 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x73, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x73, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x73 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x73 : UInt8) =
      .ok ⟨115, some "utf32", SpecAMQP.Generated.Oasis.Category.fixed, 4, "char",
        "a UTF-32BE encoded Unicode character"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p => .ok (.char (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p => .ok (.char p.1.toUInt32, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 4 d d' hd) (fun bytes => .char (payloadNat bytes))
    (fun n => .char n.toUInt32)
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 32 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt32.toNat_ofNat_of_lt (n := b) hlt).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `ulong` row (`0x80`).** The same fold at eight octets, where the bound is `2 ^ 64`. -/
theorem arm_0x80 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x80, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x80, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x80 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x80 : UInt8) =
      .ok ⟨128, none, SpecAMQP.Generated.Oasis.Category.fixed, 8, "ulong",
        "64-bit unsigned integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p => .ok (.ulong (payloadNat p.1), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 8 d' >>= fun p => .ok (.ulong p.1.toUInt64, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 8 d d' hd) (fun bytes => .ulong (payloadNat bytes))
    (fun n => .ulong n.toUInt64)
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 64 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt64.toNat_ofNat_of_lt (n := b) hlt).symm)
    hS hR (spec_takeU8_data hs)


/-! ## The opaque widths

Six rows carry their payload without interpreting it: the artifact fixes these encodings' framing and
nothing in this layer does arithmetic on their contents, so the two readers answer the *octets* they
took. That makes them the cheapest group of all — the step relation is equality of arrays and the
value equation is `rfl` — and it is worth saying why the group is not smaller: `float`, `double`, the
three decimals and `uuid` are the six rows of the declared surface whose payload the value domain
keeps rather than reduces, and each one is still a separate arm because each is a separate arm of the
reference's own literal dispatch. -/

/-- **The `float` row (`0x72`).** Four payload octets, carried as they were read. -/
theorem arm_0x72 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x72, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x72, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x72 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x72 : UInt8) =
      .ok ⟨114, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 4, "float",
        "IEEE 754-2008 binary32"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p => .ok (.float p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 4 d' >>= fun p => .ok (.float p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 4 d d' hd) (fun bytes => .float bytes)
    (fun bytes => .float bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `decimal32` row (`0x74`).** The same four octets under the artifact's Binary Integer Decimal
framing, which this layer does not decode — the framing is what the row fixes. -/
theorem arm_0x74 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x74, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x74, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x74 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x74 : UInt8) =
      .ok ⟨116, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 4, "decimal32",
        "IEEE 754-2008 decimal32 using the Binary Integer Decimal encoding"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p => .ok (.decimal32 p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 4 d' >>= fun p => .ok (.decimal32 p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 4 d d' hd) (fun bytes => .decimal32 bytes)
    (fun bytes => .decimal32 bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `double` row (`0x82`).** The same carrier at eight octets. -/
theorem arm_0x82 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x82, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x82, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x82 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x82 : UInt8) =
      .ok ⟨130, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 8, "double",
        "IEEE 754-2008 binary64"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p => .ok (.double p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 8 d' >>= fun p => .ok (.double p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 8 d d' hd) (fun bytes => .double bytes)
    (fun bytes => .double bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `decimal64` row (`0x84`).** The same eight octets under the decimal framing. -/
theorem arm_0x84 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x84, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x84, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x84 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x84 : UInt8) =
      .ok ⟨132, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 8, "decimal64",
        "IEEE 754-2008 decimal64 using the Binary Integer Decimal encoding"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p => .ok (.decimal64 p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 8 d' >>= fun p => .ok (.decimal64 p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 8 d d' hd) (fun bytes => .decimal64 bytes)
    (fun bytes => .decimal64 bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `decimal128` row (`0x94`).** Sixteen octets, the widest opaque payload the surface
declares. -/
theorem arm_0x94 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x94, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x94, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x94 : UInt8).toNat = .fixed 16 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x94 : UInt8) =
      .ok ⟨148, some "ieee-754", SpecAMQP.Generated.Oasis.Category.fixed, 16, "decimal128",
        "IEEE 754-2008 decimal128 using the Binary Integer Decimal encoding"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 16 d >>= fun p => .ok (.decimal128 p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 16 d' >>= fun p => .ok (.decimal128 p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 16 d d' hd) (fun bytes => .decimal128 bytes)
    (fun bytes => .decimal128 bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)

/-- **The `uuid` row (`0x98`).** The same sixteen octets, whose fields this layer does not interpret:
the artifact fixes the width and the octet order, not what the fields mean. -/
theorem arm_0x98 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x98, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x98, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x98 : UInt8).toNat = .fixed 16 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x98 : UInt8) =
      .ok ⟨152, none, SpecAMQP.Generated.Oasis.Category.fixed, 16, "uuid",
        "UUID as defined in section 4.1.2 of RFC-4122"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 16 d >>= fun p => .ok (.uuid p.1, p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBytes 16 d' >>= fun p => .ok (.uuid p.1, p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBytes 16 d d' hd) (fun bytes => .uuid bytes)
    (fun bytes => .uuid bytes)
    (fun a b hrel _ _ => by simpa only [BodiesAgree] using hrel)
    hS hR (spec_takeU8_data hs)


/-! ## The variable rows

Six rows announce their own payload's length: `binary`, `string` and `symbol` in the eight- and
thirty-two-bit forms. They are the only arms whose read is *two* steps deep — a length field, then the
payload that field announced — and the reference reads the eight-bit length with its octet reader
(`takeU8`) while the specification reads it as a field (`takeBe 1`), which is
`stepAgreesAll_takeBeOne`: the relation is that the field's number is the octet's own value. The
thirty-two-bit rows agree on the number itself (`stepAgreesAll_takeBeEq`), because both readers fold
the same four octets.

The inner reader is `readersAgree_bind`'s composition: it takes the payload the outer step's number
announced and reads it at the cursors the outer step handed back. For `binary` the inner reader is the
payload read followed by the value (`readersAgree_ok`); for `string` and `symbol` it is the payload
read composed with `readersAgree_utf8`, the same-octets-same-text bridge above. -/

/-- **The `vbin8` row (`0xA0`).** A one-octet length, then that many octets carried as binary. -/
theorem arm_0xA0 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xA0, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xA0, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xA0 : UInt8).toNat = .variable 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xA0 : UInt8) =
      .ok ⟨160, some "vbin8", SpecAMQP.Generated.Oasis.Category.variable, 1, "binary",
        "up to 2^8 - 1 octets of binary data"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 1 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q => .ok (.binary q.1, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1.toNat p.2 >>= fun q => .ok (.binary q.1.toList, q.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q => .ok (.binary q.1, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b.toNat f' >>= fun q => .ok (.binary q.1.toList, q.2))
    (stepAgreesAll_takeBeOne d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_ok (.binary bytes) (.binary bytes.toList)
            (by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `vbin32` row (`0xB0`).** The same payload behind a four-octet length, which both readers
fold the same way. -/
theorem arm_0xB0 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xB0, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xB0, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xB0 : UInt8).toNat = .variable 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xB0 : UInt8) =
      .ok ⟨176, some "vbin32", SpecAMQP.Generated.Oasis.Category.variable, 4, "binary",
        "up to 2^32 - 1 octets of binary data"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 4 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q => .ok (.binary q.1, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1 p.2 >>= fun q => .ok (.binary q.1.toList, q.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q => .ok (.binary q.1, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b f' >>= fun q => .ok (.binary q.1.toList, q.2))
    (stepAgreesAll_takeBeEq 4 d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_ok (.binary bytes) (.binary bytes.toList)
            (by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `str8-utf8` row (`0xA1`).** A one-octet length, the payload, then the payload decoded as
UTF-8 — the step `stepAgreesAll_utf8` carries, since both readers ask the same standard-library
question and the only difference is the refusal's prose. -/
theorem arm_0xA1 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xA1, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xA1, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xA1 : UInt8).toNat = .variable 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xA1 : UInt8) =
      .ok ⟨161, some "str8-utf8", SpecAMQP.Generated.Oasis.Category.variable, 1, "string",
        "up to 2^8 - 1 octets worth of UTF-8 Unicode (with no byte order mark)"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 1 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1.toNat p.2 >>= fun q =>
          SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b.toNat f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2))
    (stepAgreesAll_takeBeOne d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "string" bytes (fun s => .string s) (fun s => .string s)
            (fun s => by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `str32-utf8` row (`0xB1`).** The same text payload behind a four-octet length. -/
theorem arm_0xB1 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xB1, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xB1, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xB1 : UInt8).toNat = .variable 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xB1 : UInt8) =
      .ok ⟨177, some "str32-utf8", SpecAMQP.Generated.Oasis.Category.variable, 4, "string",
        "up to 2^32 - 1 octets worth of UTF-8 Unicode (with no byte order mark)"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 4 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2))
    (stepAgreesAll_takeBeEq 4 d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "string" bytes (fun s => .string s) (fun s => .string s)
            (fun s => by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `sym8` row (`0xA3`).** The symbol payload, which this layer decodes through the same UTF-8
test as `string`: the artifact restricts symbols to ASCII on the wire, and requiring the stricter of
the two rules is what makes the two artefacts agree on the payload. -/
theorem arm_0xA3 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xA3, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xA3, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xA3 : UInt8).toNat = .variable 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xA3 : UInt8) =
      .ok ⟨163, some "sym8", SpecAMQP.Generated.Oasis.Category.variable, 1, "symbol",
        "up to 2^8 - 1 seven bit ASCII characters representing a symbolic value"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 1 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1.toNat p.2 >>= fun q =>
          SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b.toNat f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2))
    (stepAgreesAll_takeBeOne d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "symbol" bytes (fun s => .symbol s) (fun s => .symbol s)
            (fun s => by simp only [BodiesAgree])))
    (spec_takeU8_data hs)

/-- **The `sym32` row (`0xB3`).** The same symbol payload behind a four-octet length. -/
theorem arm_0xB3 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xB3, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xB3, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0xB3 : UInt8).toNat = .variable 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xB3 : UInt8) =
      .ok ⟨179, some "sym32", SpecAMQP.Generated.Oasis.Category.variable, 4, "symbol",
        "up to 2^32 - 1 seven bit ASCII characters representing a symbolic value"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBe 4 d >>= fun p =>
        SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readVariable]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p =>
        SpecAMQP.Ref.takeBytes p.1 p.2 >>= fun q =>
          SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_two_steps
    (fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2))
    (fun b f' => SpecAMQP.Ref.takeBytes b f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2))
    (stepAgreesAll_takeBeEq 4 d d' hd)
    hS hR
    (fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "symbol" bytes (fun s => .symbol s) (fun s => .symbol s)
            (fun s => by simp only [BodiesAgree])))
    (spec_takeU8_data hs)


/-! ## The signed rows

Seven rows carry two's-complement integers, and each owes a *value equation* rather than a new read:
the specification computes the field's value with `SpecAMQP.Spec.Codec.signedOfOctets` (a conditional subtraction of the
modulus) while the reference keeps it in a width-carrying carrier (`Int8`…`Int64`) built from the
same octets. The bridges below are therefore pure arithmetic on two spellings of one number, and the
three narrow rows (`0x51`, `0x54`, `0x55` — one octet carrying a wider-typed value) additionally need
the reference's *sign extension*: `Int32.ofBitVec (BitVec.ofNat 32 (signedOctet b % 2 ^ 32).toNat)`.
`Proofs/ValueCarrierAgreement`'s `i8_toInt`…`i64_toInt` are exactly that sign extension — the corpus
side reached them from the other direction — which is why this module imports that one. -/

/-- **A two's-complement field, as the carrier the same octets make.** `SpecAMQP.Spec.Codec.signedOfOctets` subtracts the
modulus above the half-way point and `BitVec.toInt` does the same, so the two are one function in two
spellings; the condition each tests is `2 * m < 2 ^ (8 * w)`, which is `m < 2 ^ (8 * w - 1)`. -/
theorem signedOfOctets_8 (m : Nat) (h : m < 2 ^ 8) :
    SpecAMQP.Spec.Codec.signedOfOctets 1 m = (Int8.ofBitVec (BitVec.ofNat 8 m)).toInt := by
  rw [Int8.toInt_ofBitVec, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  split <;> split <;> omega

/-- The same at two octets. -/
theorem signedOfOctets_16 (m : Nat) (h : m < 2 ^ 16) :
    SpecAMQP.Spec.Codec.signedOfOctets 2 m = (Int16.ofBitVec (BitVec.ofNat 16 m)).toInt := by
  rw [Int16.toInt_ofBitVec, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  split <;> split <;> omega

/-- The same at four octets. -/
theorem signedOfOctets_32 (m : Nat) (h : m < 2 ^ 32) :
    SpecAMQP.Spec.Codec.signedOfOctets 4 m = (Int32.ofBitVec (BitVec.ofNat 32 m)).toInt := by
  rw [Int32.toInt_ofBitVec, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  split <;> split <;> omega

/-- The same at eight octets. -/
theorem signedOfOctets_64 (m : Nat) (h : m < 2 ^ 64) :
    SpecAMQP.Spec.Codec.signedOfOctets 8 m = (Int64.ofBitVec (BitVec.ofNat 64 m)).toInt := by
  rw [Int64.toInt_ofBitVec, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  split <;> split <;> omega

/-- **The reference's octet reader, as the specification's one-octet field.** The reference spells a
signed octet `signedOctet`, the specification `SpecAMQP.Spec.Codec.signedOfOctets 1`; this is the first bridge as an
equation between the two, which is what the narrow rows' value equations rewrite through. -/
theorem signedOctet_eq (b : UInt8) :
    SpecAMQP.Ref.signedOctet b = SpecAMQP.Spec.Codec.signedOfOctets 1 b.toNat := by
  unfold SpecAMQP.Ref.signedOctet
  exact (signedOfOctets_8 b.toNat b.toNat_lt).symm

/-- The range a signed octet's value actually occupies, which is what the sign-extension lemmas below
need: one octet of two's complement is `-2 ^ 7` to `2 ^ 7 - 1`, never the wider type's extremes. -/
theorem signedOctet_bounds (b : UInt8) :
    -(2 ^ 7) ≤ SpecAMQP.Ref.signedOctet b ∧ SpecAMQP.Ref.signedOctet b ≤ 2 ^ 7 - 1 := by
  rw [signedOctet_eq b]
  unfold SpecAMQP.Spec.Codec.signedOfOctets
  have hlt := b.toNat_lt
  split <;> omega

/-- **The reference's sign extension into `Int32`.** A signed octet read into a four-octet carrier
keeps its sign: the octet's value is taken modulo the wider modulus and interpreted again, which is
the identity exactly on the octet's own range. `Proofs/ValueCarrierAgreement`'s `i32_toInt` is this
statement, reached from the corpus side; here it is applied to what the *reader* produced. -/
theorem signedOctet_int32 (b : UInt8) :
    (Int32.ofBitVec (BitVec.ofNat 32
      (SpecAMQP.Ref.signedOctet b % 4294967296).toNat)).toInt = SpecAMQP.Spec.Codec.signedOfOctets 1 b.toNat := by
  rw [← signedOctet_eq b]
  exact i32_toInt (SpecAMQP.Ref.signedOctet b) (by have := signedOctet_bounds b; omega)
    (by have := signedOctet_bounds b; omega)

/-- The same sign extension into `Int64`. -/
theorem signedOctet_int64 (b : UInt8) :
    (Int64.ofBitVec (BitVec.ofNat 64
      (SpecAMQP.Ref.signedOctet b % 18446744073709551616).toNat)).toInt =
      SpecAMQP.Spec.Codec.signedOfOctets 1 b.toNat := by
  rw [← signedOctet_eq b]
  exact i64_toInt (SpecAMQP.Ref.signedOctet b) (by have := signedOctet_bounds b; omega)
    (by have := signedOctet_bounds b; omega)

/-- **The `byte` row (`0x51`).** One octet, read as a signed byte: the specification's field value and
the reference's `Int8` carrier are the same number in two spellings. -/
theorem arm_0x51 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x51, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x51, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x51 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x51 : UInt8) =
      .ok ⟨81, none, SpecAMQP.Generated.Oasis.Category.fixed, 1, "byte",
        "8-bit two's-complement integer"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p =>
        .ok (.byte (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        .ok (.byte (Int8.ofBitVec (BitVec.ofNat 8 p.1.toNat)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd)
    (fun bytes => .byte (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat bytes)))
    (fun b => .byte (Int8.ofBitVec (BitVec.ofNat 8 b.toNat)))
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_8 b.toNat b.toNat_lt)
    hS hR (spec_takeU8_data hs)

/-- **The `smallint` row (`0x54`).** One octet read into a four-octet `int`: the reference sign-extends
the octet, which is `signedOctet_int32`, and the specification's one-octet field already carries that
value. -/
theorem arm_0x54 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x54, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x54, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x54 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x54 : UInt8) =
      .ok ⟨84, some "smallint", SpecAMQP.Generated.Oasis.Category.fixed, 1, "int",
        "8-bit two's-complement integer"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p =>
        .ok (.int (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        .ok (.int (Int32.ofBitVec (BitVec.ofNat 32
          (SpecAMQP.Ref.signedOctet p.1 % 4294967296).toNat)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd)
    (fun bytes => .int (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat bytes)))
    (fun b => .int (Int32.ofBitVec (BitVec.ofNat 32
      (SpecAMQP.Ref.signedOctet b % 4294967296).toNat)))
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (signedOctet_int32 b).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `smalllong` row (`0x55`).** The same one-octet form at `long`, with the eight-octet sign
extension. -/
theorem arm_0x55 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x55, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x55, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x55 : UInt8).toNat = .fixed 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x55 : UInt8) =
      .ok ⟨85, some "smalllong", SpecAMQP.Generated.Oasis.Category.fixed, 1, "long",
        "8-bit two's-complement integer"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 1 d >>= fun p =>
        .ok (.long (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeU8 d' >>= fun p =>
        .ok (.long (Int64.ofBitVec (BitVec.ofNat 64
          (SpecAMQP.Ref.signedOctet p.1 % 18446744073709551616).toNat)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeU8Nat d d' hd)
    (fun bytes => .long (SpecAMQP.Spec.Codec.signedOfOctets 1 (payloadNat bytes)))
    (fun b => .long (Int64.ofBitVec (BitVec.ofNat 64
      (SpecAMQP.Ref.signedOctet b % 18446744073709551616).toNat)))
    (fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (signedOctet_int64 b).symm)
    hS hR (spec_takeU8_data hs)

/-- **The `short` row (`0x61`).** Two octets as a signed sixteen-bit integer: the same fold as the
unsigned row, and the same value in two spellings. -/
theorem arm_0x61 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x61, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x61, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x61 : UInt8).toNat = .fixed 2 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x61 : UInt8) =
      .ok ⟨97, none, SpecAMQP.Generated.Oasis.Category.fixed, 2, "short",
        "16-bit two's-complement integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 2 d >>= fun p =>
        .ok (.short (SpecAMQP.Spec.Codec.signedOfOctets 2 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 2 d' >>= fun p =>
        .ok (.short (Int16.ofBitVec (BitVec.ofNat 16 p.1)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 2 d d' hd)
    (fun bytes => .short (SpecAMQP.Spec.Codec.signedOfOctets 2 (payloadNat bytes)))
    (fun n => .short (Int16.ofBitVec (BitVec.ofNat 16 n)))
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 16 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_16 b hlt)
    hS hR (spec_takeU8_data hs)

/-- **The `int` row (`0x71`).** The same at four octets. -/
theorem arm_0x71 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x71, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x71, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x71 : UInt8).toNat = .fixed 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x71 : UInt8) =
      .ok ⟨113, none, SpecAMQP.Generated.Oasis.Category.fixed, 4, "int",
        "32-bit two's-complement integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 4 d >>= fun p =>
        .ok (.int (SpecAMQP.Spec.Codec.signedOfOctets 4 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 4 d' >>= fun p =>
        .ok (.int (Int32.ofBitVec (BitVec.ofNat 32 p.1)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 4 d d' hd)
    (fun bytes => .int (SpecAMQP.Spec.Codec.signedOfOctets 4 (payloadNat bytes)))
    (fun n => .int (Int32.ofBitVec (BitVec.ofNat 32 n)))
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 32 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_32 b hlt)
    hS hR (spec_takeU8_data hs)

/-- **The `long` row (`0x81`).** The same at eight octets. -/
theorem arm_0x81 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x81, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x81, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x81 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x81 : UInt8) =
      .ok ⟨129, none, SpecAMQP.Generated.Oasis.Category.fixed, 8, "long",
        "64-bit two's-complement integer in network byte order"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p =>
        .ok (.long (SpecAMQP.Spec.Codec.signedOfOctets 8 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 8 d' >>= fun p =>
        .ok (.long (Int64.ofBitVec (BitVec.ofNat 64 p.1)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 8 d d' hd)
    (fun bytes => .long (SpecAMQP.Spec.Codec.signedOfOctets 8 (payloadNat bytes)))
    (fun n => .long (Int64.ofBitVec (BitVec.ofNat 64 n)))
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 64 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_64 b hlt)
    hS hR (spec_takeU8_data hs)

/-- **The `timestamp` row (`0x83`).** The same eight octets read as a signed count of milliseconds:
the row's only content beyond `long` is which type name the two artefacts give the value. -/
theorem arm_0x83 (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (c' : SpecAMQP.Ref.Cursor)
    (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor) (hd : CursorAgrees d d')
    (_hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0x83, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0x83, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hclass : SpecAMQP.Spec.Value.classify (0x83 : UInt8).toNat = .fixed 8 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0x83 : UInt8) =
      .ok ⟨131, some "ms64", SpecAMQP.Generated.Oasis.Category.fixed, 8, "timestamp",
        "64-bit two's-complement integer representing milliseconds since the unix epoch"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.takeBytes 8 d >>= fun p =>
        .ok (.timestamp (SpecAMQP.Spec.Codec.signedOfOctets 8 (payloadNat p.1)), p.2) := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
    simp only [SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rfl
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' =
      SpecAMQP.Ref.takeBeU 8 d' >>= fun p =>
        .ok (.timestamp (Int64.ofBitVec (BitVec.ofNat 64 p.1)), p.2) := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  exact reader_of_step (stepAgreesAll_takeBeNat 8 d d' hd)
    (fun bytes => .timestamp (SpecAMQP.Spec.Codec.signedOfOctets 8 (payloadNat bytes)))
    (fun n => .timestamp (Int64.ofBitVec (BitVec.ofNat 64 n)))
    (fun a b hrel f hf => by
      have hlt : b < 2 ^ 64 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_64 b hlt)
    hS hR (spec_takeU8_data hs)

/-! ## What the induction carries, and why it is not the law itself

The compound and array rows read *below* the fuel their own value was read at: a `list8` opened by
`readValue (fuel + 1)` reads its items at `readValue (fuel - 1)`, two levels down, while a described
value reads its descriptor and its value at `readValue fuel`, one level down. So a step lemma cannot
rest on `WireAgrees fuel` alone — it needs the agreement at every fuel beneath it — and this is that
obligation, named once rather than spelled out at every branch:

`WireAgreesUpTo n` is `WireAgrees` at every fuel up to `n`. It is *not* a strengthening of the law a
contract needs; it is the induction's own invariant, and `wireLayer_all` below ends by reading the
top of it off at `n = n`. -/
def WireAgreesUpTo (n : Nat) : Prop := ∀ k, k ≤ n → WireAgrees k

/-- The invariant at a lower fuel, which is what every descent inside a branch needs. -/
theorem wireAgreesUpTo_mono {m n : Nat} (h : WireAgreesUpTo n) (hmn : m ≤ n) : WireAgreesUpTo m :=
  fun k hk => h k (by omega)

/-- The invariant at its own fuel. -/
theorem wireAgreesUpTo_self {n : Nat} (h : WireAgreesUpTo n) : WireAgrees n := h n (le_refl n)

/-! ## An octet the declared surface does not assign

The reference dispatches on the constructor octet as a literal, so its own arms cover forty of the
256 and its catch-all covers the rest; the specification dispatches on `classify` and the generated
table, so an octet outside those forty reaches `declInRange`, which refuses it by name. What the
catch-all needs is that "outside the reference's forty" and "the declared surface assigns no row" are
the same set, and the two artefacts' own tests are the cheapest way to say so: `assignedConstructor`
is the reference's own forty-literal test, and the sweep below checks the generated table against it
for every octet there is, by ordinary evaluation over the 256 of them. -/

set_option maxRecDepth 10000 in
/-- **The declared surface and the reference's constructor test assign the same octets.** One finite
evaluation over all 256 octets, with the table's own `find?` asked about each; the reference's test is
asked of `UInt8.ofNat n`, which *is* `n` as an octet for every `n < 256`, so the sweep covers every
octet there is. -/
theorem no_encoding_of_unassigned_constructor :
    (List.range 256).all (fun n =>
      (SpecAMQP.Generated.Oasis.encodingOf n).isNone
        || SpecAMQP.Ref.assignedConstructor (UInt8.ofNat n)) = true := by
  decide

/-- The sweep, read off at one octet: an octet the reference does not accept has no row in the
declared surface. -/
theorem encodingOf_none_of_not_assigned {code : UInt8}
    (h : SpecAMQP.Ref.assignedConstructor code = false) :
    SpecAMQP.Generated.Oasis.encodingOf code.toNat = none := by
  have hmem := List.all_eq_true.mp no_encoding_of_unassigned_constructor code.toNat
    (List.mem_range.mpr code.toNat_lt)
  rw [Bool.or_eq_true] at hmem
  rcases hmem with hnone | hassigned
  · exact Option.isNone_iff_eq_none.mp hnone
  · rw [show UInt8.ofNat code.toNat = code from by simp [UInt8.ofNat_toNat]] at hassigned
    rw [h] at hassigned
    exact absurd hassigned (by simp)

/-- **The reference refuses an octet it does not accept, naming it `unassigned`.** The reference's own
dispatch has one arm per assigned octet and one catch-all, so the catch-all is exactly the
`assignedConstructor` test failing — which is what makes this provable from the test alone. -/
theorem ref_readValue_unassigned (fuel : Nat) (c' : SpecAMQP.Ref.Cursor) (code : UInt8)
    (d' : SpecAMQP.Ref.Cursor) (hr : SpecAMQP.Ref.takeU8 c' = .ok (code, d'))
    (hass : SpecAMQP.Ref.assignedConstructor code = false) :
    SpecAMQP.Ref.readValue (fuel + 1) c' = .error (.unassigned code) := by
  simp only [SpecAMQP.Ref.readValue]
  rw [hr, except_bind_ok]
  dsimp only
  split
  all_goals first
    | rfl
    | (simp only [SpecAMQP.Ref.assignedConstructor] at hass; exact absurd hass (by simp))

set_option maxRecDepth 10000 in
/-- The grammar's classification, checked against the octet it classifies: `%x00` is the only
descriptor prefix, so every *other* octet is refused by the specification's own dispatch rather than
read as one. -/
theorem classify_sweep :
    (List.range 255).all (fun k =>
      decide (SpecAMQP.Spec.Value.classify (k + 1) ≠ .descriptor)) = true := by
  decide

/-- A non-zero octet is never the descriptor prefix. -/
theorem classify_ne_descriptor_of_ne_zero (n : Nat) (hn : n < 256) (h : n ≠ 0) :
    SpecAMQP.Spec.Value.classify n ≠ SpecAMQP.Spec.Value.Constructor.descriptor := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact of_decide_eq_true
    (List.all_eq_true.mp classify_sweep k (List.mem_range.mpr (by omega)))

/-- **The declared surface's range check, in the shape a refusal needs.** A row the table does not
hold is refused with the class `unassigned`, whatever the range the octet's classification gave it. -/
theorem declInRange_of_none {code : UInt8} {cat : SpecAMQP.Generated.Oasis.Category} {w : Nat}
    (h : SpecAMQP.Generated.Oasis.encodingOf code.toNat = none) :
    ∃ r : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.declInRange code cat w = .error r ∧ r.reasonClass = "unassigned" := by
  unfold SpecAMQP.Spec.Codec.declInRange
  rw [h]
  exact ⟨_, rfl, rfl⟩

/-- The declared surface's lookup refuses an octet it has no row for, in the same words. The
descriptor prefix and the reserved octets are refusals here too, so this needs no hypothesis beyond
the missing row. -/
theorem dataDecl_of_unassigned (code : UInt8)
    (hnone : SpecAMQP.Generated.Oasis.encodingOf code.toNat = none) :
    ∃ r : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.dataDecl code = .error r ∧ r.reasonClass = "unassigned" := by
  unfold SpecAMQP.Spec.Codec.dataDecl
  split
  all_goals first
    | exact ⟨_, rfl, rfl⟩
    | exact declInRange_of_none hnone

/-- **The specification refuses an octet the declared surface does not assign, naming it
`unassigned`.** The one place this needs more than the missing row is the descriptor prefix: `%x00`
is unassigned in the table and would send the reader down the described-value arm, so the octet has to
be excluded by name — which is what the reference's own test already does, since it counts `%x00`
among the constructors it accepts. -/
theorem spec_readValue_unassigned (fuel : Nat) (c : SpecAMQP.Spec.Codec.Cursor) (code : UInt8)
    (d : SpecAMQP.Spec.Codec.Cursor)
    (hu : SpecAMQP.Spec.Codec.takeU8 c = .ok (code, d))
    (hnone : SpecAMQP.Generated.Oasis.encodingOf code.toNat = none)
    (hne : code ≠ 0x00) :
    ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.readValue (fuel + 1) c = .error refusal ∧
      refusal.reasonClass = "unassigned" := by
  obtain ⟨r, hd, hc⟩ := dataDecl_of_unassigned code hnone
  have hne0 : code.toNat ≠ 0 := fun h => hne (UInt8.toNat_inj.mp (by simpa using h))
  have hcl : SpecAMQP.Spec.Value.classify code.toNat ≠ .descriptor :=
    classify_ne_descriptor_of_ne_zero code.toNat code.toNat_lt hne0
  simp only [SpecAMQP.Spec.Codec.readValue]
  rw [hu, except_bind_ok]
  split
  all_goals first
    | exact absurd ‹SpecAMQP.Spec.Value.classify code.toNat = .descriptor› hcl
    | exact ⟨_, rfl, rfl⟩
    | exact ⟨r, by dsimp only; rw [hd]; simp only [except_bind_error], hc⟩

/-! ## The element constructor: two tests, one set of octets

An array's element constructor is checked by both readers *after* the count and the limit and *before*
any element is read: the reference asks its own `assignedConstructor`, and the specification asks
`elementDecl?`, whose answer is the declaration the element's data is read under (or `none` for the
descriptor prefix). The two tests accept the same octets, which is one finite evaluation over the 256
of them — `elementDecl?` is asked of `UInt8.ofNat n`, which is `n` as an octet for every `n < 256`. -/

set_option maxRecDepth 10000 in
/-- **The two element-constructor tests accept the same octets.** -/
theorem elementDecl?_sweep :
    (List.range 256).all (fun n =>
      (SpecAMQP.Spec.Codec.elementDecl? (UInt8.ofNat n)).toOption.isSome
        == SpecAMQP.Ref.assignedConstructor (UInt8.ofNat n)) = true := by
  decide

/-- The sweep as an equation at one octet. -/
theorem elementDecl?_isSome (ctor : UInt8) :
    (SpecAMQP.Spec.Codec.elementDecl? ctor).toOption.isSome =
      SpecAMQP.Ref.assignedConstructor ctor := by
  have hall := List.all_eq_true.mp elementDecl?_sweep ctor.toNat
    (List.mem_range.mpr ctor.toNat_lt)
  rwa [show UInt8.ofNat ctor.toNat = ctor from by simp [UInt8.ofNat_toNat], beq_iff_eq] at hall

/-- An octet the reference accepts as an element constructor is one the specification looks up
successfully. -/
theorem elementDecl?_of_assigned {ctor : UInt8}
    (h : SpecAMQP.Ref.assignedConstructor ctor = true) :
    ∃ ed : Option SpecAMQP.Generated.Oasis.EncodingDecl,
      SpecAMQP.Spec.Codec.elementDecl? ctor = .ok ed := by
  cases hed : SpecAMQP.Spec.Codec.elementDecl? ctor with
  | ok ed => exact ⟨ed, rfl⟩
  | error e =>
    have his := elementDecl?_isSome ctor
    rw [hed] at his
    simp only [Except.toOption, Option.isSome] at his
    rw [h] at his
    exact absurd his (by simp)

/-- **An octet the reference refuses as an element constructor is refused by name.** The specification
has two more refusal sites than the reference here — the reserved range and the range check — but both
name `unassigned`, and the octet below `%x40` that the reference's test also rejects cannot reach the
descriptor-prefix arm, since `elementDecl?` handles `%x00` before it classifies anything. -/
theorem elementDecl?_refusal {ctor : UInt8}
    (h : SpecAMQP.Ref.assignedConstructor ctor = false) :
    ∃ r : SpecAMQP.Spec.Codec.Refusal,
      SpecAMQP.Spec.Codec.elementDecl? ctor = .error r ∧ r.reasonClass = "unassigned" := by
  have hnone := encodingOf_none_of_not_assigned h
  have hne : ctor.toNat ≠ 0 := by
    intro hz
    have hz' : ctor = 0x00 := by
      have : ctor.toNat = (0x00 : UInt8).toNat := by simpa using hz
      exact UInt8.toNat_inj.mp this
    rw [hz'] at h
    exact absurd h (by decide)
  have hcl : SpecAMQP.Spec.Value.classify ctor.toNat ≠ .descriptor :=
    classify_ne_descriptor_of_ne_zero ctor.toNat ctor.toNat_lt hne
  unfold SpecAMQP.Spec.Codec.elementDecl?
  rw [if_neg hne]
  split
  all_goals first
    | exact absurd ‹SpecAMQP.Spec.Value.classify ctor.toNat = .descriptor› hcl
    | exact ⟨_, rfl, rfl⟩
    | (obtain ⟨r, hr, hc⟩ := declInRange_of_none (cat := .fixed) hnone
       exact ⟨r, by rw [hr]; simp only [except_map_error], hc⟩)
    | (obtain ⟨r, hr, hc⟩ := declInRange_of_none (cat := .variable) hnone
       exact ⟨r, by rw [hr]; simp only [except_map_error], hc⟩)
    | (obtain ⟨r, hr, hc⟩ := declInRange_of_none (cat := .compound) hnone
       exact ⟨r, by rw [hr]; simp only [except_map_error], hc⟩)
    | (obtain ⟨r, hr, hc⟩ := declInRange_of_none (cat := .array) hnone
       exact ⟨r, by rw [hr]; simp only [except_map_error], hc⟩)

/-! ## The reference's own reads, as the arithmetic a loop's bound needs

Every bound in this development is a statement about the octets left at a cursor, and the cursor
arithmetic that carries one bound to the next read is the readers' own advances. The specification's
are in `Proofs.ReadProgress`; these are the reference's, stated the same way — where the read left the
cursor, on which buffer, and what the read therefore required of the buffer. The requirement is what a
*small* fuel is excluded by: a header that was read says the buffer held its octets. -/

/-- **The reference's payload read.** -/
theorem ref_takeBytes_of_ok {n : Nat} {c c' : SpecAMQP.Ref.Cursor}
    {bytes : SpecAMQP.Harness.Octets} (h : SpecAMQP.Ref.takeBytes n c = .ok (bytes, c')) :
    c'.data = c.data ∧ c'.pos = c.pos + n ∧ c.pos + n ≤ c.data.size := by
  by_cases hn : c.pos + n ≤ c.data.size
  · simp only [SpecAMQP.Ref.takeBytes, if_pos hn, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hcur⟩ := h
    subst hcur
    exact ⟨rfl, rfl, hn⟩
  · simp only [SpecAMQP.Ref.takeBytes, if_neg hn] at h
    exact absurd h (by simp)

/-- **The reference's octet read.** -/
theorem ref_takeU8_of_ok {c c' : SpecAMQP.Ref.Cursor} {b : UInt8}
    (h : SpecAMQP.Ref.takeU8 c = .ok (b, c')) :
    c'.data = c.data ∧ c'.pos = c.pos + 1 ∧ c.pos + 1 ≤ c.data.size := by
  by_cases hn : c.pos < c.data.size
  · simp only [SpecAMQP.Ref.takeU8, dif_pos hn, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hcur⟩ := h
    subst hcur
    exact ⟨rfl, rfl, hn⟩
  · simp only [SpecAMQP.Ref.takeU8, dif_neg hn] at h
    exact absurd h (by simp)

/-- **The reference's big-endian field read.** -/
theorem ref_takeBeU_of_ok {w : Nat} {c c' : SpecAMQP.Ref.Cursor} {m : Nat}
    (h : SpecAMQP.Ref.takeBeU w c = .ok (m, c')) :
    c'.data = c.data ∧ c'.pos = c.pos + w ∧ c.pos + w ≤ c.data.size := by
  unfold SpecAMQP.Ref.takeBeU at h
  obtain ⟨⟨bytes, d⟩, hb, h⟩ := exists_of_bind_ok h
  dsimp only at h
  rw [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hcur⟩ := h
  subst hcur
  exact ref_takeBytes_of_ok hb

/-- The specification's octet read leaves its cursor one further on, which is the arithmetic its own
branches need. Stated here because `Proofs.ReadProgress` gives the *inequality* the fuel law needs and
the loops need the advance itself. -/
theorem spec_takeU8_pos {c d : SpecAMQP.Spec.Codec.Cursor} {b : UInt8}
    (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (b, d)) : d.pos = c.pos + 1 := by
  by_cases hn : c.pos < c.data.size
  · simp only [SpecAMQP.Spec.Codec.takeU8, dif_pos hn, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  · simp only [SpecAMQP.Spec.Codec.takeU8, dif_neg hn] at h
    exact absurd h (by simp)

/-! ## A map's pairs, from the items it read

The two artefacts pair a map's items the same way — consecutive items, key then value, in wire order —
but they say it differently: the reference's `pairUp` is the partial function that *refuses* an odd
tail (`none`), the specification's drops a dangling item rather than refusing it. The parity check
ahead of the items read is what makes the two agree, so the bridge below is stated with the reference's
`pairUp` succeeding as a hypothesis; the specification's list is then the same pairing, and the
hypothesis is exactly what the reference's own reader had established. -/

/-- Two lists that agree are both empty or both consed; the mismatched shapes are the relation's own
`False`, so they are the two sides of the induction's base. -/
theorem bodiesAgreeList_cons {x : SpecAMQP.Spec.Codec.Value}
    {xs : List SpecAMQP.Spec.Codec.Value} {y : SpecAMQP.Ref.Value} {ys : List SpecAMQP.Ref.Value}
    (h : BodiesAgreeList (x :: xs) (y :: ys)) : BodiesAgree x y ∧ BodiesAgreeList xs ys := by
  simpa only [BodiesAgreeList] using h

/-- An agreeing list is empty on the right when it is empty on the left. -/
theorem bodiesAgreeList_nil_left {ys : List SpecAMQP.Ref.Value}
    (h : BodiesAgreeList [] ys) : ys = [] := by
  cases ys with
  | nil => rfl
  | cons y ys => simp only [BodiesAgreeList] at h

/-- ... and empty on the left when it is empty on the right. -/
theorem bodiesAgreeList_nil_right {xs : List SpecAMQP.Spec.Codec.Value}
    (h : BodiesAgreeList xs []) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [BodiesAgreeList] at h

/-- **The two artefacts' pairings agree.** Inducting on the *pairing* rather than on the items: the
reference's `pairUp` is the partial function, so its success is what says how many items there were
and how they were grouped, and each pair of the reference's is a pair of the specification's, key
against key and value against value. Inducting on the grouping rather than on the items is what keeps
the induction hypothesis available at the list the recursion actually reaches — the items come two at
a time, so the tail the recursion reaches is two shorter than the tail the item induction would
reach. The shapes where the two disagree about a dangling item are the ones the reference's success
excludes, and each is closed as the contradiction it is. -/
theorem pairUp_agrees (zs : List (SpecAMQP.Ref.Value × SpecAMQP.Ref.Value)) :
    ∀ (xs : List SpecAMQP.Spec.Codec.Value) (ys : List SpecAMQP.Ref.Value),
      BodiesAgreeList xs ys → SpecAMQP.Ref.pairUp ys = some zs →
      BodiesAgreePairs (SpecAMQP.Spec.Codec.pairUp xs) zs := by
  induction zs with
  | nil =>
    intro xs ys h hz
    cases ys with
    | nil =>
      rw [bodiesAgreeList_nil_right h]
      simp only [SpecAMQP.Spec.Codec.pairUp, BodiesAgreePairs]
    | cons y ys =>
      cases ys with
      | nil =>
        simp only [SpecAMQP.Ref.pairUp] at hz
        exact absurd hz (by intro hh; cases hh)
      | cons y' ys' =>
        cases hp : SpecAMQP.Ref.pairUp ys' with
        | none =>
          simp only [SpecAMQP.Ref.pairUp, hp, Option.map_none] at hz
          exact absurd hz (by intro hh; cases hh)
        | some zs'' =>
          simp only [SpecAMQP.Ref.pairUp, hp, Option.map_some] at hz
          exact absurd hz (by intro hh; cases hh)
  | cons z zs' ih =>
    cases z with
    | mk z₁ z₂ =>
      intro xs ys h hz
      cases ys with
      | nil =>
        simp only [SpecAMQP.Ref.pairUp, Option.some.injEq] at hz
        exact absurd hz (by intro hh; cases hh)
      | cons y ys =>
        cases ys with
        | nil =>
          simp only [SpecAMQP.Ref.pairUp] at hz
          exact absurd hz (by intro hh; cases hh)
        | cons y' ys' =>
          cases hp : SpecAMQP.Ref.pairUp ys' with
          | none =>
            simp only [SpecAMQP.Ref.pairUp, hp, Option.map_none] at hz
            exact absurd hz (by intro hh; cases hh)
          | some zs'' =>
            simp only [SpecAMQP.Ref.pairUp, hp, Option.map_some, Option.some.injEq] at hz
            injection hz with hhead htailz
            injection hhead with h1 h2
            subst h1
            subst h2
            subst htailz
            cases xs with
            | nil => simp only [BodiesAgreeList] at h
            | cons x xs₁ =>
              obtain ⟨hxy, htail⟩ := bodiesAgreeList_cons h
              cases xs₁ with
              | nil => simp only [BodiesAgreeList] at htail
              | cons x' xs' =>
                obtain ⟨hx', hrest⟩ := bodiesAgreeList_cons htail
                simp only [SpecAMQP.Spec.Codec.pairUp]
                unfold BodiesAgreePairs
                exact ⟨hxy, hx', ih xs' ys' hrest hp⟩

/-! ## The map key comparison, and the agreement it owes

The map reader's duplicate-key rule asks each artefact to compare two key values, and the claim the
differential makes about a refused map is that both readings refuse it *in the same class*. That is a
claim about what the comparison answers — the reference's `keysRepeat` answers `true` exactly where
the specification's does — and not merely about where the question is asked.

Both artefacts therefore carry the comparison as three structurally recursive definitions
(`SpecAMQP.Spec.Codec.sameValue` and `SpecAMQP.Ref.sameValue`, with their item-list and pair-list
forms) rather than as a derived `BEq` instance, which the kernel cannot unfold: an opaque instance
answers the question at runtime and refuses to answer it to any proof, which is exactly what the
duplicate case needs. These lemmas are what the written-out comparison buys, and
`readCompound_map_body` spends it.

`BodiesAgree` is the relation between the two representations, so it also relates the comparisons:
`value_beq_agrees` is that statement, `list_beq_agrees` and `pairs_beq_agrees` are its item-list and
pair-list forms, and they are mutually recursive because a value's items are values.

Two things keep the proof out of the pairing analysis a second time — the analysis that pairs two
reference values up, which is what an agreement between two *readings* needs and what a comparison
between two *shapes* does not. `valueTag_agrees` says a paired body is paired at the same tag, so a
goal whose two specification values are of different constructors is settled by the two artefacts'
shapes alone (`sameValue_eq_false_of_tag_ne`, `refValue_eq_false_of_refTag_ne`) and never looks at
the reference's pairing at all. Only where the two readings share a constructor are values paired up
against each other, and there the fields' own relations carry the case: the projections the carriers
publish (`toNat_inj`, `toInt_inj`, `Array.isEqv_toList`) close the scalar and opaque shapes in one
step, and the item and pair lists are the mutual lemmas. -/

/-- The constructor a value is, as a number: the first thing a comparison compares, and the
reason two values of different constructors answer `false` without either payload being consulted.
The two artefacts number the constructors identically — the number is this module's, not either
artefact's — so the same tag is a claim about the same shape. -/
def valueTag : SpecAMQP.Spec.Codec.Value → Nat
  | .null => 0
  | .boolean _ => 1
  | .ubyte _ => 2
  | .ushort _ => 3
  | .uint _ => 4
  | .ulong _ => 5
  | .byte _ => 6
  | .short _ => 7
  | .int _ => 8
  | .long _ => 9
  | .float _ => 10
  | .double _ => 11
  | .decimal32 _ => 12
  | .decimal64 _ => 13
  | .decimal128 _ => 14
  | .char _ => 15
  | .timestamp _ => 16
  | .uuid _ => 17
  | .binary _ => 18
  | .string _ => 19
  | .symbol _ => 20
  | .list _ => 21
  | .map _ => 22
  | .array _ _ => 23
  | .described _ _ => 24

/-- The reference's constructors under the same numbering: `valueTag`'s companion. -/
def refTag : SpecAMQP.Ref.Value → Nat
  | .null => 0
  | .boolean _ => 1
  | .ubyte _ => 2
  | .ushort _ => 3
  | .uint _ => 4
  | .ulong _ => 5
  | .byte _ => 6
  | .short _ => 7
  | .int _ => 8
  | .long _ => 9
  | .string _ => 19
  | .symbol _ => 20
  | .binary _ => 18
  | .char _ => 15
  | .timestamp _ => 16
  | .float _ => 10
  | .double _ => 11
  | .decimal32 _ => 12
  | .decimal64 _ => 13
  | .decimal128 _ => 14
  | .uuid _ => 17
  | .list _ => 21
  | .map _ => 22
  | .array _ _ => 23
  | .described _ _ => 24

/-- **A paired body is paired at the same tag.** The two numberings agree under `BodiesAgree`,
which is what lets a goal about two *different* constructors be settled without pairing the
reference's readings up a second time. -/
theorem valueTag_agrees {a : SpecAMQP.Spec.Codec.Value} {b : SpecAMQP.Ref.Value}
    (h : BodiesAgree a b) : valueTag a = refTag b := by
  cases a <;> cases b <;> simp only [BodiesAgree] at h <;> rfl

/-- Two values of different constructors are different values to the specification's comparison,
whatever their payloads. -/
theorem sameValue_eq_false_of_tag_ne {a a' : SpecAMQP.Spec.Codec.Value}
    (h : valueTag a ≠ valueTag a') : SpecAMQP.Spec.Codec.sameValue a a' = false := by
  cases a <;> cases a' <;> simp only [SpecAMQP.Spec.Codec.sameValue, valueTag] at h ⊢
  all_goals first | rfl | exact absurd rfl h

/-- ... and to the reference's, the same way. -/
theorem refValue_eq_false_of_refTag_ne {b b' : SpecAMQP.Ref.Value}
    (h : refTag b ≠ refTag b') : SpecAMQP.Ref.sameValue b b' = false := by
  cases b <;> cases b' <;> simp only [SpecAMQP.Ref.sameValue, refTag] at h ⊢
  all_goals first | rfl | exact absurd rfl h

-- The case analyses below walk a 25-constructor value type on both sides, and one `whnf` of the
-- well-founded comparison inside them is over the default budget; the budget is raised here so the
-- block reports about the comparison rather than about the elapsed heartbeats.
set_option maxHeartbeats 4000000 in
mutual

/-- **The two readings compare values the same way.** Values the frame layer's relation calls the
same value are the same value to each artefact's own comparison, constructor against constructor and
payload against payload. -/
theorem value_beq_agrees : ∀ (a a' : SpecAMQP.Spec.Codec.Value) (b b' : SpecAMQP.Ref.Value),
    BodiesAgree a b → BodiesAgree a' b' →
    SpecAMQP.Spec.Codec.sameValue a a' = SpecAMQP.Ref.sameValue b b'
  | a, a', b, b', h, h' => by
    cases a <;> cases b <;> simp only [BodiesAgree] at h
    all_goals (cases a' <;> first
      | -- `a'` is not the constructor the reference's reading paired with `a`, so it is not the
        -- constructor `b'` carries either: both comparisons answer `false` because the shapes differ.
        -- This arm reads no reference payload, which is why it needs no pairing of its own
        (rw [sameValue_eq_false_of_tag_ne (a := a) (a' := a') (by simp only [valueTag]; decide),
          refValue_eq_false_of_refTag_ne (b := b) (b' := b')
            (by
              intro hcon
              have hne : valueTag a ≠ valueTag a' := by simp only [valueTag]; decide
              exact hne ((valueTag_agrees h).trans (hcon.trans (valueTag_agrees h').symm)))])
      | (cases b' <;> simp only [BodiesAgree] at h' <;>
          simp only [SpecAMQP.Spec.Codec.sameValue, SpecAMQP.Ref.sameValue] <;>
          first
            | rfl
            -- the containers first: each is a case whose two parts are settled by the mutual lemma,
            -- and each of these steps fails outright on a body that is not that container
            | (exact list_beq_agrees _ _ _ _ h h')
            | (exact pairs_beq_agrees _ _ _ _ h h')
            -- an array: its constructor octet is the same octet on both sides once the relation is
            -- used as a rewrite rule, and its elements are the item list's own case
            | (rw [h.1, h'.1, list_beq_agrees _ _ _ _ h.2 h'.2]; done)
            -- a described body: both of its two parts are values
            | (rw [value_beq_agrees _ _ _ _ h.1 h'.1, value_beq_agrees _ _ _ _ h.2 h'.2]; done)
            -- a scalar, a `String` or an opaque payload: the field relations rewrite and both sides
            -- become the same comparison, which is the projection the carriers publish —
            -- `toNat_inj`/`toInt_inj` where a `Nat` or an `Int` meets a `UIntNN` or an `IntNN`
            | (simp only [h, h', BEq.beq, UInt8.toNat_inj, UInt16.toNat_inj, UInt32.toNat_inj,
                 UInt64.toNat_inj, Int8.toInt_inj, Int16.toInt_inj, Int32.toInt_inj,
                 Int64.toInt_inj]; done)
            -- a binary payload: the one shape where the two carriers are different containers —
            -- `Array UInt8` against `List UInt8` — so the octet list is what the two comparisons
            -- have in common, which is what `h` says the payloads are
            | (simp only [h.symm, h'.symm, BEq.beq, List.beq_eq_isEqv, Array.isEqv_toList]; done)))
termination_by a a' b b' => sizeOf a + sizeOf a' + sizeOf b + sizeOf b'

/-- **Item lists compare item by item**, in order: the value comparison's own form at a list. -/
theorem list_beq_agrees : ∀ (xs xs' : List SpecAMQP.Spec.Codec.Value)
    (ys ys' : List SpecAMQP.Ref.Value),
    BodiesAgreeList xs ys → BodiesAgreeList xs' ys' →
    SpecAMQP.Spec.Codec.sameValues xs xs' = SpecAMQP.Ref.sameValues ys ys'
  | xs, xs', ys, ys', h, h' => by
    cases xs <;> cases ys <;> simp only [BodiesAgreeList] at h
    all_goals (cases xs' <;> cases ys' <;> simp only [BodiesAgreeList] at h')
    all_goals simp only [SpecAMQP.Spec.Codec.sameValues, SpecAMQP.Ref.sameValues]
    all_goals (first
      | rfl
      | (rw [value_beq_agrees _ _ _ _ h.1 h'.1, list_beq_agrees _ _ _ _ h.2 h'.2]))
termination_by xs xs' ys ys' => sizeOf xs + sizeOf xs' + sizeOf ys + sizeOf ys'

/-- **Pair lists compare pair by pair**, key against key and value against value, in the order the
wire carried them: the value comparison's own form at a map's pairing. -/
theorem pairs_beq_agrees : ∀ (ps ps' : List (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Value))
    (qs qs' : List (SpecAMQP.Ref.Value × SpecAMQP.Ref.Value)),
    BodiesAgreePairs ps qs → BodiesAgreePairs ps' qs' →
    SpecAMQP.Spec.Codec.samePairs ps ps' = SpecAMQP.Ref.samePairs qs qs'
  -- The pairing relation and the comparison are both written on a pair-headed list, so a variable
  -- head leaves neither of them unfoldable and the pair has to be destructured. It is destructured
  -- in the clause patterns, not by a tactic, because this recursion is well-founded: a tactic
  -- `rcases` on one of the *parameters* leaves the pattern out of the termination goal, which then
  -- asks `sizeOf (tail) < sizeOf (parameter)` for a parameter nothing constrains - an obligation no
  -- tactic can close. With the pair in the clause pattern the obligation is `sizeOf` on a
  -- constructor's argument against `sizeOf` on the constructor (`List.cons.sizeOf_spec`,
  -- `Prod.mk.sizeOf_spec`), which arithmetic closes. The first four clauses are the cases where one
  -- of the four lists is empty: the relation makes one of the two hypotheses `False` there, or both
  -- comparisons answer `false`.
  | [], ps', qs, qs', h, h' => by
    cases ps' <;> cases qs <;> cases qs' <;>
      simp_all only [BodiesAgreePairs, SpecAMQP.Spec.Codec.samePairs, SpecAMQP.Ref.samePairs]
  | ps, [], qs, qs', h, h' => by
    cases ps <;> cases qs <;> cases qs' <;>
      simp_all only [BodiesAgreePairs, SpecAMQP.Spec.Codec.samePairs, SpecAMQP.Ref.samePairs]
  | ps, ps', [], qs', h, h' => by
    cases ps <;> cases ps' <;> cases qs' <;>
      simp_all only [BodiesAgreePairs, SpecAMQP.Spec.Codec.samePairs, SpecAMQP.Ref.samePairs]
  | ps, ps', qs, [], h, h' => by
    cases ps <;> cases ps' <;> cases qs <;>
      simp_all only [BodiesAgreePairs, SpecAMQP.Spec.Codec.samePairs, SpecAMQP.Ref.samePairs]
  | (k, v) :: ps, (k', v') :: ps', (l, w) :: qs, (l', w') :: qs', h, h' => by
    simp only [BodiesAgreePairs, SpecAMQP.Spec.Codec.samePairs, SpecAMQP.Ref.samePairs] at h h' ⊢
    rw [value_beq_agrees _ _ _ _ h.1 h'.1, value_beq_agrees _ _ _ _ h.2.1 h'.2.1,
        pairs_beq_agrees _ _ _ _ h.2.2 h'.2.2]
termination_by ps ps' qs qs' => sizeOf ps + sizeOf ps' + sizeOf qs + sizeOf qs'
end

/-- **A key occurs in a pair list exactly where its counterpart occurs in the other's.** The `any`
of a pair list is what `keysRepeat` asks of a map's keys, so this is the step that lets the two
artefacts' answers be compared: each pair's key is compared against the key in hand on its own side,
and `value_beq_agrees` says those two comparisons are the same comparison. -/
theorem any_key_agrees : ∀ (sp : List (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Value))
    (rp : List (SpecAMQP.Ref.Value × SpecAMQP.Ref.Value)),
    BodiesAgreePairs sp rp → ∀ (k : SpecAMQP.Spec.Codec.Value) (k' : SpecAMQP.Ref.Value),
      BodiesAgree k k' →
      (sp.any (fun p => p.1 == k)) = (rp.any (fun q => q.1 == k')) := by
  intro sp
  induction sp with
  | nil =>
    intro rp h k k' _
    cases rp with
    | nil => rfl
    | cons q rp => simp only [BodiesAgreePairs] at h
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    intro rp h k k' hk
    cases rp with
    | nil => simp only [BodiesAgreePairs] at h
    | cons q rp =>
      obtain ⟨a', b'⟩ := q
      simp only [BodiesAgreePairs] at h
      obtain ⟨ha, -, hrest⟩ := h
      simp only [List.any_cons]
      rw [show (a == k) = SpecAMQP.Spec.Codec.sameValue a k from rfl,
        show (a' == k') = SpecAMQP.Ref.sameValue a' k' from rfl,
        value_beq_agrees _ _ _ _ ha hk, ih rp hrest k k' hk]

/-- **A repeated key is a repeated key in both readings.** The rule Part 1 states of a map — "a map
in which there exist two identical key values is invalid" — is asked of each artefact's own key
comparison, and the two answers are the same answer. This is the lemma the duplicate case of
`readCompound_map_body` needs: the reference's refusal and the specification's are the same refusal
about the same map, and so they name the same class. -/
theorem keysRepeat_agrees : ∀ (sp : List (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Value))
    (rp : List (SpecAMQP.Ref.Value × SpecAMQP.Ref.Value)), BodiesAgreePairs sp rp →
    SpecAMQP.Spec.Codec.keysRepeat sp = SpecAMQP.Ref.keysRepeat rp := by
  intro sp
  induction sp with
  | nil =>
    intro rp h
    cases rp with
    | nil => rfl
    | cons q rp => simp only [BodiesAgreePairs] at h
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    intro rp h
    cases rp with
    | nil => simp only [BodiesAgreePairs] at h
    | cons q rp =>
      obtain ⟨a', b'⟩ := q
      simp only [BodiesAgreePairs] at h
      obtain ⟨ha, -, hrest⟩ := h
      simp only [SpecAMQP.Spec.Codec.keysRepeat, SpecAMQP.Ref.keysRepeat,
        any_key_agrees ps rp hrest a a' ha, ih rp hrest]

/-! ## The specification's array element, as a reader of its own

An array's elements are read by `readElementsLoop`, whose one element is a *decision* on the element
constructor's declaration rather than a reader: the descriptor prefix reads the element's own
descriptor and value, and an assigned row reads the data its category names. The loop's agreement has
to be an induction on the element count, and an induction on a count needs its step to be a *step* —
so the decision is named here as a reader, and `specElementData_loop` below is the equation that says
this is the reader's own read rather than a second reading of the same octets. -/
def specElementData (fuel : Nat) (elementDecl : Option SpecAMQP.Generated.Oasis.EncodingDecl)
    (c : SpecAMQP.Spec.Codec.Cursor) :
    Except SpecAMQP.Spec.Codec.Refusal
      (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Cursor) :=
  match elementDecl with
  | none => (do
      let (descriptor, c) ← SpecAMQP.Spec.Codec.readValue fuel c
      let (value, c) ← SpecAMQP.Spec.Codec.readValue fuel c
      return (.described descriptor value, c))
  | some decl =>
    match decl.category with
    | .fixed | .variable => SpecAMQP.Spec.Codec.readScalarData decl c
    | .compound => SpecAMQP.Spec.Codec.readCompound fuel decl c
    | .array => SpecAMQP.Spec.Codec.readArrayData fuel decl c

/-- **The element loop is its element read and then the loop.** An identity of the reader's own
definition, so a step of the count induction is the element read and the induction hypothesis. Proved
through the equation lemmas rather than by `rfl`: the specification's readers are one `mutual` block,
so their unfoldings are the compiler's equations and not `iota`. -/
theorem specElementData_loop (fuel : Nat) (elementDecl : Option SpecAMQP.Generated.Oasis.EncodingDecl)
    (count : Nat) (c : SpecAMQP.Spec.Codec.Cursor) :
    SpecAMQP.Spec.Codec.readElementsLoop fuel elementDecl (count + 1) c =
      specElementData fuel elementDecl c >>= fun p =>
        SpecAMQP.Spec.Codec.readElementsLoop fuel elementDecl count p.2 >>= fun q =>
          .ok (p.1 :: q.1, q.2) := by
  cases elementDecl <;> cases count <;>
    (unfold SpecAMQP.Spec.Codec.readElementsLoop specElementData
     dsimp only
     first
       | rfl
       | ((simp only [SpecAMQP.Spec.Codec.readElementsLoop, except_bind_ok, except_pure_ok]) <;> rfl))

/-- **An element read does not move its cursor backwards.** The loop's bound is a statement about the
octets left at the loop's *entry* cursor, and the induction hands it to the read of the next element:
what makes it still hold there is that the cursor only moves forward. The four readers the element
decision selects are the ones `Proofs.ReadProgress` already states this for, at the fuels this
decision uses them at. -/
theorem specElementData_progress (fuel : Nat)
    (elementDecl : Option SpecAMQP.Generated.Oasis.EncodingDecl) :
    ∀ (c : SpecAMQP.Spec.Codec.Cursor) (v : SpecAMQP.Spec.Codec.Value)
      (c₂ : SpecAMQP.Spec.Codec.Cursor),
      specElementData fuel elementDecl c = .ok (v, c₂) → c.pos ≤ c₂.pos := by
  intro c v c₂ h
  cases elementDecl with
  | none =>
    unfold specElementData at h
    obtain ⟨⟨d, c₁⟩, h1, h⟩ := exists_of_bind_ok h
    dsimp only at h
    obtain ⟨⟨val, c₃⟩, h2, h⟩ := exists_of_bind_ok h
    dsimp only at h
    rw [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
    have p1 := (readValue_progress fuel).1 c d c₁ h1
    have p2 := (readValue_progress fuel).1 c₁ val c₃ h2
    rw [← h.2]
    omega
  | some decl =>
    simp only [specElementData] at h
    split at h
    all_goals first
      | exact readScalarData_progress decl c v c₂ h
      | exact (readValue_progress fuel).2.2.1 decl c v c₂ h
      | exact (readValue_progress fuel).2.2.2.1 decl c v c₂ h

/-! ## An exhausted cursor, and what the container readers answer there

A compound's zero-fuel case is the one place the two readers' *shape* differs rather than their fuel:
the reference's `readCompound` matches on `fuel + 1` and refuses at zero, while the specification's has
no match of its own and refuses at zero by failing to read its first size field. The two refusals are
the same class, and these are the facts that say so without either reader having to name the prose it
refused with. -/

/-- **An exhausted cursor makes the specification's big-endian field read refuse as `truncated`.** The
refusal is the one a compound's or an array's header meets first, and its *class* is what the fuel
comparison reads. -/
theorem spec_takeBe_exhausted {w : Nat} (hw : 1 ≤ w) {c : SpecAMQP.Spec.Codec.Cursor}
    (h : c.data.size ≤ c.pos) :
    SpecAMQP.Spec.Codec.takeBe w c = .error (SpecAMQP.Spec.Codec.refusal "truncated"
      s!"{w} octet(s) needed at offset {c.pos} of {c.data.size}") := by
  unfold SpecAMQP.Spec.Codec.takeBe SpecAMQP.Spec.Codec.takeBytes
  rw [if_neg (by omega), except_bind_error]

/-- The same for a compound's own header. The fuel does not appear: a compound's items are only
reached behind two size fields, so a cursor with nothing left refuses before any of the reader's own
decisions. -/
theorem spec_readCompound_header {fuel : Nat} {decl : SpecAMQP.Generated.Oasis.EncodingDecl}
    (hwidth : 1 ≤ decl.width) (c : SpecAMQP.Spec.Codec.Cursor) (h : c.data.size ≤ c.pos) :
    SpecAMQP.Spec.Codec.readCompound fuel decl c = .error (SpecAMQP.Spec.Codec.refusal "truncated"
      s!"{decl.width} octet(s) needed at offset {c.pos} of {c.data.size}") := by
  unfold SpecAMQP.Spec.Codec.readCompound
  rw [spec_takeBe_exhausted hwidth h, except_bind_error]


/-! ## The specification's fuel is irrelevant above the octet bound

The tooling above is what the middle layer's compound and array rows need; this is the fact that lets
them be stated. The two artefacts spend fuel differently on a compound's header — the reference's
`readCompound` matches on `fuel + 1` and so spends a unit on its own header, while the specification's
`readValue` is where that unit was spent and its `readCompound` passes its own fuel through — so the
item loops sit one apart at one value-level fuel. What closes the gap is that a fuel unit is spent
only where a reader *descends*, and a descent consumes octets: at a cursor the fuel covers, one unit
more of fuel changes no answer. That is the family below, and it is what the loops are then put on one
footing with.

The statements carry three things beyond the answer. The agreement is an *agreement* and not an
equality, because a refusal's prose names the cursor it was refused at. Each reader's read is shown to
hand back the buffer it was given (`readRows_data`), because a loop's tail is read at a cursor the item
read advanced and the octet bound at the tail is expressible only through that buffer. And two clauses
carry guards that are conditions on the *statement*: the item loop refuses at fuel zero and accepts at
fuel one with a zero count, so its clause is stated from fuel one, and the compound and array readers
need a header wide enough to spend the octet that puts their item loops a level down, which is
`WideOption` and the two table sweeps. -/

open SpecAMQP.Spec.Codec
open SpecAMQP.Generated.Oasis (EncodingDecl)


/-- **A fixed-width row's read hands back its own buffer.** The value the row answers is built from
the payload, but the cursor it answers with is the one the payload read left, and that read took an
`extract` of the buffer rather than a copy of it. -/
theorem readFixed_data (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readFixed decl c = .ok (v, c')) : c'.data = c.data := by
  obtain ⟨payload, c₁, hb, hc⟩ := readFixed_ok decl c v c' h
  rw [← hc]
  exact spec_takeBytes_data hb

/-- **A variable-width row's read hands back its own buffer.** -/
theorem readVariable_data (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readVariable decl c = .ok (v, c')) : c'.data = c.data := by
  obtain ⟨length, c₁, payload, c₂, hbe, hbp, hc, -⟩ := readVariable_ok decl c v c' h
  rw [← hc, spec_takeBytes_data hbp, spec_takeBe_data hbe]

/-- **A scalar row's read hands back its own buffer**, whichever of the two categories it declares. -/
theorem readScalarData_data (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readScalarData decl c = .ok (v, c')) : c'.data = c.data := by
  unfold readScalarData at h
  split at h
  all_goals first
    | exact readFixed_data decl c v c' h
    | exact readVariable_data decl c v c' h
    | exact absurd h (by simp)

/-- **A fixed row's read lands inside its buffer.** The row's read is one payload read, and a payload
read leaves its cursor at the position it asked for plus the octets it asked for — so the landing
position is inside the buffer *because* the read asked for octets the buffer held. No hypothesis
about where the read started is needed: the fit is the read's own. -/
theorem readFixed_le (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readFixed decl c = .ok (v, c')) : c'.pos ≤ c'.data.size := by
  obtain ⟨payload, c₁, hb, hc⟩ := readFixed_ok decl c v c' h
  rw [← hc]
  exact spec_takeBytes_le hb

/-- The same for a variable row, whose read is the length field and then the payload; the text
families' decode is not a cursor step, so the payload read is still where the cursor stops. -/
theorem readVariable_le (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readVariable decl c = .ok (v, c')) : c'.pos ≤ c'.data.size := by
  obtain ⟨length, c₁, payload, c₂, hbe, hbp, hc, -⟩ := readVariable_ok decl c v c' h
  rw [← hc]
  exact spec_takeBytes_le hbp

/-- ... and so for a scalar row, whichever category it declares. -/
theorem readScalarData_le (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor)
    (h : readScalarData decl c = .ok (v, c')) : c'.pos ≤ c'.data.size := by
  unfold readScalarData at h
  split at h
  all_goals first
    | exact readFixed_le decl c v c' h
    | exact readVariable_le decl c v c' h
    | exact absurd h (by simp)

/-- **Every reader in the value cluster hands back the buffer it was given.**

The companion of `readValue_progress`, and the fact the fuel-irrelevance clauses need: a loop's tail
is read at the cursor the item or element read handed back, so the octet bound at the tail is
expressible only through the buffer the read left. The six clauses are one induction on the fuel, in
dependency order, because the `mutual` block cannot be separated: the compound reader reads its items
at its *own* fuel, and the element loop's element decision reads the value reader at its own fuel
too, so those two clauses are reached at the same level they are proved at. -/
theorem readRows_data : ∀ (fuel : Nat),
    (∀ (c : Cursor) (v : Value) (c' : Cursor), readValue fuel c = .ok (v, c') → c'.data = c.data) ∧
    (∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
      readItems fuel count c = .ok (items, c') → c'.data = c.data) ∧
    (∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
      readCompound fuel decl c = .ok (v, c') → c'.data = c.data) ∧
    (∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
      readArrayData fuel decl c = .ok (v, c') → c'.data = c.data) ∧
    (∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor) (items : List Value)
      (c' : Cursor), readElements fuel elementDecl count c = .ok (items, c') → c'.data = c.data) ∧
    (∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor) (items : List Value)
      (c' : Cursor), readElementsLoop fuel elementDecl count c = .ok (items, c') →
        c'.data = c.data) := by
  intro fuel
  induction fuel with
  | zero =>
    have hValue : ∀ (c : Cursor) (v : Value) (c' : Cursor),
        readValue 0 c = .ok (v, c') → c'.data = c.data := by
      intro c v c' h
      simp only [readValue] at h
      exact absurd h (by simp)
    have hItems : ∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
        readItems 0 count c = .ok (items, c') → c'.data = c.data := by
      intro count c items c' h
      simp only [readItems] at h
      exact absurd h (by simp)
    have hCompound : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readCompound 0 decl c = .ok (v, c') → c'.data = c.data := by
      intro decl c v c' h
      unfold readCompound at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have d1 := spec_takeBe_data h1
      have d2 := spec_takeBe_data h2
      split at h
      · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d3 := hItems count c₂ items c₃ h3
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2, d3, d2, d1]
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
          try dsimp only at h
          have d3 := hItems count c₂ items c₃ h3
          -- the duplicate-key check, which is a rule on the map's items and so runs before the
          -- declared size is compared with the octets measured
          split at h
          · exact absurd h (by simp)
          · split at h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2, d3, d2, d1]
            · exact absurd h (by simp)
      · exact absurd h (by simp)
    have hArrayData : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readArrayData 0 decl c = .ok (v, c') → c'.data = c.data := by
      intro decl c v c' h
      simp only [readArrayData] at h
      exact absurd h (by simp)
    have hElements : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElements 0 elementDecl count c = .ok (items, c') → c'.data = c.data := by
      intro elementDecl count c items c' h
      simp only [readElements] at h
      exact absurd h (by simp)
    have hElementData : ∀ (elementDecl : Option EncodingDecl) (c : Cursor) (v : Value)
        (c' : Cursor), specElementData 0 elementDecl c = .ok (v, c') → c'.data = c.data := by
      intro elementDecl c v c' h
      unfold specElementData at h
      split at h <;> try (split at h)
      all_goals first
        | (obtain ⟨⟨dsc, c₁⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           simp only [readValue] at h1
           exact absurd h1 (by simp))
        | exact readScalarData_data _ c v c' h
        | exact hCompound _ c v c' h
        | exact hArrayData _ c v c' h
    have hElementsLoop : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElementsLoop 0 elementDecl count c = .ok (items, c') → c'.data = c.data := by
      intro elementDecl count
      induction count with
      | zero =>
        intro c items c' h
        simp only [readElementsLoop] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
      | succ k ihk =>
        intro c items c' h
        rw [specElementData_loop] at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d1 := hElementData elementDecl c item c₁ h1
        have d2 := ihk c₁ rest c₂ h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2, d2, d1]
    exact ⟨hValue, hItems, hCompound, hArrayData, hElements, hElementsLoop⟩
  | succ n ih =>
    obtain ⟨ihValue, ihItems, ihCompound, ihArrayData, ihElements, ihElementsLoop⟩ := ih
    have hValue : ∀ (c : Cursor) (v : Value) (c' : Cursor),
        readValue (n + 1) c = .ok (v, c') → c'.data = c.data := by
      intro c v c' h
      unfold readValue at h
      obtain ⟨⟨code, c₁⟩, hu, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have d0 := spec_takeU8_data hu
      split at h
      all_goals first
        | (obtain ⟨⟨descriptor, c₂⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           obtain ⟨⟨inner, c₃⟩, h2, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           have d1 := ihValue c₁ descriptor c₂ h1
           have d2 := ihValue c₂ inner c₃ h2
           simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
           rw [← h.2, d2, d1, d0])
        | (obtain ⟨decl, hd, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           split at h <;> try (split at h)
           all_goals first
             | (have hh := readScalarData_data decl c₁ v c' h; rw [hh, d0])
             | (have hh := ihCompound decl c₁ v c' h; rw [hh, d0])
             | (have hh := ihArrayData decl c₁ v c' h; rw [hh, d0]))
        | exact absurd h (by simp)
    have hItems : ∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
        readItems (n + 1) count c = .ok (items, c') → c'.data = c.data := by
      intro count
      cases count with
      | zero =>
        intro c items c' h
        simp only [readItems] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
      | succ k =>
        intro c items c' h
        unfold readItems at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d1 := ihValue c item c₁ h1
        have d2 := ihItems k c₁ rest c₂ h2
        simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2, d2, d1]
    have hCompound : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readCompound (n + 1) decl c = .ok (v, c') → c'.data = c.data := by
      intro decl c v c' h
      unfold readCompound at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have d1 := spec_takeBe_data h1
      have d2 := spec_takeBe_data h2
      split at h
      · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d3 := hItems count c₂ items c₃ h3
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2, d3, d2, d1]
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
          try dsimp only at h
          have d3 := hItems count c₂ items c₃ h3
          -- the duplicate-key check, which is a rule on the map's items and so runs before the
          -- declared size is compared with the octets measured
          split at h
          · exact absurd h (by simp)
          · split at h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2, d3, d2, d1]
            · exact absurd h (by simp)
      · exact absurd h (by simp)
    have hArrayData : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readArrayData (n + 1) decl c = .ok (v, c') → c'.data = c.data := by
      intro decl c v c' h
      unfold readArrayData at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have d1 := spec_takeBe_data h1
      have d2 := spec_takeBe_data h2
      split at h
      · exact absurd h (by simp)
      · obtain ⟨⟨constructor, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d3 := spec_takeU8_data h3
        obtain ⟨elementDecl, h4, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨items, c₄⟩, h5, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d4 := ihElements elementDecl count c₃ items c₄ h5
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2, d4, d3, d2, d1]
        · exact absurd h (by simp)
    have hElements : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElements (n + 1) elementDecl count c = .ok (items, c') → c'.data = c.data := by
      intro elementDecl count c items c' h
      simp only [readElements] at h
      exact ihElementsLoop elementDecl count c items c' h
    have hElementData : ∀ (elementDecl : Option EncodingDecl) (c : Cursor) (v : Value)
        (c' : Cursor), specElementData (n + 1) elementDecl c = .ok (v, c') → c'.data = c.data := by
      intro elementDecl c v c' h
      unfold specElementData at h
      split at h <;> try (split at h)
      all_goals first
        | (obtain ⟨⟨dsc, c₁⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           obtain ⟨⟨val, c₂⟩, h2, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           have d1 := hValue c dsc c₁ h1
           have d2 := hValue c₁ val c₂ h2
           simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
           rw [← h.2, d2, d1])
        | exact readScalarData_data _ c v c' h
        | exact hCompound _ c v c' h
        | exact hArrayData _ c v c' h
    have hElementsLoop : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElementsLoop (n + 1) elementDecl count c = .ok (items, c') → c'.data = c.data := by
      intro elementDecl count
      induction count with
      | zero =>
        intro c items c' h
        simp only [readElementsLoop] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
      | succ k ihk =>
        intro c items c' h
        rw [specElementData_loop] at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have d1 := hElementData elementDecl c item c₁ h1
        have d2 := ihk c₁ rest c₂ h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2, d2, d1]
    exact ⟨hValue, hItems, hCompound, hArrayData, hElements, hElementsLoop⟩

/-- **Every reader in the value cluster keeps its cursor inside the buffer it was given.**

The third companion of `readValue_progress` and `readRows_data`, and the fact the array's element loop
needs. An element whose row declares no width reads *nothing* — through `takeBytes 0` — and that read
succeeds exactly when the cursor is inside the buffer, a position equal to the buffer's size counting
as inside: the elements of an array of zero-width values are read at exactly that cursor. So the
agreement of an array of such elements rests on the caller knowing where its cursor is.

The clauses carry the position as a hypothesis rather than asserting it, because it is not a fact about
a reader alone: a read's tail is inside the buffer *because* its start was. Every step either consumed
octets it had checked for or consumed none, and a read that starts outside the buffer refuses rather
than landing further outside. The six clauses are one induction on the fuel in the same dependency
order as `readRows_data`: the compound's items are read at the compound's own fuel and the element
decision at its own, so those clauses are reached at the level they are proved at, and the scalar rows
are free of the hypothesis altogether (`readScalarData_le`). -/
theorem readRows_le_size : ∀ (fuel : Nat),
    (∀ (c : Cursor) (v : Value) (c' : Cursor), readValue fuel c = .ok (v, c') →
      c.pos ≤ c.data.size → c'.pos ≤ c'.data.size) ∧
    (∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
      readItems fuel count c = .ok (items, c') → c.pos ≤ c.data.size → c'.pos ≤ c'.data.size) ∧
    (∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
      readCompound fuel decl c = .ok (v, c') → c.pos ≤ c.data.size → c'.pos ≤ c'.data.size) ∧
    (∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
      readArrayData fuel decl c = .ok (v, c') → c.pos ≤ c.data.size → c'.pos ≤ c'.data.size) ∧
    (∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor) (items : List Value)
      (c' : Cursor), readElements fuel elementDecl count c = .ok (items, c') →
        c.pos ≤ c.data.size → c'.pos ≤ c'.data.size) ∧
    (∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor) (items : List Value)
      (c' : Cursor), readElementsLoop fuel elementDecl count c = .ok (items, c') →
        c.pos ≤ c.data.size → c'.pos ≤ c'.data.size) := by
  intro fuel
  induction fuel with
  | zero =>
    have hValue : ∀ (c : Cursor) (v : Value) (c' : Cursor),
        readValue 0 c = .ok (v, c') → c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro c v c' h _
      simp only [readValue] at h
      exact absurd h (by simp)
    have hItems : ∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
        readItems 0 count c = .ok (items, c') → c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro count c items c' h _
      simp only [readItems] at h
      exact absurd h (by simp)
    have hCompound : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readCompound 0 decl c = .ok (v, c') → c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro decl c v c' h _
      unfold readCompound at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p2 := spec_takeBe_le h2
      split at h
      · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p3 := hItems count c₂ items c₃ h3 p2
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          exact p3
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
          try dsimp only at h
          have p3 := hItems count c₂ items c₃ h3 p2
          -- the duplicate-key check, which is a rule on the map's items and so runs before the
          -- declared size is compared with the octets measured
          split at h
          · exact absurd h (by simp)
          · split at h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]
              exact p3
            · exact absurd h (by simp)
      · exact absurd h (by simp)
    have hArrayData : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readArrayData 0 decl c = .ok (v, c') → c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro decl c v c' h _
      simp only [readArrayData] at h
      exact absurd h (by simp)
    have hElements : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElements 0 elementDecl count c = .ok (items, c') →
          c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro elementDecl count c items c' h _
      simp only [readElements] at h
      exact absurd h (by simp)
    have hElementData : ∀ (elementDecl : Option EncodingDecl) (c : Cursor) (v : Value)
        (c' : Cursor), specElementData 0 elementDecl c = .ok (v, c') →
          c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro elementDecl c v c' h hpos
      unfold specElementData at h
      split at h <;> try (split at h)
      all_goals first
        | (obtain ⟨⟨dsc, c₁⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           simp only [readValue] at h1
           exact absurd h1 (by simp))
        | exact readScalarData_le _ c v c' h
        | exact hCompound _ c v c' h hpos
        | exact hArrayData _ c v c' h hpos
    have hElementsLoop : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElementsLoop 0 elementDecl count c = .ok (items, c') →
          c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro elementDecl count
      induction count with
      | zero =>
        intro c items c' h hpos
        simp only [readElementsLoop] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact hpos
      | succ k ihk =>
        intro c items c' h hpos
        rw [specElementData_loop] at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p1 := hElementData elementDecl c item c₁ h1 hpos
        have p2 := ihk c₁ rest c₂ h2 p1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact p2
    exact ⟨hValue, hItems, hCompound, hArrayData, hElements, hElementsLoop⟩
  | succ n ih =>
    obtain ⟨ihValue, ihItems, ihCompound, ihArrayData, ihElements, ihElementsLoop⟩ := ih
    have hValue : ∀ (c : Cursor) (v : Value) (c' : Cursor),
        readValue (n + 1) c = .ok (v, c') → c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro c v c' h hpos
      unfold readValue at h
      obtain ⟨⟨code, c₁⟩, hu, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p0 := spec_takeU8_next_le hu
      split at h
      all_goals first
        | (obtain ⟨⟨descriptor, c₂⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           obtain ⟨⟨inner, c₃⟩, h2, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           have p1 := ihValue c₁ descriptor c₂ h1 p0
           have p2 := ihValue c₂ inner c₃ h2 p1
           simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
           rw [← h.2]
           exact p2)
        | (obtain ⟨decl, hd, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           split at h <;> try (split at h)
           all_goals first
             | exact readScalarData_le decl c₁ v c' h
             | (have hh := ihCompound decl c₁ v c' h p0; exact hh)
             | (have hh := ihArrayData decl c₁ v c' h p0; exact hh))
        | exact absurd h (by simp)
    have hItems : ∀ (count : Nat) (c : Cursor) (items : List Value) (c' : Cursor),
        readItems (n + 1) count c = .ok (items, c') → c.pos ≤ c.data.size →
          c'.pos ≤ c'.data.size := by
      intro count
      cases count with
      | zero =>
        intro c items c' h hpos
        simp only [readItems] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact hpos
      | succ k =>
        intro c items c' h hpos
        unfold readItems at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p1 := ihValue c item c₁ h1 hpos
        have p2 := ihItems k c₁ rest c₂ h2 p1
        simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact p2
    have hCompound : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readCompound (n + 1) decl c = .ok (v, c') → c.pos ≤ c.data.size →
          c'.pos ≤ c'.data.size := by
      intro decl c v c' h _
      unfold readCompound at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      have p2 := spec_takeBe_le h2
      split at h
      · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p3 := hItems count c₂ items c₃ h3 p2
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          exact p3
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · obtain ⟨⟨items, c₃⟩, h3, h⟩ := exists_of_bind_ok h
          try dsimp only at h
          have p3 := hItems count c₂ items c₃ h3 p2
          -- the duplicate-key check, which is a rule on the map's items and so runs before the
          -- declared size is compared with the octets measured
          split at h
          · exact absurd h (by simp)
          · split at h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]
              exact p3
            · exact absurd h (by simp)
      · exact absurd h (by simp)
    have hArrayData : ∀ (decl : EncodingDecl) (c : Cursor) (v : Value) (c' : Cursor),
        readArrayData (n + 1) decl c = .ok (v, c') → c.pos ≤ c.data.size →
          c'.pos ≤ c'.data.size := by
      intro decl c v c' h _
      unfold readArrayData at h
      obtain ⟨⟨size, c₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨count, c₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      split at h
      · exact absurd h (by simp)
      · obtain ⟨⟨constructor, c₃⟩, h3, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p3 := spec_takeU8_next_le h3
        obtain ⟨elementDecl, h4, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨items, c₄⟩, h5, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p4 := ihElements elementDecl count c₃ items c₄ h5 p3
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          exact p4
        · exact absurd h (by simp)
    have hElements : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElements (n + 1) elementDecl count c = .ok (items, c') →
          c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro elementDecl count c items c' h hpos
      simp only [readElements] at h
      exact ihElementsLoop elementDecl count c items c' h hpos
    have hElementData : ∀ (elementDecl : Option EncodingDecl) (c : Cursor) (v : Value)
        (c' : Cursor), specElementData (n + 1) elementDecl c = .ok (v, c') →
          c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro elementDecl c v c' h hpos
      unfold specElementData at h
      split at h <;> try (split at h)
      all_goals first
        | (obtain ⟨⟨dsc, c₁⟩, h1, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           obtain ⟨⟨val, c₂⟩, h2, h⟩ := exists_of_bind_ok h
           try dsimp only at h
           have p1 := hValue c dsc c₁ h1 hpos
           have p2 := hValue c₁ val c₂ h2 p1
           simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
           rw [← h.2]
           exact p2)
        | exact readScalarData_le _ c v c' h
        | exact hCompound _ c v c' h hpos
        | exact hArrayData _ c v c' h hpos
    have hElementsLoop : ∀ (elementDecl : Option EncodingDecl) (count : Nat) (c : Cursor)
        (items : List Value) (c' : Cursor),
        readElementsLoop (n + 1) elementDecl count c = .ok (items, c') →
          c.pos ≤ c.data.size → c'.pos ≤ c'.data.size := by
      intro elementDecl count
      induction count with
      | zero =>
        intro c items c' h hpos
        simp only [readElementsLoop] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact hpos
      | succ k ihk =>
        intro c items c' h hpos
        rw [specElementData_loop] at h
        obtain ⟨⟨item, c₁⟩, h1, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        obtain ⟨⟨rest, c₂⟩, h2, h⟩ := exists_of_bind_ok h
        try dsimp only at h
        have p1 := hElementData elementDecl c item c₁ h1 hpos
        have p2 := ihk c₁ rest c₂ h2 p1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact p2
    exact ⟨hValue, hItems, hCompound, hArrayData, hElements, hElementsLoop⟩

/-- **The element decision keeps its cursor inside the buffer**, which is the clause the element loop
needs: the next element is read where the last one stopped. -/
theorem specElementData_le {fuel : Nat} {elementDecl : Option EncodingDecl}
    {c : Cursor} {v : Value} {c' : Cursor}
    (h : specElementData fuel elementDecl c = .ok (v, c')) (hpos : c.pos ≤ c.data.size) :
    c'.pos ≤ c'.data.size := by
  cases elementDecl with
  | none =>
    unfold specElementData at h
    obtain ⟨⟨dsc, c₁⟩, h1, h⟩ := exists_of_bind_ok h
    try dsimp only at h
    obtain ⟨⟨val, c₂⟩, h2, h⟩ := exists_of_bind_ok h
    try dsimp only at h
    have p1 := (readRows_le_size fuel).1 c dsc c₁ h1 hpos
    have p2 := (readRows_le_size fuel).1 c₁ val c₂ h2 p1
    simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact p2
  | some decl =>
    simp only [specElementData] at h
    split at h
    all_goals first
      | exact readScalarData_le decl c v c' h
      | exact (readRows_le_size fuel).2.2.1 decl c v c' h hpos
      | exact (readRows_le_size fuel).2.2.2.1 decl c v c' h hpos

/-- **A value read spends its constructor octet before anything else**, so at a fuel at least one it
leaves the cursor strictly further on. The weak progress `readValue_progress` gives is not enough for
the item loop's tail: its bound is one octet tighter than the loop's, and only the octet the value
reader took makes up the difference. -/
theorem readValue_lt {f : Nat} {c : Cursor} {v : Value} {d : Cursor}
    (hf : 1 ≤ f) (h : readValue f c = .ok (v, d)) : c.pos < d.pos := by
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  unfold readValue at h
  obtain ⟨⟨code, c₁⟩, hu, h⟩ := exists_of_bind_ok h
  try dsimp only at h
  have h1 : c₁.pos = c.pos + 1 := spec_takeU8_pos hu
  split at h
  all_goals first
    | (obtain ⟨⟨descriptor, c₂⟩, h2, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       obtain ⟨⟨inner, c₃⟩, h3, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       have p1 := (readValue_progress k).1 c₁ descriptor c₂ h2
       have p2 := (readValue_progress k).1 c₂ inner c₃ h3
       simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
       rw [← h.2]
       omega)
    | (obtain ⟨decl, hd, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       split at h <;> try (split at h)
       all_goals first
         | (have p := readScalarData_progress decl c₁ v d h; omega)
         | (have p := (readValue_progress k).2.2.1 decl c₁ v d h; omega)
         | (have p := (readValue_progress k).2.2.2.1 decl c₁ v d h; omega))
    | exact absurd h (by simp)

/-- **The element decision hands back its own buffer.** Read off the cluster: the descriptor prefix's
two value reads and the compound and array rows are all cases of it, and the scalar rows are the
payload-free ones. -/
theorem specElementData_data (fuel : Nat) (ed : Option EncodingDecl) (c : Cursor) (v : Value)
    (c' : Cursor) (h : specElementData fuel ed c = .ok (v, c')) : c'.data = c.data := by
  unfold specElementData at h
  split at h <;> try (split at h)
  all_goals first
    | (obtain ⟨⟨dsc, c₁⟩, h1, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       obtain ⟨⟨val, c₂⟩, h2, h⟩ := exists_of_bind_ok h
       try dsimp only at h
       have d1 := (readRows_data fuel).1 c dsc c₁ h1
       have d2 := (readRows_data fuel).1 c₁ val c₂ h2
       simp only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] at h
       rw [← h.2, d2, d1])
    | exact readScalarData_data _ c v c' h
    | exact (readRows_data fuel).2.2.1 _ c v c' h
    | exact (readRows_data fuel).2.2.2.1 _ c v c' h


/-! ## The specification's fuel is irrelevant above the octet bound -/

/-- **The specification's two answers agree**: the same value and cursor, or refusals of the same
class. An *agreement* rather than an equality, because a refusal's prose names the cursor it was
refused at: `readValue 0 c` says the input ends before the value does, while the same read at a
larger fuel fails to take its constructor octet and says so. -/
def AnswerAgrees {α : Type} (x y : Except SpecAMQP.Spec.Codec.Refusal α) : Prop :=
  (∀ a, x = .ok a → y = .ok a) ∧
  (∀ r : SpecAMQP.Spec.Codec.Refusal, x = .error r →
    ∃ r' : SpecAMQP.Spec.Codec.Refusal, y = .error r' ∧ r.reasonClass = r'.reasonClass)

theorem answerAgrees_refl {α : Type} (x : Except SpecAMQP.Spec.Codec.Refusal α) :
    AnswerAgrees x x :=
  ⟨fun _ h => h, fun r h => ⟨r, h, rfl⟩⟩

/-- A shared continuation preserves the relation: everything a reader's caller does with the answer —
a size comparison, a pairing, a value constructor — is fuel-free. -/
theorem answerAgrees_bind {α β : Type} {x y : Except SpecAMQP.Spec.Codec.Refusal α}
    (h : AnswerAgrees x y) (k : α → Except SpecAMQP.Spec.Codec.Refusal β) :
    AnswerAgrees (x >>= k) (y >>= k) := by
  constructor
  · intro b hb
    obtain ⟨a, hx, hk⟩ := exists_of_bind_ok hb
    rw [h.1 a hx, except_bind_ok, hk]
  · intro r hr
    cases hx : x with
    | error e =>
      rw [hx, except_bind_error] at hr
      obtain ⟨r', hr', hcl⟩ := h.2 e hx
      exact ⟨r', by rw [hr', except_bind_error], by rw [← Except.error.inj hr]; exact hcl⟩
    | ok a =>
      rw [hx, except_bind_ok] at hr
      exact ⟨r, by rw [h.1 a hx, except_bind_ok, hr], rfl⟩

/-- The same, for a continuation that consumes the *cursor* as well as the value — which every
reader below a read does, since the read beneath starts where the read above left off. The
continuation's agreement is asked only of the pair the left read actually answers, because that is
the cursor the second read's octet bound has to be about. -/
theorem answerAgrees_bind₂ {α β : Type} {x y : Except SpecAMQP.Spec.Codec.Refusal (α × Cursor)}
    {F G : α × Cursor → Except SpecAMQP.Spec.Codec.Refusal (β × Cursor)}
    (h : AnswerAgrees x y)
    (hk : ∀ (p : α × Cursor), x = .ok p → AnswerAgrees (F p) (G p)) :
    AnswerAgrees (x >>= F) (y >>= G) := by
  constructor
  · intro b hb
    obtain ⟨p, hx, hk'⟩ := exists_of_bind_ok hb
    have hy := h.1 p hx
    rw [hy, except_bind_ok, (hk p hx).1 b hk']
  · intro r hr
    cases hx : x with
    | error e =>
      rw [hx, except_bind_error] at hr
      obtain ⟨r', hr', hcl⟩ := h.2 e hx
      exact ⟨r', by rw [hr', except_bind_error], by rw [← Except.error.inj hr]; exact hcl⟩
    | ok p =>
      rw [hx, except_bind_ok] at hr
      obtain ⟨r', hr', hcl⟩ := (hk p hx).2 r hr
      exact ⟨r', by rw [h.1 p hx, except_bind_ok, hr'], hcl⟩

/-- **A continuation under a read that refuses.** When the left read never accepts, the two
continuations are never reached and nothing about them matters — which is how the item loop's
zero-fuel tail is closed. -/
theorem answerAgrees_bind_error {α β : Type} {x y : Except SpecAMQP.Spec.Codec.Refusal α}
    (h : AnswerAgrees x y) (hx : ∀ a, x ≠ .ok a)
    (K : α → Except SpecAMQP.Spec.Codec.Refusal β) (K' : α → Except SpecAMQP.Spec.Codec.Refusal β) :
    AnswerAgrees (x >>= K) (y >>= K') := by
  constructor
  · intro b hb
    obtain ⟨a, ha, -⟩ := exists_of_bind_ok hb
    exact absurd ha (hx a)
  · intro r hr
    cases hxe : x with
    | error e =>
      rw [hxe, except_bind_error] at hr
      obtain ⟨r', hr', hcl⟩ := h.2 e hxe
      exact ⟨r', by rw [hr', except_bind_error], by rw [← Except.error.inj hr]; exact hcl⟩
    | ok a => exact absurd hxe (hx a)

/-- The class a failed octet step names: `truncated`, whatever the prose. -/
theorem spec_takeU8_error_class {c : Cursor} {r : SpecAMQP.Spec.Codec.Refusal}
    (h : takeU8 c = .error r) : r.reasonClass = "truncated" := by
  unfold takeU8 at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.error.injEq] at h
    rw [← h]
    rfl

/-- The same for a failed payload read. -/
theorem spec_takeBytes_error_class {n : Nat} {c : Cursor} {r : SpecAMQP.Spec.Codec.Refusal}
    (h : takeBytes n c = .error r) : r.reasonClass = "truncated" := by
  unfold takeBytes at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.error.injEq] at h
    rw [← h]
    rfl

/-- ... and for a failed big-endian field, which refuses through the payload read. -/
theorem spec_takeBe_error_class {w : Nat} {c : Cursor} {r : SpecAMQP.Spec.Codec.Refusal}
    (h : takeBe w c = .error r) : r.reasonClass = "truncated" := by
  unfold takeBe at h
  cases hb : takeBytes w c with
  | error e =>
    rw [hb, except_bind_error] at h
    rw [← Except.error.inj h]
    exact spec_takeBytes_error_class hb
  | ok p => rw [hb, except_bind_ok] at h; exact absurd h (by simp)

/-- **The budget a read hands to the read beneath it**: the same buffer, a cursor no further back. -/
theorem bound_tail_value {f : Nat} {c d : Cursor} {v : Value}
    (h : readValue f c = .ok (v, d)) (hb : c.data.size - c.pos ≤ f) :
    d.data.size - d.pos ≤ f := by
  have hd := (readRows_data f).1 c v d h
  have hp := (readValue_progress f).1 c v d h
  rw [hd]; omega

/-- **One octet of the budget is spent by the value reader's own constructor**, which is what makes the
item loop's tail bound one tighter than the loop's. -/
theorem bound_tail_lt {f : Nat} {c d : Cursor} {v : Value}
    (h : readValue f c = .ok (v, d)) (hb : c.data.size - c.pos ≤ f) :
    d.data.size - d.pos ≤ f - 1 := by
  have hf : 1 ≤ f := by
    cases f with
    | zero => simp only [readValue] at h; exact absurd h (by simp)
    | succ k => omega
  have hd := (readRows_data f).1 c v d h
  have hp := readValue_lt hf h
  rw [hd]; omega

/-- The element read's budget, which the element loop's count induction passes on. -/
theorem bound_tail_element {f : Nat} {ed : Option EncodingDecl} {c d : Cursor} {v : Value}
    (h : specElementData f ed c = .ok (v, d)) (hb : c.data.size - c.pos ≤ f) :
    d.data.size - d.pos ≤ f := by
  have hd := specElementData_data f ed c v d h
  have hp := specElementData_progress f ed c v d h
  rw [hd]; omega

/-- **An element declaration set whose rows carry a width.** The declared surface's rows below the
fixed category are one and four octets wide, and a zero-width header would leave the two fuels' item
loops reached with nothing spent — which is why the element clauses carry this rather than a bare
`Option EncodingDecl`. -/
def WideOption (ed : Option EncodingDecl) : Prop :=
  ∀ decl : EncodingDecl, ed = some decl → decl.category ≠ Generated.Oasis.Category.fixed →
    1 ≤ decl.width

/-- **Every reader in the value cluster agrees with itself across fuels above the octet bound**, at
one fuel. Six clauses rather than one, because the readers are mutually recursive and their
guard-free forms are false at the boundary: the item loop refuses at fuel zero and accepts at fuel one
with a zero count, so its clause is stated from fuel one, and the compound and array readers need a
header wide enough to spend the octet that puts their item loops a level down. -/
structure FuelIrrelevant (f : Nat) : Prop where
  value : ∀ (f' : Nat), f ≤ f' → ∀ (c : Cursor), c.data.size - c.pos ≤ f →
    AnswerAgrees (readValue f c) (readValue f' c)
  items : ∀ (f' : Nat), f ≤ f' → 1 ≤ f → ∀ (count : Nat) (c : Cursor),
    c.data.size - c.pos ≤ f - 1 → AnswerAgrees (readItems f count c) (readItems f' count c)
  compound : ∀ (f' : Nat), f ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
    c.data.size - c.pos ≤ f → AnswerAgrees (readCompound f decl c) (readCompound f' decl c)
  array : ∀ (f' : Nat), f ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
    c.data.size - c.pos ≤ f → AnswerAgrees (readArrayData f decl c) (readArrayData f' decl c)
  element : ∀ (f' : Nat), f ≤ f' → ∀ (ed : Option EncodingDecl) (c : Cursor), WideOption ed →
    c.data.size - c.pos ≤ f → AnswerAgrees (specElementData f ed c) (specElementData f' ed c)
  elementLoop : ∀ (f' : Nat), f ≤ f' → ∀ (ed : Option EncodingDecl) (count : Nat) (c : Cursor),
    WideOption ed → c.data.size - c.pos ≤ f →
    AnswerAgrees (readElementsLoop f ed count c) (readElementsLoop f' ed count c)


/-- The invariant at every fuel up to `n`. A clause is read at the fuel below when a reader descends
into a container two levels down, so the step has to reach every lower level, not only its own. -/
def FuelIrrelevantUpTo (n : Nat) : Prop := ∀ k, k ≤ n → FuelIrrelevant k

set_option maxRecDepth 10000 in
/-- **The declared surface's rows below the fixed category carry a width.** One finite evaluation of
the table itself, asked of every octet there is. -/
theorem dataDecl_rows_wide :
    (List.range 256).all (fun n =>
      match (SpecAMQP.Spec.Codec.dataDecl (UInt8.ofNat n)).toOption with
      | some d => (match d.category with
        | Generated.Oasis.Category.fixed => true
        | _ => decide (1 ≤ d.width))
      | none => true) = true := by
  decide

set_option maxRecDepth 10000 in
/-- The same for the element-constructor lookup, which reads the same table. -/
theorem elementDecl_rows_wide :
    (List.range 256).all (fun n =>
      match (SpecAMQP.Spec.Codec.elementDecl? (UInt8.ofNat n)).toOption with
      | some (some d) => (match d.category with
        | Generated.Oasis.Category.fixed => true
        | _ => decide (1 ≤ d.width))
      | _ => true) = true := by
  decide

/-- **The declared surface's rows below the fixed category carry a width**, read off the sweep at one
octet: the compound, array and variable rows are one and four octets wide, and a zero-width header
would leave the item loop reached with nothing spent. -/
theorem width_of_dataDecl {code : UInt8} {decl : EncodingDecl}
    (hd : SpecAMQP.Spec.Codec.dataDecl code = .ok decl)
    (hc : decl.category ≠ Generated.Oasis.Category.fixed) : 1 ≤ decl.width := by
  have hmem := List.all_eq_true.mp dataDecl_rows_wide code.toNat
    (List.mem_range.mpr code.toNat_lt)
  rw [show UInt8.ofNat code.toNat = code from by simp [UInt8.ofNat_toNat]] at hmem
  rw [hd] at hmem
  simp only [Except.toOption] at hmem
  cases hcat : decl.category with
  | fixed => exact absurd hcat hc
  | «variable» => exact of_decide_eq_true hmem
  | compound => exact of_decide_eq_true hmem
  | array => exact of_decide_eq_true hmem

/-- The same read off `elementDecl?`: an array's element constructor names a row of the same table. -/
theorem wideOption_of_elementDecl {ctor : UInt8} {ed : Option EncodingDecl}
    (h : SpecAMQP.Spec.Codec.elementDecl? ctor = .ok ed) : WideOption ed := by
  intro decl heq hc
  have hmem := List.all_eq_true.mp elementDecl_rows_wide ctor.toNat
    (List.mem_range.mpr ctor.toNat_lt)
  rw [show UInt8.ofNat ctor.toNat = ctor from by simp [UInt8.ofNat_toNat]] at hmem
  rw [h] at hmem
  simp only [Except.toOption, heq] at hmem
  cases hcat : decl.category with
  | fixed => exact absurd hcat hc
  | «variable» => exact of_decide_eq_true hmem
  | compound => exact of_decide_eq_true hmem
  | array => exact of_decide_eq_true hmem

/-- **Every reader in the value cluster answers the same way at every fuel above the octet bound.**

The proof is one induction over the fuel, and each level's six clauses are proved in dependency order,
because the readers are one `mutual` block and two of the dependences stay *inside* a level: the
compound reader reads its items at its own fuel, and the element loop reads the element decision at
its own fuel too. Everything else descends a level, which is why the induction hypothesis has to be
the family at every fuel below rather than the last one. -/
theorem fuelIrrelevantUpTo_all : ∀ n : Nat, FuelIrrelevantUpTo n := by
  intro n
  induction n with
  | zero =>
    have hVal0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (c : Cursor), c.data.size - c.pos ≤ 0 →
        AnswerAgrees (readValue 0 c) (readValue f' c) := by
      intro f' _ c hb
      have hle : c.data.size ≤ c.pos := by omega
      cases f' with
      | zero => exact answerAgrees_refl _
      | succ m =>
        have h0 : readValue 0 c = .error (SpecAMQP.Spec.Codec.refusal "truncated"
            "the input ends before the value does") := by simp only [readValue]
        cases hu : takeU8 c with
        | error r =>
          have h1 : readValue (m + 1) c = .error r := by
            simp only [readValue, hu, except_bind_error]
          have hcl := spec_takeU8_error_class hu
          rw [h0, h1]
          exact ⟨fun a ha => absurd ha (by simp),
            fun r₀ hr₀ => ⟨r, rfl, by rw [← Except.error.inj hr₀]; exact hcl.symm⟩⟩
        | ok p => obtain ⟨b, d⟩ := p; exact absurd (spec_takeU8_lt hu) (by omega)
    have hIt0 : ∀ (f' : Nat), 0 ≤ f' → 1 ≤ 0 → ∀ (count : Nat) (c : Cursor),
        c.data.size - c.pos ≤ 0 - 1 →
        AnswerAgrees (readItems 0 count c) (readItems f' count c) := by
      intro f' _ h1
      exact absurd h1 (by omega)
    have hComp0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
        c.data.size - c.pos ≤ 0 →
        AnswerAgrees (readCompound 0 decl c) (readCompound f' decl c) := by
      intro f' _ decl c hw hb
      have hle : c.data.size ≤ c.pos := by omega
      have h0 := spec_readCompound_header (fuel := 0) hw c hle
      cases f' with
      | zero => exact answerAgrees_refl _
      | succ m =>
        rw [h0, spec_readCompound_header (fuel := m + 1) hw c hle]
        exact answerAgrees_refl _
    have hArr0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
        c.data.size - c.pos ≤ 0 →
        AnswerAgrees (readArrayData 0 decl c) (readArrayData f' decl c) := by
      intro f' _ decl c hw hb
      have hle : c.data.size ≤ c.pos := by omega
      cases f' with
      | zero => exact answerAgrees_refl _
      | succ m =>
        have h0 : readArrayData 0 decl c = .error (SpecAMQP.Spec.Codec.refusal "truncated"
            "the input ends before the array does") := by simp only [readArrayData]
        cases h1 : takeBe decl.width c with
        | error r =>
          have h1' : readArrayData (m + 1) decl c = .error r := by
            simp only [readArrayData, h1, except_bind_error]
          have hcl := spec_takeBe_error_class h1
          rw [h0, h1']
          exact ⟨fun a ha => absurd ha (by simp),
            fun r₀ hr₀ => ⟨r, rfl, by rw [← Except.error.inj hr₀]; exact hcl.symm⟩⟩
        | ok p => obtain ⟨size, c₁⟩ := p; rw [spec_takeBe_exhausted hw hle] at h1; exact absurd h1 (by simp)
    have hEl0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (ed : Option EncodingDecl) (c : Cursor), WideOption ed →
        c.data.size - c.pos ≤ 0 →
        AnswerAgrees (specElementData 0 ed c) (specElementData f' ed c) := by
      intro f' _ ed c hw hb
      have hle : c.data.size ≤ c.pos := by omega
      cases f' with
      | zero => exact answerAgrees_refl _
      | succ m =>
        cases hed : ed with
        | none =>
          simp only [specElementData]
          exact answerAgrees_bind_error (hVal0 (m + 1) (Nat.zero_le (m + 1)) c (by omega))
            (fun a ha => by simp only [readValue] at ha; exact absurd ha (by simp)) _ _
        | some decl =>
          simp only [specElementData]
          cases hcat : decl.category with
          | fixed => exact answerAgrees_refl _
          | «variable» => exact answerAgrees_refl _
          | compound =>
            exact hComp0 (m + 1) (Nat.zero_le (m + 1)) decl c
              (hw decl hed (by rw [hcat]; simp)) (by omega)
          | array =>
            exact hArr0 (m + 1) (Nat.zero_le (m + 1)) decl c
              (hw decl hed (by rw [hcat]; simp)) (by omega)
    have hElLoop0 : ∀ (f' : Nat), 0 ≤ f' → ∀ (ed : Option EncodingDecl) (count : Nat) (c : Cursor),
        WideOption ed → c.data.size - c.pos ≤ 0 →
        AnswerAgrees (readElementsLoop 0 ed count c) (readElementsLoop f' ed count c) := by
      intro f' _ ed count
      cases f' with
      | zero => intro c hw hb; exact answerAgrees_refl _
      | succ m =>
       induction count with
       | zero => intro c hw hb; simp only [readElementsLoop]; exact answerAgrees_refl _
       | succ k ihk =>
        intro c hw hb
        rw [specElementData_loop, specElementData_loop]
        refine answerAgrees_bind₂ (hEl0 (m + 1) (Nat.zero_le (m + 1)) ed c hw hb) ?_
        intro p hrd
        obtain ⟨a, d⟩ := p
        dsimp only at hrd ⊢
        exact answerAgrees_bind (ihk d hw (bound_tail_element hrd (by omega))) _
    have hLvl : FuelIrrelevant 0 := ⟨hVal0, hIt0, hComp0, hArr0, hEl0, hElLoop0⟩
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact hLvl
  | succ n ih =>
    have hVal : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (c : Cursor), c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (readValue (n + 1) c) (readValue f' c) := by
      intro f' hf' c hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases hu : takeU8 c with
      | error r => simp only [readValue, hu, except_bind_error]; exact answerAgrees_refl _
      | ok p =>
        obtain ⟨code, c₁⟩ := p
        have hc1d : c₁.data = c.data := spec_takeU8_data hu
        have hc1p : c₁.pos = c.pos + 1 := spec_takeU8_pos hu
        have hb1 : c₁.data.size - c₁.pos ≤ n := by rw [hc1d, hc1p]; omega
        simp only [readValue, hu, except_bind_ok]
        split
        all_goals first
          | (refine answerAgrees_bind₂ ((ih n le_rfl).value m hm c₁ hb1) ?_
             intro p hrd
             obtain ⟨a, d⟩ := p
             dsimp only at hrd ⊢
             exact answerAgrees_bind ((ih n le_rfl).value m hm d (bound_tail_value hrd hb1)) _)
          | exact answerAgrees_refl _
          | (cases hd : SpecAMQP.Spec.Codec.dataDecl code with
             | error r => exact answerAgrees_refl _
             | ok decl =>
               cases hcat : decl.category with
               | fixed => simp only [except_bind_ok, hcat]; exact answerAgrees_refl _
               | «variable» =>
                 simp only [except_bind_ok, hcat]; exact answerAgrees_refl _
               | compound =>
                 simp only [except_bind_ok, hcat]
                 exact (ih n le_rfl).compound m hm decl c₁
                   (width_of_dataDecl hd (by rw [hcat]; simp)) hb1
               | array =>
                 simp only [except_bind_ok, hcat]
                 exact (ih n le_rfl).array m hm decl c₁
                   (width_of_dataDecl hd (by rw [hcat]; simp)) hb1)
    have hIt : ∀ (f' : Nat), n + 1 ≤ f' → 1 ≤ n + 1 → ∀ (count : Nat) (c : Cursor),
        c.data.size - c.pos ≤ (n + 1) - 1 →
        AnswerAgrees (readItems (n + 1) count c) (readItems f' count c) := by
      intro f' hf' _ count c hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases count with
      | zero => simp only [readItems]; exact answerAgrees_refl _
      | succ k =>
        cases n with
        | zero =>
          -- the item read at this level is the value reader at fuel zero, which refuses outright
          simp only [readItems]
          have hb0 : c.data.size - c.pos ≤ 0 := by simpa using hb
          refine answerAgrees_bind_error ((ih 0 (Nat.zero_le 0)).value m (Nat.zero_le m) c hb0) ?_ _ _
          intro a ha
          simp only [readValue] at ha
          exact absurd ha (by simp)
        | succ n' =>
          simp only [readItems]
          refine answerAgrees_bind₂ ((ih (n' + 1) (by omega)).value m (by omega) c (by omega)) ?_
          intro p hrd
          obtain ⟨a, d⟩ := p
          dsimp only at hrd ⊢
          exact answerAgrees_bind ((ih (n' + 1) (by omega)).items m (by omega) (by omega) k d
            (bound_tail_lt hrd (by omega))) _
    have hComp : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
        c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (readCompound (n + 1) decl c) (readCompound f' decl c) := by
      intro f' hf' decl c hw hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases h1 : takeBe decl.width c with
      | error r => simp only [readCompound, h1, except_bind_error]; exact answerAgrees_refl _
      | ok p =>
        obtain ⟨size, c₁⟩ := p
        cases h2 : takeBe decl.width c₁ with
        | error r =>
          simp only [readCompound, h1, h2, except_bind_ok, except_bind_error]
          exact answerAgrees_refl _
        | ok q =>
          obtain ⟨count, c₂⟩ := q
          have hb2 : c₂.data.size - c₂.pos ≤ (n + 1) - 1 := by
            rw [spec_takeBe_data h2, spec_takeBe_data h1]
            have p1 := takeBe_advances decl.width c size c₁ h1
            have p2 := takeBe_advances decl.width c₁ count c₂ h2
            omega
          simp only [readCompound, h1, h2, except_bind_ok]
          split
          all_goals first
            | (refine answerAgrees_bind (hIt (m + 1) (by omega) (by omega) count c₂ hb2) _)
            | (split
               all_goals first
                 | (refine answerAgrees_bind (hIt (m + 1) (by omega) (by omega) count c₂ hb2) _)
                 | exact answerAgrees_refl _)
            | exact answerAgrees_refl _
    have hArr : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (decl : EncodingDecl) (c : Cursor), 1 ≤ decl.width →
        c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (readArrayData (n + 1) decl c) (readArrayData f' decl c) := by
      intro f' hf' decl c hw hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases h1 : takeBe decl.width c with
      | error r => simp only [readArrayData, h1, except_bind_error]; exact answerAgrees_refl _
      | ok p =>
        obtain ⟨size, c₁⟩ := p
        cases h2 : takeBe decl.width c₁ with
        | error r =>
          simp only [readArrayData, h1, h2, except_bind_ok, except_bind_error]
          exact answerAgrees_refl _
        | ok q =>
          obtain ⟨count, c₂⟩ := q
          simp only [readArrayData, h1, h2, except_bind_ok]
          split
          · all_goals exact answerAgrees_refl _
          · cases h3 : takeU8 c₂ with
            | error r =>
              simp only [except_bind_error]
              exact answerAgrees_refl _
            | ok p3 =>
              obtain ⟨ctor, c₃⟩ := p3
              cases h4 : elementDecl? ctor with
              | error r =>
                simp only [h4, except_bind_ok, except_bind_error]
                exact answerAgrees_refl _
              | ok ed =>
                simp only [h4, except_bind_ok]
                have hp3 := spec_takeU8_pos h3
                have hle3 := spec_takeU8_next_le h3
                have hp1 := takeBe_advances decl.width c size c₁ h1
                have hp2 := takeBe_advances decl.width c₁ count c₂ h2
                have hdd : c₃.data.size = c.data.size := by
                  rw [spec_takeU8_data h3, spec_takeBe_data h2, spec_takeBe_data h1]
                have hge : 2 ≤ n := by omega
                obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
                obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                simp only [readElements]
                refine answerAgrees_bind ((ih n' (by omega)).elementLoop m' (by omega) ed count c₃
                  (wideOption_of_elementDecl h4) (by omega)) _
    have hEl : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (ed : Option EncodingDecl) (c : Cursor), WideOption ed →
        c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (specElementData (n + 1) ed c) (specElementData f' ed c) := by
      intro f' hf' ed c hw hb
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      have hm : n ≤ m := by omega
      cases hed : ed with
      | none =>
        simp only [specElementData]
        refine answerAgrees_bind₂ (hVal (m + 1) (by omega) c hb) ?_
        intro p hrd
        obtain ⟨a, d⟩ := p
        dsimp only at hrd ⊢
        exact answerAgrees_bind (hVal (m + 1) (by omega) d (bound_tail_value hrd hb)) _
      | some decl =>
        simp only [specElementData]
        cases hcat : decl.category with
        | fixed => exact answerAgrees_refl _
        | «variable» => exact answerAgrees_refl _
        | compound =>
          exact hComp (m + 1) (by omega) decl c (hw decl hed (by rw [hcat]; simp)) hb
        | array =>
          exact hArr (m + 1) (by omega) decl c (hw decl hed (by rw [hcat]; simp)) hb
    have hElLoop : ∀ (f' : Nat), n + 1 ≤ f' → ∀ (ed : Option EncodingDecl) (count : Nat) (c : Cursor),
        WideOption ed → c.data.size - c.pos ≤ n + 1 →
        AnswerAgrees (readElementsLoop (n + 1) ed count c) (readElementsLoop f' ed count c) := by
      intro f' hf' ed count
      obtain ⟨m, rfl⟩ : ∃ m, f' = m + 1 := ⟨f' - 1, by omega⟩
      induction count with
      | zero => intro c hw hb; simp only [readElementsLoop]; exact answerAgrees_refl _
      | succ k ihk =>
        intro c hw hb
        rw [specElementData_loop, specElementData_loop]
        refine answerAgrees_bind₂ (hEl (m + 1) (by omega) ed c hw hb) ?_
        intro p hrd
        obtain ⟨a, d⟩ := p
        dsimp only at hrd ⊢
        exact answerAgrees_bind (ihk d hw (bound_tail_element hrd hb)) _
    have hLvl : FuelIrrelevant (n + 1) := ⟨hVal, hIt, hComp, hArr, hEl, hElLoop⟩
    intro k hk
    by_cases hkn : k ≤ n
    · exact ih k hkn
    · have hk1 : k = n + 1 := by omega
      subst hk1
      exact hLvl

/-- The level family holds at every fuel. -/
theorem fuelIrrelevant_all (f : Nat) : FuelIrrelevant f := fuelIrrelevantUpTo_all f f le_rfl

/-- **The specification's value reader answers the same at every fuel above the octet bound.** -/
theorem readValue_irrel {f f' : Nat} (hle : f ≤ f') {c : Cursor} (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (readValue f c) (readValue f' c) :=
  (fuelIrrelevant_all f).value f' hle c hb

/-- **The item loop, from fuel one** at a cursor whose octets the fuel covers one below itself. -/
theorem readItems_irrel {f f' : Nat} (hle : f ≤ f') (hf : 1 ≤ f) {count : Nat} {c : Cursor}
    (hb : c.data.size - c.pos ≤ f - 1) :
    AnswerAgrees (readItems f count c) (readItems f' count c) :=
  (fuelIrrelevant_all f).items f' hle hf count c hb

/-- **The compound reader**, whose header the width guard makes spend octets. -/
theorem readCompound_irrel {f f' : Nat} (hle : f ≤ f') {decl : EncodingDecl} {c : Cursor}
    (hw : 1 ≤ decl.width) (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (readCompound f decl c) (readCompound f' decl c) :=
  (fuelIrrelevant_all f).compound f' hle decl c hw hb

/-- The array reader, the same clause. -/
theorem readArrayData_irrel {f f' : Nat} (hle : f ≤ f') {decl : EncodingDecl} {c : Cursor}
    (hw : 1 ≤ decl.width) (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (readArrayData f decl c) (readArrayData f' decl c) :=
  (fuelIrrelevant_all f).array f' hle decl c hw hb

/-- The element decision. -/
theorem specElementData_irrel {f f' : Nat} (hle : f ≤ f') {ed : Option EncodingDecl} {c : Cursor}
    (hw : WideOption ed) (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (specElementData f ed c) (specElementData f' ed c) :=
  (fuelIrrelevant_all f).element f' hle ed c hw hb

/-- The element loop. -/
theorem readElementsLoop_irrel {f f' : Nat} (hle : f ≤ f') {ed : Option EncodingDecl}
    {count : Nat} {c : Cursor} (hw : WideOption ed) (hb : c.data.size - c.pos ≤ f) :
    AnswerAgrees (readElementsLoop f ed count c) (readElementsLoop f' ed count c) :=
  (fuelIrrelevant_all f).elementLoop f' hle ed count c hw hb

/-! ## The item loop, at one fuel on both sides

The irrelevance above aligns the loops; this is the relation itself, and the first of the three the
compound and array rows share. The reference refuses at fuel zero and reads its items at its
predecessor, while the specification reads its items at the fuel it was handed — so at one value-level
fuel the two item loops are one apart, and the *statement* puts them back together at one fuel: the
value law at the item's fuel relates the two item reads, the loop relation at the fuel below relates
the tails, and the irrelevance converts the specification's loop down where a caller has only
`Spec.readItems F` and `Ref.readItems (F - 1)`. -/

/-- **The two artefacts' item loops at one fuel.** The reference refuses at fuel zero and reads its
items at its predecessor; the specification reads its items at the fuel it was handed, so a compound's
items sit one fuel apart between the artefacts and *this* is the statement that puts them back
together: the value law at the item's fuel relates the two item reads, and the loop relation at the
fuel below relates the tails. -/
def ItemsAgree (j : Nat) (count : Nat) (c : Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (others : List SpecAMQP.Ref.Value) (d' : SpecAMQP.Ref.Cursor),
      SpecAMQP.Ref.readItems j count c' = .ok (others, d') →
      ∃ (bodies : List Value) (d : Cursor),
        SpecAMQP.Spec.Codec.readItems j count c = .ok (bodies, d) ∧
        CursorAgrees d d' ∧ BodiesAgreeList bodies others) ∧
  (∀ failure : SpecAMQP.Ref.DecodeError,
      SpecAMQP.Ref.readItems j count c' = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
        SpecAMQP.Spec.Codec.readItems j count c = .error refusal ∧
        (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- **The item loop agrees at one fuel**, given the value law at every fuel beneath it: the item read
is at the fuel below the loop's, and the loop's tail at the fuel below that. -/
theorem readItems_loop : ∀ (j : Nat), WireAgreesUpTo (j - 1) → 1 ≤ j →
    ∀ (count : Nat) (c : Cursor) (c' : SpecAMQP.Ref.Cursor), CursorAgrees c c' →
      c.data.size - c.pos ≤ j - 1 → ItemsAgree j count c c' := by
  intro j
  induction j with
  | zero => intro _ h1; exact absurd h1 (by omega)
  | succ s ih =>
    intro hup _ count c c' hc hb
    have hup' : WireAgreesUpTo s := hup
    have hval : WireAgrees s := wireAgreesUpTo_self hup'
    constructor
    · intro others d' hr
      cases count with
      | zero =>
        simp only [SpecAMQP.Ref.readItems] at hr
        obtain ⟨ho, hd⟩ : [] = others ∧ c' = d' := by
          simpa only [Except.ok.injEq, Prod.mk.injEq] using hr
        subst ho
        subst hd
        exact ⟨[], c, by simp only [SpecAMQP.Spec.Codec.readItems], hc,
          by simp only [BodiesAgreeList]⟩
      | succ k =>
        unfold SpecAMQP.Ref.readItems at hr
        obtain ⟨⟨other, d₁'⟩, hr1, hr⟩ := exists_of_bind_ok hr
        try dsimp only at hr
        obtain ⟨⟨rest, d₂'⟩, hr2, hr⟩ := exists_of_bind_ok hr
        try dsimp only at hr
        obtain ⟨ho, hd⟩ : other :: rest = others ∧ d₂' = d' := by
          simpa only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] using hr
        subst ho
        subst hd
        obtain ⟨body, d₁, hs1, hc1, -, hbody⟩ := (hval c c' hc hb).1 other d₁' hr1
        have hs_ge : 1 ≤ s := by
          cases s with
          | zero => simp only [SpecAMQP.Ref.readItems] at hr2; exact absurd hr2 (by simp)
          | succ t => omega
        obtain ⟨bodies, d₂, hs2, hc2, hbodies⟩ :=
          (ih (wireAgreesUpTo_mono hup' (by omega)) hs_ge k d₁ d₁' hc1 (bound_tail_lt hs1 hb)).1
            rest d₂' hr2
        refine ⟨body :: bodies, d₂, ?_, hc2, ?_⟩
        · simp only [SpecAMQP.Spec.Codec.readItems]
          rw [hs1, except_bind_ok, hs2, except_bind_ok, except_pure_ok]
        · simp only [BodiesAgreeList]; exact ⟨hbody, hbodies⟩
    · intro failure hr
      cases count with
      | zero => simp only [SpecAMQP.Ref.readItems] at hr; exact absurd hr (by simp)
      | succ k =>
        unfold SpecAMQP.Ref.readItems at hr
        cases h1 : SpecAMQP.Ref.readValue s c' with
        | error e =>
          rw [h1, except_bind_error] at hr
          simp only [Except.error.injEq] at hr
          subst hr
          obtain ⟨refusal, hs1, hcl⟩ := (hval c c' hc hb).2 e h1
          refine ⟨refusal, ?_, hcl⟩
          simp only [SpecAMQP.Spec.Codec.readItems]
          rw [hs1, except_bind_error]
        | ok p =>
          obtain ⟨other, d₁'⟩ := p
          rw [h1, except_bind_ok] at hr
          try dsimp only at hr
          cases h2 : SpecAMQP.Ref.readItems s k d₁' with
          | error e =>
            rw [h2, except_bind_error] at hr
            simp only [Except.error.injEq] at hr
            subst hr
            obtain ⟨body, d₁, hs1, hc1, -, -⟩ := (hval c c' hc hb).1 other d₁' h1
            -- the item read accepted, so the loop's fuel is not zero
            have hs_ge : 1 ≤ s := by
              cases s with
              | zero => simp only [SpecAMQP.Ref.readValue] at h1; exact absurd h1 (by simp)
              | succ t => omega
            obtain ⟨refusal, hs2, hcl⟩ :=
              (ih (wireAgreesUpTo_mono hup' (by omega)) hs_ge k d₁ d₁' hc1
                (bound_tail_lt hs1 hb)).2 e h2
            refine ⟨refusal, ?_, hcl⟩
            simp only [SpecAMQP.Spec.Codec.readItems]
            rw [hs1, except_bind_ok, hs2, except_bind_error]
          | ok q =>
            rw [h2, except_bind_ok] at hr
            try dsimp only at hr
            exact absurd hr (by simp)
/-- **The item loop with the specification's fuel as a parameter.** The reference's loop is at `j`; the
specification's at `js`, one fuel higher where a compound row calls it — and the two are related by
the irrelevance above. -/
def ItemsAgree2 (j : Nat) (js : Nat) (count : Nat) (c : Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (others : List SpecAMQP.Ref.Value) (d' : SpecAMQP.Ref.Cursor),
      SpecAMQP.Ref.readItems j count c' = .ok (others, d') →
      ∃ (bodies : List Value) (d : Cursor),
        SpecAMQP.Spec.Codec.readItems js count c = .ok (bodies, d) ∧
        CursorAgrees d d' ∧ BodiesAgreeList bodies others) ∧
  (∀ failure : SpecAMQP.Ref.DecodeError,
      SpecAMQP.Ref.readItems j count c' = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
        SpecAMQP.Spec.Codec.readItems js count c = .error refusal ∧
        (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- The loop relation transfers along a specification fuel its own irrelevance relates. -/
theorem itemsAgree2_of_irrel {j js count : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor}
    (h : ItemsAgree j count c c')
    (ha : AnswerAgrees (SpecAMQP.Spec.Codec.readItems j count c)
      (SpecAMQP.Spec.Codec.readItems js count c)) : ItemsAgree2 j js count c c' := by
  constructor
  · intro others d' hr
    obtain ⟨bodies, d, hs, hcd, hbl⟩ := h.1 others d' hr
    exact ⟨bodies, d, ha.1 (bodies, d) hs, hcd, hbl⟩
  · intro failure hr
    obtain ⟨refusal, hs, hcl⟩ := h.2 failure hr
    obtain ⟨refusal', hs', hcl'⟩ := ha.2 refusal hs
    exact ⟨refusal', hs', by rw [hcl, hcl']⟩

/-- **A compound row whose two size fields were read has at least two fuel.** The header spends two
octets of width at least one each, and the octet bound says the fuel covers the octets at the cursor —
which is what puts the item loops a fuel below their caller rather than at zero. -/
theorem two_le_fuel_of_header {F w : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hw : 1 ≤ w)
    (hc : CursorAgrees c c') (hb : c.data.size - c.pos ≤ F)
    {size : Nat} {c₁' : SpecAMQP.Ref.Cursor}
    (hr1 : SpecAMQP.Ref.takeBeU w c' = .ok (size, c₁'))
    {count : Nat} {c₂' : SpecAMQP.Ref.Cursor}
    (hr2 : SpecAMQP.Ref.takeBeU w c₁' = .ok (count, c₂')) : 2 ≤ F := by
  have hf2 : c.pos + 2 * w ≤ c.data.size := by
    have h1 := (ref_takeBeU_of_ok hr1).2.1
    have h2 := (ref_takeBeU_of_ok hr2).2.2
    have hd := (ref_takeBeU_of_ok hr1).1
    rw [h1, hd, ← hc.1, ← hc.2] at h2
    omega
  omega

/-- **The compound body on a list row.** The specification's `readCompound` against the reference's,
both at the fuel the value's constructor octet handed down: the two size fields are the landed
`takeBe`/`takeBeU` bridge, the item loops are one fuel apart and met by the irrelevance, and the size
comparisons are the same numbers over the same window — which is what makes the reference's negated
inequality the specification's equality. -/
theorem readCompound_list_body (F : Nat) (ih : WireAgreesUpTo (F - 2)) (decl : EncodingDecl)
    (hw : 1 ≤ decl.width) (howner : decl.owner = "list")
    {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    (hb : c.data.size - c.pos ≤ F) :
    StepAgreesAt BodiesAgree (SpecAMQP.Spec.Codec.readCompound F decl)
      (SpecAMQP.Ref.readCompound F decl.width) c c' := by
  cases F with
  | zero =>
    constructor
    · intro other d' hr
      simp only [SpecAMQP.Ref.readCompound] at hr
      exact absurd hr (by simp)
    · intro failure hr
      simp only [SpecAMQP.Ref.readCompound] at hr
      have hcl : (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = "truncated" := by
        rw [← Except.error.inj hr]
        simp only [SpecAMQP.Ref.Frame.valueFailure]
        rfl
      cases h1 : SpecAMQP.Spec.Codec.takeBe decl.width c with
      | error e =>
        refine ⟨e, ?_, ?_⟩
        · simp only [SpecAMQP.Spec.Codec.readCompound]; rw [h1, except_bind_error]
        · rw [spec_takeBe_error_class h1, hcl]
      | ok p =>
        obtain ⟨size, c₁⟩ := p
        cases h2 : SpecAMQP.Spec.Codec.takeBe decl.width c₁ with
        | error e =>
          refine ⟨e, ?_, ?_⟩
          · simp only [SpecAMQP.Spec.Codec.readCompound]
            rw [h1, except_bind_ok, h2, except_bind_error]
          · rw [spec_takeBe_error_class h2, hcl]
        | ok q =>
          obtain ⟨count, c₂⟩ := q
          refine ⟨SpecAMQP.Spec.Codec.refusal "truncated" "the input ends before the list's items do",
            ?_, ?_⟩
          · simp only [SpecAMQP.Spec.Codec.readCompound]
            rw [h1, except_bind_ok, h2, except_bind_ok, howner]
            simp only [SpecAMQP.Spec.Codec.readItems, except_bind_error]
          · rw [hcl]; rfl
  | succ G =>
    -- the reference reads its two size fields through `takeBeU`; the specification through `takeBe`
    constructor
    · intro other d' hr
      unfold SpecAMQP.Ref.readCompound at hr
      obtain ⟨⟨size, c₁'⟩, hr1, hr⟩ := exists_of_bind_ok hr
      try dsimp only at hr
      obtain ⟨⟨count, c₂'⟩, hr2, hr⟩ := exists_of_bind_ok hr
      try dsimp only at hr
      obtain ⟨⟨items', c₃'⟩, hr3, hr⟩ := exists_of_bind_ok hr
      try dsimp only at hr
      split at hr
      · exact absurd hr (by simp)
      · rename_i hpass
        have hsz : c₃'.pos - c₁'.pos = size := by simpa using hpass
        have hother : SpecAMQP.Ref.Value.list items' = other := by
          have := Except.ok.inj (by simpa only [except_pure_ok] using hr)
          exact (Prod.mk.inj this).1
        have hd' : c₃' = d' := by
          have := Except.ok.inj (by simpa only [except_pure_ok] using hr)
          exact (Prod.mk.inj this).2
        subst hother
        subst hd'
        obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
        obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
        have hdd : d₂.data.size = c.data.size := by
          rw [spec_takeBe_data hs2, spec_takeBe_data hs1]
        have hp1 := takeBe_advances decl.width c size d₁ hs1
        have hp2 := takeBe_advances decl.width d₁ count d₂ hs2
        have hb₂ : d₂.data.size - d₂.pos ≤ (G + 1) - 1 := by rw [hdd, hp2, hp1]; omega
        have hge : 1 ≤ G := by
          have := two_le_fuel_of_header hw hc hb hr1 hr2
          omega
        obtain ⟨items, c₃, hs3, hc3, hbl⟩ :=
          (itemsAgree2_of_irrel
            (readItems_loop G (wireAgreesUpTo_mono ih (by omega)) hge count d₂ c₂' hc2
              (by omega))
            (readItems_irrel (Nat.le_succ G) hge (by omega))).1 items' c₃' hr3
        have hmeasured : c₃.pos - d₁.pos = size := by
          rw [hc3.2, hc1.2]; exact hsz
        refine ⟨.list items, c₃, ?_, ?_, hc3, ?_⟩
        · simp only [SpecAMQP.Spec.Codec.readCompound]
          rw [hs1, except_bind_ok, hs2, except_bind_ok, howner]
          rw [hs3, except_bind_ok]
          rw [if_pos hmeasured]
          rfl
        · simp only [BodiesAgree]; exact hbl
        · rw [(readRows_data (G + 1)).2.1 count d₂ items c₃ hs3, spec_takeBe_data hs2,
            spec_takeBe_data hs1]
    · intro failure hr
      unfold SpecAMQP.Ref.readCompound at hr
      cases hr1 : SpecAMQP.Ref.takeBeU decl.width c' with
      | error e =>
        rw [hr1, except_bind_error] at hr
        simp only [Except.error.injEq] at hr
        subst hr
        obtain ⟨refusal, hs, hcl⟩ := takeBe_fails hc decl.width e hr1
        refine ⟨refusal, ?_, hcl⟩
        simp only [SpecAMQP.Spec.Codec.readCompound]
        rw [hs, except_bind_error]
      | ok p =>
        obtain ⟨size, c₁'⟩ := p
        rw [hr1, except_bind_ok] at hr
        try dsimp only at hr
        cases hr2 : SpecAMQP.Ref.takeBeU decl.width c₁' with
        | error e =>
          rw [hr2, except_bind_error] at hr
          simp only [Except.error.injEq] at hr
          subst hr
          obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
          obtain ⟨refusal, hs2, hcl⟩ := takeBe_fails hc1 decl.width e hr2
          refine ⟨refusal, ?_, hcl⟩
          simp only [SpecAMQP.Spec.Codec.readCompound]
          rw [hs1, except_bind_ok, hs2, except_bind_error]
        | ok q =>
          obtain ⟨count, c₂'⟩ := q
          rw [hr2, except_bind_ok] at hr
          try dsimp only at hr
          cases hr3 : SpecAMQP.Ref.readItems G count c₂' with
          | error e =>
            rw [hr3, except_bind_error] at hr
            simp only [Except.error.injEq] at hr
            subst hr
            obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
            obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
            have hdd : d₂.data.size = c.data.size := by
              rw [spec_takeBe_data hs2, spec_takeBe_data hs1]
            have hp1 := takeBe_advances decl.width c size d₁ hs1
            have hp2 := takeBe_advances decl.width d₁ count d₂ hs2
            have hge : 1 ≤ G := by
              have := two_le_fuel_of_header hw hc hb hr1 hr2
              omega
            obtain ⟨refusal, hs3, hcl⟩ :=
              (itemsAgree2_of_irrel
                (readItems_loop G (wireAgreesUpTo_mono ih (by omega)) hge count d₂ c₂' hc2
                  (by rw [hdd, hp2, hp1]; omega))
                (readItems_irrel (Nat.le_succ G) hge (by rw [hdd, hp2, hp1]; omega))).2 e hr3
            refine ⟨refusal, ?_, hcl⟩
            simp only [SpecAMQP.Spec.Codec.readCompound]
            rw [hs1, except_bind_ok, hs2, except_bind_ok, howner, hs3, except_bind_error]
            rfl
          | ok r =>
            obtain ⟨items', c₃'⟩ := r
            rw [hr3, except_bind_ok] at hr
            try dsimp only at hr
            split at hr
            · -- the reference's size comparison refuses
              simp only [Except.error.injEq] at hr
              subst hr
              obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
              obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
              have hdd : d₂.data.size = c.data.size := by
                rw [spec_takeBe_data hs2, spec_takeBe_data hs1]
              have hp1 := takeBe_advances decl.width c size d₁ hs1
              have hp2 := takeBe_advances decl.width d₁ count d₂ hs2
              have hge : 1 ≤ G := by
                have := two_le_fuel_of_header hw hc hb hr1 hr2
                omega
              obtain ⟨items, c₃, hs3, hc3, hbl⟩ :=
                (itemsAgree2_of_irrel
                  (readItems_loop G (wireAgreesUpTo_mono ih (by omega)) hge count d₂ c₂' hc2
                    (by rw [hdd, hp2, hp1]; omega))
                  (readItems_irrel (Nat.le_succ G) hge (by rw [hdd, hp2, hp1]; omega))).1
                    items' c₃' hr3
              rename_i hfail
              have hne : c₃.pos - d₁.pos ≠ size := by
                intro hcon
                have hz : c₃'.pos - c₁'.pos = size := by rw [← hc3.2, ← hc1.2]; exact hcon
                rw [hz] at hfail
                exact absurd hfail (by simp)
              refine ⟨SpecAMQP.Spec.Codec.refusal "sizeMismatch" s!"a list declares {size} \
                octet(s) after its size field and measures {c₃.pos - d₁.pos}", ?_, ?_⟩
              · simp only [SpecAMQP.Spec.Codec.readCompound]
                rw [hs1, except_bind_ok, hs2, except_bind_ok, howner, hs3, except_bind_ok]
                rw [if_neg hne]
                rfl
              · simp only [SpecAMQP.Ref.Frame.valueFailure]
                rfl
            · exact absurd hr (by simp)

/-! ## The compound body on the map rows

The map rows share the list body's skeleton — the two size fields through the same bridges, the item
loops one fuel apart met by the irrelevance, the size comparison over the same window — and differ in
the two places the map's own clause puts between them: the item count's parity is decided *before* the
items are read, and the value is the items' *pairing* rather than the items. Both readers make that
decision in the same place and refuse an odd count as `malformed`, which is what lets the two
computations be walked in step; the pairing is where the landed `pairUp_agrees` is the value equation.

The one arm here without a counterpart is the reference's own second line of defence: `Ref.pairUp`
answers `none` for an odd tail and `Ref.readMap` reports that as a further malformed. An even count
excludes it, and that is a fact about the reference's item loop rather than an assumption — the loop
answers one item per unit of the count it was handed, so the list the reference pairs is exactly
`count` long. `ref_readItems_length` and `ref_pairUp_isSome_of_even` are those two facts. The arm is
not removed, because removing it would change the reference; a branch closes the arms the reader has. -/

/-- **The reference's item loop answers `count` items.** The count is one of the loop's own parameters,
so the list it answers is exactly that long — which is the parity of the list the reference's own
pairing is handed. -/
theorem ref_readItems_length : ∀ (count : Nat) (fuel : Nat) (c : SpecAMQP.Ref.Cursor)
    (items : List SpecAMQP.Ref.Value) (c' : SpecAMQP.Ref.Cursor),
    SpecAMQP.Ref.readItems fuel count c = .ok (items, c') → items.length = count := by
  intro count
  induction count with
  | zero =>
    intro fuel c items c' h
    cases fuel with
    | zero => simp only [SpecAMQP.Ref.readItems] at h; exact absurd h (by simp)
    | succ f =>
      simp only [SpecAMQP.Ref.readItems] at h
      obtain ⟨ho, -⟩ : [] = items ∧ c = c' := by
        simpa only [Except.ok.injEq, Prod.mk.injEq] using h
      subst ho
      rfl
  | succ k ih =>
    intro fuel c items c' h
    cases fuel with
    | zero => simp only [SpecAMQP.Ref.readItems] at h; exact absurd h (by simp)
    | succ f =>
      unfold SpecAMQP.Ref.readItems at h
      obtain ⟨⟨item, d₁⟩, h1, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨⟨rest, d₂⟩, h2, h⟩ := exists_of_bind_ok h
      try dsimp only at h
      obtain ⟨ho, -⟩ : item :: rest = items ∧ d₂ = c' := by
        simpa only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] using h
      subst ho
      simp only [List.length_cons]
      rw [ih f d₁ rest d₂ h2]

/-- **An even item count leaves the reference's pairing something to answer.** The reference's
`pairUp` is the partial function that answers `none` for an odd tail, so a list of even length has a
pairing — the direction a reader needs, with the half-count carried explicitly so that the induction
is on the list's own structure rather than on a division. The empty list is its own pairing at every
count, and the singleton is the shape an even length excludes. -/
theorem ref_pairUp_isSome_of_even : ∀ (k : Nat) (ys : List SpecAMQP.Ref.Value),
    ys.length = 2 * k → ∃ zs, SpecAMQP.Ref.pairUp ys = some zs
  | _, [], _ => ⟨[], rfl⟩
  | _, [_], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | k + 1, y :: y' :: ys', h => by
    have hpar : ys'.length = 2 * k := by
      simp only [List.length_cons] at h
      omega
    obtain ⟨zs, hz⟩ := ref_pairUp_isSome_of_even k ys' hpar
    exact ⟨(y, y') :: zs, by simp only [SpecAMQP.Ref.pairUp, hz, Option.map_some]⟩

/-- **The compound body on a map row.** The specification's `readCompound` against the reference's
`readMap`, at the fuel the value's constructor octet handed down. The two size fields are the landed
bridge, the item loops are one fuel apart and met by the irrelevance, the parity decision is the same
decision over the same count, and the size comparisons are the same numbers over the same window —
which is what makes the reference's negated inequality the specification's equality. The value is the
items' pairing, and `pairUp_agrees` is the equation between the two pairings. -/
theorem readCompound_map_body (F : Nat) (ih : WireAgreesUpTo (F - 2)) (decl : EncodingDecl)
    (hw : 1 ≤ decl.width) (howner : decl.owner = "map")
    {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    (hb : c.data.size - c.pos ≤ F) :
    StepAgreesAt BodiesAgree (SpecAMQP.Spec.Codec.readCompound F decl)
      (SpecAMQP.Ref.readMap F decl.width) c c' := by
  cases F with
  | zero =>
    constructor
    · intro other d' hr
      simp only [SpecAMQP.Ref.readMap] at hr
      exact absurd hr (by simp)
    · intro failure hr
      simp only [SpecAMQP.Ref.readMap] at hr
      have hcl : (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = "truncated" := by
        rw [← Except.error.inj hr]
        simp only [SpecAMQP.Ref.Frame.valueFailure]
        rfl
      cases h1 : SpecAMQP.Spec.Codec.takeBe decl.width c with
      | error e =>
        refine ⟨e, ?_, ?_⟩
        · simp only [SpecAMQP.Spec.Codec.readCompound]; rw [h1, except_bind_error]
        · rw [spec_takeBe_error_class h1, hcl]
      | ok p =>
        obtain ⟨size, c₁⟩ := p
        cases h2 : SpecAMQP.Spec.Codec.takeBe decl.width c₁ with
        | error e =>
          refine ⟨e, ?_, ?_⟩
          · simp only [SpecAMQP.Spec.Codec.readCompound]
            rw [h1, except_bind_ok, h2, except_bind_error]
          · rw [spec_takeBe_error_class h2, hcl]
        | ok q =>
          -- the bound says the cursor holds nothing, so its header cannot have been read
          have hcontra := spec_takeBe_exhausted (w := decl.width) hw (c := c) (by omega)
          rw [h1] at hcontra
          exact absurd hcontra (by simp)
  | succ G =>
    constructor
    · intro other d' hr
      unfold SpecAMQP.Ref.readMap at hr
      obtain ⟨⟨size, c₁'⟩, hr1, hr⟩ := exists_of_bind_ok hr
      try dsimp only at hr
      obtain ⟨⟨count, c₂'⟩, hr2, hr⟩ := exists_of_bind_ok hr
      try dsimp only at hr
      split at hr
      · exact absurd hr (by simp)
      · rename_i hpar
        obtain ⟨⟨items', c₃'⟩, hr3, hr⟩ := exists_of_bind_ok hr
        try dsimp only at hr
        cases hp : SpecAMQP.Ref.pairUp items' with
        | none =>
          have habs : False := by rw [hp] at hr; simp at hr
          exact habs.elim
        | some pairs =>
          -- the rewritten pairing is reduced here rather than left as a match, so the splits below
          -- are the reference's two guards and not that match's two arms
          simp only [hp] at hr
          split at hr
          · exact absurd hr (by simp)
          · rename_i hnodup
            split at hr
            · exact absurd hr (by simp)
            · rename_i hpass
              have hsz : c₃'.pos - c₁'.pos = size := by simpa using hpass
              obtain ⟨hother, hcur'⟩ : SpecAMQP.Ref.Value.map pairs = other ∧ c₃' = d' := by
                simpa using hr
              subst hother
              subst hcur'
              obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
              obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
              have hdd : d₂.data.size = c.data.size := by
                rw [spec_takeBe_data hs2, spec_takeBe_data hs1]
              have hp1 := takeBe_advances decl.width c size d₁ hs1
              have hp2 := takeBe_advances decl.width d₁ count d₂ hs2
              have hb₂ : d₂.data.size - d₂.pos ≤ (G + 1) - 1 := by rw [hdd, hp2, hp1]; omega
              have hge : 1 ≤ G := by
                have := two_le_fuel_of_header hw hc hb hr1 hr2
                omega
              obtain ⟨items, c₃, hs3, hc3, hbl⟩ :=
                (itemsAgree2_of_irrel
                  (readItems_loop G (wireAgreesUpTo_mono ih (by omega)) hge count d₂ c₂' hc2
                    (by omega))
                  (readItems_irrel (Nat.le_succ G) hge (by omega))).1 items' c₃' hr3
              have hmeasured : c₃.pos - d₁.pos = size := by rw [hc3.2, hc1.2]; exact hsz
              -- the reference answered the map, so its duplicate-key check answered `false`, and the
              -- specification's check is the same question about the same map
              have hkeys : ¬(SpecAMQP.Spec.Codec.keysRepeat
                  (SpecAMQP.Spec.Codec.pairUp items) = true) := by
                simpa only [← keysRepeat_agrees (SpecAMQP.Spec.Codec.pairUp items) pairs
                  (pairUp_agrees pairs items items' hbl hp)] using hnodup
              refine ⟨.map (SpecAMQP.Spec.Codec.pairUp items), c₃, ?_, ?_, hc3, ?_⟩
              · simp only [SpecAMQP.Spec.Codec.readCompound]
                rw [hs1, except_bind_ok, hs2, except_bind_ok]
                simp only [howner]
                rw [if_neg hpar]
                rw [hs3, except_bind_ok]
                dsimp only
                rw [if_neg hkeys, if_pos hmeasured]
              · simp only [BodiesAgree]
                exact pairUp_agrees pairs items items' hbl hp
              · rw [(readRows_data (G + 1)).2.1 count d₂ items c₃ hs3, spec_takeBe_data hs2,
                  spec_takeBe_data hs1]
    · intro failure hr
      unfold SpecAMQP.Ref.readMap at hr
      cases hr1 : SpecAMQP.Ref.takeBeU decl.width c' with
      | error e =>
        rw [hr1, except_bind_error] at hr
        simp only [Except.error.injEq] at hr
        subst hr
        obtain ⟨refusal, hs, hcl⟩ := takeBe_fails hc decl.width e hr1
        refine ⟨refusal, ?_, hcl⟩
        simp only [SpecAMQP.Spec.Codec.readCompound]
        rw [hs, except_bind_error]
      | ok p =>
        obtain ⟨size, c₁'⟩ := p
        rw [hr1, except_bind_ok] at hr
        try dsimp only at hr
        cases hr2 : SpecAMQP.Ref.takeBeU decl.width c₁' with
        | error e =>
          rw [hr2, except_bind_error] at hr
          simp only [Except.error.injEq] at hr
          subst hr
          obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
          obtain ⟨refusal, hs2, hcl⟩ := takeBe_fails hc1 decl.width e hr2
          refine ⟨refusal, ?_, hcl⟩
          simp only [SpecAMQP.Spec.Codec.readCompound]
          rw [hs1, except_bind_ok, hs2, except_bind_error]
        | ok q =>
          obtain ⟨count, c₂'⟩ := q
          rw [hr2, except_bind_ok] at hr
          try dsimp only at hr
          split at hr
          · -- the reference refuses the odd count, and the specification refuses it in the same class
            rename_i hpar
            obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
            obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
            have hcond : (count % 2 != 0) = true := hpar
            simp only [Except.error.injEq] at hr
            subst hr
            refine ⟨SpecAMQP.Spec.Codec.refusal "malformed" s!"a map declares {count} item(s): keys and values come in pairs, so an odd count is not a map", ?_, ?_⟩
            · simp only [SpecAMQP.Spec.Codec.readCompound]
              rw [hs1, except_bind_ok, hs2, except_bind_ok]
              simp only [howner]
              rw [if_pos hcond]
            · simp only [SpecAMQP.Ref.Frame.valueFailure]
              rfl
          · rename_i hpar
            cases hr3 : SpecAMQP.Ref.readItems G count c₂' with
            | error e =>
              rw [hr3, except_bind_error] at hr
              simp only [Except.error.injEq] at hr
              subst hr
              obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
              obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
              have hdd : d₂.data.size = c.data.size := by
                rw [spec_takeBe_data hs2, spec_takeBe_data hs1]
              have hp1 := takeBe_advances decl.width c size d₁ hs1
              have hp2 := takeBe_advances decl.width d₁ count d₂ hs2
              have hge : 1 ≤ G := by
                have := two_le_fuel_of_header hw hc hb hr1 hr2
                omega
              obtain ⟨refusal, hs3, hcl⟩ :=
                (itemsAgree2_of_irrel
                  (readItems_loop G (wireAgreesUpTo_mono ih (by omega)) hge count d₂ c₂' hc2
                    (by rw [hdd, hp2, hp1]; omega))
                  (readItems_irrel (Nat.le_succ G) hge (by rw [hdd, hp2, hp1]; omega))).2 e hr3
              refine ⟨refusal, ?_, hcl⟩
              simp only [SpecAMQP.Spec.Codec.readCompound]
              rw [hs1, except_bind_ok, hs2, except_bind_ok]
              simp only [howner]
              rw [if_neg hpar, hs3, except_bind_error]
            | ok r =>
              obtain ⟨items', c₃'⟩ := r
              rw [hr3, except_bind_ok] at hr
              try dsimp only at hr
              cases hp : SpecAMQP.Ref.pairUp items' with
              | none =>
                -- the pairing refuses only an odd item count, and the count is even: the item loop
                -- answered `count` items, so this arm's failure is not the one in hand
                have hbool : (count % 2 != 0) = false := by
                  cases hb : (count % 2 != 0) with
                  | false => rfl
                  | true => exact absurd hb hpar
                have hodd : count % 2 = 0 := by simpa using hbool
                have hlen := ref_readItems_length count G c₂' items' c₃' hr3
                obtain ⟨k, hk⟩ := Nat.dvd_iff_mod_eq_zero.mpr hodd
                obtain ⟨zs, hzs⟩ := ref_pairUp_isSome_of_even k items' (by rw [hlen]; exact hk)
                exact absurd (hp.symm.trans hzs) (by simp)
              | some pairs =>
                simp only [hp] at hr
                split at hr
                · -- the reference refuses the repeated key, and the specification refuses the same
                  -- map in the same class
                  rename_i hdup
                  obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
                  obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
                  have hdd : d₂.data.size = c.data.size := by
                    rw [spec_takeBe_data hs2, spec_takeBe_data hs1]
                  have hp1 := takeBe_advances decl.width c size d₁ hs1
                  have hp2 := takeBe_advances decl.width d₁ count d₂ hs2
                  have hge : 1 ≤ G := by
                    have := two_le_fuel_of_header hw hc hb hr1 hr2
                    omega
                  obtain ⟨items, c₃, hs3, hc3, hbl⟩ :=
                    (itemsAgree2_of_irrel
                      (readItems_loop G (wireAgreesUpTo_mono ih (by omega)) hge count d₂ c₂' hc2
                        (by rw [hdd, hp2, hp1]; omega))
                      (readItems_irrel (Nat.le_succ G) hge (by rw [hdd, hp2, hp1]; omega))).1
                        items' c₃' hr3
                  -- the reference's refusal is the duplicate it names, and the specification's own
                  -- key comparison answers the same question of the same map
                  have hkeys : SpecAMQP.Spec.Codec.keysRepeat
                      (SpecAMQP.Spec.Codec.pairUp items) = true := by
                    rw [keysRepeat_agrees (SpecAMQP.Spec.Codec.pairUp items) pairs
                      (pairUp_agrees pairs items items' hbl hp)]
                    exact hdup
                  simp only [Except.error.injEq] at hr
                  subst hr
                  refine ⟨SpecAMQP.Spec.Codec.refusal "malformed" "a map carries two identical \
                    key values, and such a map is invalid", ?_, ?_⟩
                  · simp only [SpecAMQP.Spec.Codec.readCompound]
                    rw [hs1, except_bind_ok, hs2, except_bind_ok]
                    simp only [howner]
                    rw [if_neg hpar, hs3, except_bind_ok]
                    dsimp only
                    rw [if_pos hkeys]
                  · simp only [SpecAMQP.Ref.Frame.valueFailure]
                    rfl
                · rename_i hnodup
                  split at hr
                  · -- the reference's size comparison refuses, and the specification measures the
                    -- same window
                    simp only [Except.error.injEq] at hr
                    subst hr
                    obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
                    obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
                    have hdd : d₂.data.size = c.data.size := by
                      rw [spec_takeBe_data hs2, spec_takeBe_data hs1]
                    have hp1 := takeBe_advances decl.width c size d₁ hs1
                    have hp2 := takeBe_advances decl.width d₁ count d₂ hs2
                    have hge : 1 ≤ G := by
                      have := two_le_fuel_of_header hw hc hb hr1 hr2
                      omega
                    obtain ⟨items, c₃, hs3, hc3, hbl⟩ :=
                      (itemsAgree2_of_irrel
                        (readItems_loop G (wireAgreesUpTo_mono ih (by omega)) hge count d₂ c₂'
                          hc2 (by rw [hdd, hp2, hp1]; omega))
                        (readItems_irrel (Nat.le_succ G) hge
                          (by rw [hdd, hp2, hp1]; omega))).1 items' c₃' hr3
                    rename_i hfail
                    have hne : c₃.pos - d₁.pos ≠ size := by
                      intro hcon
                      have hz : c₃'.pos - c₁'.pos = size := by rw [← hc3.2, ← hc1.2]; exact hcon
                      rw [hz] at hfail
                      exact absurd hfail (by simp)
                    have hkeys : ¬(SpecAMQP.Spec.Codec.keysRepeat
                        (SpecAMQP.Spec.Codec.pairUp items) = true) := by
                      simpa only [← keysRepeat_agrees (SpecAMQP.Spec.Codec.pairUp items) pairs
                        (pairUp_agrees pairs items items' hbl hp)] using hnodup
                    refine ⟨SpecAMQP.Spec.Codec.refusal "sizeMismatch" s!"a map declares {size} \
                      octet(s) after its size field and measures {c₃.pos - d₁.pos}", ?_, ?_⟩
                    · simp only [SpecAMQP.Spec.Codec.readCompound]
                      rw [hs1, except_bind_ok, hs2, except_bind_ok]
                      simp only [howner]
                      rw [if_neg hpar, hs3, except_bind_ok]
                      dsimp only
                      rw [if_neg hkeys, if_neg hne]
                    · simp only [SpecAMQP.Ref.Frame.valueFailure]
                      rfl
                  · -- the size comparison passed and the reference answered the map, so the failure
                    -- hypothesis is contradicted
                    exact absurd hr (by simp)

/-! ## The four compound and map arms

The four arms that read a compound or a map are the first of the recursive arms, and they are the
ones the two loop relations already close: every one of them resolves the specification's
classification and table row with two `decide`-checked facts, hands *both* cursors to the body lemma
at the value-level fuel, and then rewrites the body's two readers back into the arms the octets
selected. What the arm adds to the body is nothing but that resolution — the body is already the
`StepAgreesAt` relation the arm needs, so the arm is the body's two conjuncts with the readers
rewritten.

The fuel the body wants is the arm's fuel *less two*: a compound's header is two size fields, and it
is those octets that put the item loops a level below the caller (`two_le_fuel_of_header` is what says
so from the body's own hypotheses). A caller therefore hands the arm `WireAgreesUpTo (fuel - 2)`
rather than the invariant itself, which is what the fuel induction's monotonicity supplies.

The empty map is worth naming here rather than in the map body: `0xC1` with a zero count is a
*success* on both sides and answers `map []`, while a zero count with the `list` owner answers
`list []` — the owner is what the row's own field decides, and both arms carry it into the body. -/

/-- **The `list8` row (`0xC0`).** The specification's `readValue` dispatches on the octet's
classification and then on the declared table, and the row this octet resolves is a one-octet `list`;
the reference matches the octet and reads at width one. Both hand their cursors to their own compound
reader one fuel down, which is what `readCompound_list_body` relates. -/
theorem arm_0xC0 (fuel : Nat) (ih : WireAgreesUpTo (fuel - 2)) (c : SpecAMQP.Spec.Codec.Cursor)
    (c' : SpecAMQP.Ref.Cursor) (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor)
    (hd : CursorAgrees d d') (hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xC0, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xC0, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0xC0 : UInt8).toNat = .compound 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xC0 : UInt8) =
      .ok ⟨192, some "list8", SpecAMQP.Generated.Oasis.Category.compound, 1, "list",
        "up to 2^8 - 1 list elements with total size less than 2^8 octets"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.readCompound fuel ⟨192, some "list8",
        SpecAMQP.Generated.Oasis.Category.compound, 1, "list",
        "up to 2^8 - 1 list elements with total size less than 2^8 octets"⟩ d := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = SpecAMQP.Ref.readCompound fuel 1 d' := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  obtain ⟨hok, herr⟩ := readCompound_list_body fuel ih ⟨192, some "list8",
    SpecAMQP.Generated.Oasis.Category.compound, 1, "list",
    "up to 2^8 - 1 list elements with total size less than 2^8 octets"⟩ (by decide) rfl hd hb
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨body, c₂, hf, hba, hcd, hdat⟩ := hok other c₂' h
    exact ⟨body, c₂, by rw [hS]; exact hf, hcd, by rw [hdat, hdata], hba⟩
  · intro failure h
    rw [hR] at h
    obtain ⟨refusal, hf, hcl⟩ := herr failure h
    exact ⟨refusal, by rw [hS]; exact hf, hcl⟩

/-- **The `map8` row (`0xC1`).** The same shape at the map owner: the table's row is a `map`, the
reference's octet selects its own map reader, and the pairing the map's value is belongs to the body. -/
theorem arm_0xC1 (fuel : Nat) (ih : WireAgreesUpTo (fuel - 2)) (c : SpecAMQP.Spec.Codec.Cursor)
    (c' : SpecAMQP.Ref.Cursor) (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor)
    (hd : CursorAgrees d d') (hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xC1, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xC1, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0xC1 : UInt8).toNat = .compound 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xC1 : UInt8) =
      .ok ⟨193, some "map8", SpecAMQP.Generated.Oasis.Category.compound, 1, "map",
        "up to 2^8 - 1 octets of encoded map data"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.readCompound fuel ⟨193, some "map8",
        SpecAMQP.Generated.Oasis.Category.compound, 1, "map",
        "up to 2^8 - 1 octets of encoded map data"⟩ d := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = SpecAMQP.Ref.readMap fuel 1 d' := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  obtain ⟨hok, herr⟩ := readCompound_map_body fuel ih ⟨193, some "map8",
    SpecAMQP.Generated.Oasis.Category.compound, 1, "map",
    "up to 2^8 - 1 octets of encoded map data"⟩ (by decide) rfl hd hb
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨body, c₂, hf, hba, hcd, hdat⟩ := hok other c₂' h
    exact ⟨body, c₂, by rw [hS]; exact hf, hcd, by rw [hdat, hdata], hba⟩
  · intro failure h
    rw [hR] at h
    obtain ⟨refusal, hf, hcl⟩ := herr failure h
    exact ⟨refusal, by rw [hS]; exact hf, hcl⟩

/-- **The `list32` row (`0xD0`).** The same list owner behind four-octet size fields: the
specification's row declares width four and the reference reads at four, and the body's own bridges
(`takeBe`/`takeBeU`) carry the wider fields. -/
theorem arm_0xD0 (fuel : Nat) (ih : WireAgreesUpTo (fuel - 2)) (c : SpecAMQP.Spec.Codec.Cursor)
    (c' : SpecAMQP.Ref.Cursor) (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor)
    (hd : CursorAgrees d d') (hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xD0, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xD0, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0xD0 : UInt8).toNat = .compound 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xD0 : UInt8) =
      .ok ⟨208, some "list32", SpecAMQP.Generated.Oasis.Category.compound, 4, "list",
        "up to 2^32 - 1 list elements with total size less than 2^32 octets"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.readCompound fuel ⟨208, some "list32",
        SpecAMQP.Generated.Oasis.Category.compound, 4, "list",
        "up to 2^32 - 1 list elements with total size less than 2^32 octets"⟩ d := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = SpecAMQP.Ref.readCompound fuel 4 d' := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  obtain ⟨hok, herr⟩ := readCompound_list_body fuel ih ⟨208, some "list32",
    SpecAMQP.Generated.Oasis.Category.compound, 4, "list",
    "up to 2^32 - 1 list elements with total size less than 2^32 octets"⟩ (by decide) rfl hd hb
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨body, c₂, hf, hba, hcd, hdat⟩ := hok other c₂' h
    exact ⟨body, c₂, by rw [hS]; exact hf, hcd, by rw [hdat, hdata], hba⟩
  · intro failure h
    rw [hR] at h
    obtain ⟨refusal, hf, hcl⟩ := herr failure h
    exact ⟨refusal, by rw [hS]; exact hf, hcl⟩

/-- **The `map32` row (`0xD1`).** The same map owner behind four-octet size fields. -/
theorem arm_0xD1 (fuel : Nat) (ih : WireAgreesUpTo (fuel - 2)) (c : SpecAMQP.Spec.Codec.Cursor)
    (c' : SpecAMQP.Ref.Cursor) (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor)
    (hd : CursorAgrees d d') (hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xD1, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xD1, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0xD1 : UInt8).toNat = .compound 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xD1 : UInt8) =
      .ok ⟨209, some "map32", SpecAMQP.Generated.Oasis.Category.compound, 4, "map",
        "up to 2^32 - 1 octets of encoded map data"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.readCompound fuel ⟨209, some "map32",
        SpecAMQP.Generated.Oasis.Category.compound, 4, "map",
        "up to 2^32 - 1 octets of encoded map data"⟩ d := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = SpecAMQP.Ref.readMap fuel 4 d' := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  obtain ⟨hok, herr⟩ := readCompound_map_body fuel ih ⟨209, some "map32",
    SpecAMQP.Generated.Oasis.Category.compound, 4, "map",
    "up to 2^32 - 1 octets of encoded map data"⟩ (by decide) rfl hd hb
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨body, c₂, hf, hba, hcd, hdat⟩ := hok other c₂' h
    exact ⟨body, c₂, by rw [hS]; exact hf, hcd, by rw [hdat, hdata], hba⟩
  · intro failure h
    rw [hR] at h
    obtain ⟨refusal, hf, hcl⟩ := herr failure h
    exact ⟨refusal, by rw [hS]; exact hf, hcl⟩

/-- **The element decision at one fuel**, as a step relation: the specification's `specElementData`
at `g` against the reference's `readElement (g+1)`.

The reference spends one unit of fuel per element *data* block — its `readElement` matches on
`fuel + 1` — while the specification's `readElementsLoop` hands its own fuel to the element decision,
which is why the two sit one apart. That is the same asymmetry the compound rows have on their
header, and it is why this relation is stated at these two fuels rather than at one. -/
def ElementDataAgrees (g : Nat) (ctor : UInt8) (ed : Option EncodingDecl)
    (c : Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  StepAgreesAt BodiesAgree (specElementData g ed) (SpecAMQP.Ref.readElement (g + 1) ctor) c c'

/-- The element decision at one fuel, as the function the loop's count induction consumes: every
constructor an array can declare, with the position and octet hypotheses the decision's zero-width
rows need — a zero-width row reads nothing, and `takeBytes 0` succeeds exactly when the cursor is
inside the buffer. -/
def ElementsDecideAt (g : Nat) : Prop :=
  ∀ (ctor : UInt8) (ed : Option EncodingDecl), SpecAMQP.Spec.Codec.elementDecl? ctor = .ok ed →
    ∀ (c : Cursor) (c' : SpecAMQP.Ref.Cursor), CursorAgrees c c' →
      c.pos ≤ c.data.size → c.data.size - c.pos ≤ g → ElementDataAgrees g ctor ed c c'

/-- **The element decision below a fuel**, which is the form the array body's recursion needs: an
array whose elements are arrays again asks for the decision at a lower fuel, so the family is what the
mutual recursion between the decision, the loop and the array body is inducted over. -/
def ElementsDecideBelow (n : Nat) : Prop := ∀ k, k < n → ElementsDecideAt k

/-- **The element loop at the one-fuel offset.** The reference's `readElements (g + 1)` against the
specification's `readElementsLoop g`: the reference reads each element at `g + 1` and the
specification's element decision at `g`, so the two element reads are related by `ElementDataAgrees g`
and the loops by this relation one count down. The count is what the induction is on — an element
whose data occupies no octets is still an element — and the element read's own tail is where the next
element is read: the position it hands on is `specElementData_le`'s, and the octet bound is
`bound_tail_element`'s, which is why both were landed before this. -/
def ElementsLoopAgrees (g : Nat) (ctor : UInt8) (ed : Option EncodingDecl) (count : Nat)
    (c : Cursor) (c' : SpecAMQP.Ref.Cursor) : Prop :=
  (∀ (others : List SpecAMQP.Ref.Value) (d' : SpecAMQP.Ref.Cursor),
      SpecAMQP.Ref.readElements (g + 1) ctor count c' = .ok (others, d') →
      ∃ (bodies : List Value) (d : Cursor),
        SpecAMQP.Spec.Codec.readElementsLoop g ed count c = .ok (bodies, d) ∧
        CursorAgrees d d' ∧ BodiesAgreeList bodies others) ∧
  (∀ failure : SpecAMQP.Ref.DecodeError,
      SpecAMQP.Ref.readElements (g + 1) ctor count c' = .error failure →
      ∃ refusal : SpecAMQP.Spec.Codec.Refusal,
        SpecAMQP.Spec.Codec.readElementsLoop g ed count c = .error refusal ∧
        (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = refusal.reasonClass)

/-- **The element loop agrees at the one-fuel offset**, given the element decision at its own fuel.
The count induction is the whole content: the element read is the decision, the tail is this relation
at the count below, and the two facts the tail needs from the element read — where the cursor is and
how many octets are left at it — are the landed `specElementData_le` and `bound_tail_element`. -/
theorem elementsLoop_agrees (g : Nat) (hdec : ElementsDecideAt g) (ctor : UInt8)
    (ed : Option EncodingDecl) (hed : SpecAMQP.Spec.Codec.elementDecl? ctor = .ok ed) :
    ∀ (count : Nat) (c : Cursor) (c' : SpecAMQP.Ref.Cursor), CursorAgrees c c' →
      c.pos ≤ c.data.size → c.data.size - c.pos ≤ g →
      ElementsLoopAgrees g ctor ed count c c' := by
  intro count
  induction count with
  | zero =>
    intro c c' hc hpos hb
    constructor
    · intro others d' hr
      simp only [SpecAMQP.Ref.readElements] at hr
      obtain ⟨ho, hd⟩ : [] = others ∧ c' = d' := by
        simpa only [Except.ok.injEq, Prod.mk.injEq] using hr
      subst ho
      subst hd
      exact ⟨[], c, by simp only [SpecAMQP.Spec.Codec.readElementsLoop], hc,
        by simp only [BodiesAgreeList]⟩
    · intro failure hr
      simp only [SpecAMQP.Ref.readElements] at hr
      exact absurd hr (by simp)
  | succ k ihk =>
    intro c c' hc hpos hb
    constructor
    · intro others d' hr
      unfold SpecAMQP.Ref.readElements at hr
      obtain ⟨⟨item', d₁'⟩, h1, hr⟩ := exists_of_bind_ok hr
      try dsimp only at hr
      obtain ⟨⟨rest', d₂'⟩, h2, hr⟩ := exists_of_bind_ok hr
      try dsimp only at hr
      obtain ⟨ho, hd⟩ : item' :: rest' = others ∧ d₂' = d' := by
        simpa only [except_pure_ok, Except.ok.injEq, Prod.mk.injEq] using hr
      subst ho
      subst hd
      obtain ⟨body, d₁, hs1, hbody, hc1, hdat1⟩ :=
        (hdec ctor ed hed c c' hc hpos hb).1 item' d₁' h1
      have hp1 : d₁.pos ≤ d₁.data.size := specElementData_le hs1 hpos
      have hb1 : d₁.data.size - d₁.pos ≤ g := bound_tail_element hs1 hb
      obtain ⟨bodies, d₂, hs2, hc2, hbodies⟩ := (ihk d₁ d₁' hc1 hp1 hb1).1 rest' d₂' h2
      refine ⟨body :: bodies, d₂, ?_, hc2, ?_⟩
      · rw [specElementData_loop, hs1, except_bind_ok, hs2, except_bind_ok]
      · simp only [BodiesAgreeList]
        exact ⟨hbody, hbodies⟩
    · intro failure hr
      unfold SpecAMQP.Ref.readElements at hr
      cases h1 : SpecAMQP.Ref.readElement (g + 1) ctor c' with
      | error e =>
        rw [h1, except_bind_error] at hr
        simp only [Except.error.injEq] at hr
        subst hr
        obtain ⟨refusal, hs1, hcl⟩ := (hdec ctor ed hed c c' hc hpos hb).2 e h1
        refine ⟨refusal, ?_, hcl⟩
        rw [specElementData_loop, hs1, except_bind_error]
      | ok p =>
        obtain ⟨item', d₁'⟩ := p
        rw [h1, except_bind_ok] at hr
        try dsimp only at hr
        cases h2 : SpecAMQP.Ref.readElements (g + 1) ctor k d₁' with
        | error e =>
          rw [h2, except_bind_error] at hr
          simp only [Except.error.injEq] at hr
          subst hr
          obtain ⟨body, d₁, hs1, -, hc1, hdat1⟩ :=
            (hdec ctor ed hed c c' hc hpos hb).1 item' d₁' h1
          have hp1 : d₁.pos ≤ d₁.data.size := specElementData_le hs1 hpos
          have hb1 : d₁.data.size - d₁.pos ≤ g := bound_tail_element hs1 hb
          obtain ⟨refusal, hs2, hcl⟩ := (ihk d₁ d₁' hc1 hp1 hb1).2 e h2
          refine ⟨refusal, ?_, hcl⟩
          rw [specElementData_loop, hs1, except_bind_ok, hs2, except_bind_error]
        | ok q =>
          rw [h2, except_bind_ok] at hr
          try dsimp only at hr
          exact absurd hr (by simp)

/-- **The array body at one fuel.** The specification's `readArrayData` against the reference's
`readArray`, at the fuel the value's constructor octet handed down: the two size fields, the count
limit, the element constructor's test, the elements themselves and the size comparison.

The elements are where the one-fuel offset lives: the reference reads them with `readElements fuel`,
whose element is `readElement fuel`, while the specification's `readElements fuel` passes one fuel
down (`readElementsLoop (fuel - 1)`), so the two loops sit one apart and `elementsLoop_agrees` is
their relation — which is why this body takes the element *decision* below its fuel as a hypothesis
rather than reaching for the value law: the array's element may itself be an array, and it is the
decision's own fuel family that terminates that recursion.

The bound is what makes the two smallest fuels work: at fuel zero both readers refuse by name, and at
fuel one the header's two size fields cannot both be read out of a cursor the fuel covers one octet of
(`two_le_fuel_of_header`). -/
theorem readArray_body (F : Nat) (hdec : ElementsDecideBelow F) (decl : EncodingDecl)
    (hw : 1 ≤ decl.width)
    {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    (hb : c.data.size - c.pos ≤ F) :
    StepAgreesAt BodiesAgree (SpecAMQP.Spec.Codec.readArrayData F decl)
      (SpecAMQP.Ref.readArray F decl.width) c c' := by
  cases F with
  | zero =>
    constructor
    · intro other d' hr
      simp only [SpecAMQP.Ref.readArray] at hr
      exact absurd hr (by simp)
    · intro failure hr
      simp only [SpecAMQP.Ref.readArray] at hr
      have hcl : (SpecAMQP.Ref.Frame.valueFailure failure).reasonClass = "truncated" := by
        rw [← Except.error.inj hr]
        simp only [SpecAMQP.Ref.Frame.valueFailure]
        rfl
      refine ⟨SpecAMQP.Spec.Codec.refusal "truncated" "the input ends before the array does", ?_, ?_⟩
      · simp only [SpecAMQP.Spec.Codec.readArrayData]
      · rw [hcl]; rfl
  | succ G =>
    cases G with
    | zero =>
      constructor
      · intro other d' hr
        unfold SpecAMQP.Ref.readArray at hr
        obtain ⟨⟨size, c₁'⟩, hr1, hr⟩ := exists_of_bind_ok hr
        try dsimp only at hr
        obtain ⟨⟨count, c₂'⟩, hr2, hr⟩ := exists_of_bind_ok hr
        try dsimp only at hr
        have h2 := two_le_fuel_of_header hw hc hb hr1 hr2
        exact absurd h2 (by omega)
      · intro failure hr
        unfold SpecAMQP.Ref.readArray at hr
        cases hr1 : SpecAMQP.Ref.takeBeU decl.width c' with
        | error e =>
          rw [hr1, except_bind_error] at hr
          simp only [Except.error.injEq] at hr
          subst hr
          obtain ⟨refusal, hs, hcl⟩ := takeBe_fails hc decl.width e hr1
          refine ⟨refusal, ?_, hcl⟩
          simp only [SpecAMQP.Spec.Codec.readArrayData]
          rw [hs, except_bind_error]
        | ok p =>
          obtain ⟨size, c₁'⟩ := p
          rw [hr1, except_bind_ok] at hr
          try dsimp only at hr
          cases hr2 : SpecAMQP.Ref.takeBeU decl.width c₁' with
          | error e =>
            rw [hr2, except_bind_error] at hr
            simp only [Except.error.injEq] at hr
            subst hr
            obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
            obtain ⟨refusal, hs2, hcl⟩ := takeBe_fails hc1 decl.width e hr2
            refine ⟨refusal, ?_, hcl⟩
            simp only [SpecAMQP.Spec.Codec.readArrayData]
            rw [hs1, except_bind_ok, hs2, except_bind_error]
          | ok q =>
            obtain ⟨count, c₂'⟩ := q
            have h2 := two_le_fuel_of_header hw hc hb hr1 hr2
            exact absurd h2 (by omega)
    | succ H =>
      constructor
      · intro other d' hr
        unfold SpecAMQP.Ref.readArray at hr
        obtain ⟨⟨size, c₁'⟩, hr1, hr⟩ := exists_of_bind_ok hr
        try dsimp only at hr
        obtain ⟨⟨count, c₂'⟩, hr2, hr⟩ := exists_of_bind_ok hr
        try dsimp only at hr
        by_cases hlim : count > SpecAMQP.Ref.arrayElementLimit
        · rw [if_pos hlim] at hr
          exact absurd hr (by simp)
        · rw [if_neg hlim] at hr
          obtain ⟨⟨ctor, c₃'⟩, hr3, hr⟩ := exists_of_bind_ok hr
          try dsimp only at hr
          by_cases hctor : (!(SpecAMQP.Ref.assignedConstructor ctor)) = true
          · rw [if_pos hctor] at hr
            exact absurd hr (by simp)
          · rw [if_neg hctor] at hr
            obtain ⟨⟨items', c₄'⟩, hr4, hr⟩ := exists_of_bind_ok hr
            try dsimp only at hr
            split at hr
            · exact absurd hr (by simp)
            · rename_i hpass
              have hsz : c₄'.pos - c₁'.pos = size := by simpa using hpass
              obtain ⟨hother, hcur'⟩ : SpecAMQP.Ref.Value.array ctor items' = other ∧ c₄' = d' := by
                simpa using hr
              subst hother
              subst hcur'
              obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
              obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
              have hdata2 : d₂.data = c.data := by
                rw [spec_takeBe_data hs2, spec_takeBe_data hs1]
              obtain ⟨d₃, hs3, hc3⟩ := takeU8_agrees hc2 ctor c₃' hr3
              have hdata3 : d₃.data = c.data := by rw [spec_takeU8_data hs3, hdata2]
              have hpos3 : d₃.pos ≤ d₃.data.size := spec_takeU8_next_le hs3
              have hp1 := takeBe_advances decl.width c size d₁ hs1
              have hp2 := takeBe_advances decl.width d₁ count d₂ hs2
              have hp3 := spec_takeU8_pos hs3
              have hb3 : d₃.data.size - d₃.pos ≤ H := by rw [hdata3, hp3, hp2, hp1]; omega
              obtain ⟨ed, hed⟩ := elementDecl?_of_assigned
                (by cases hac : SpecAMQP.Ref.assignedConstructor ctor <;> simp_all)
              obtain ⟨items, c₄, hs4, hc4, hbl⟩ :=
                (elementsLoop_agrees H (hdec H (by omega)) ctor ed hed count d₃ c₃' hc3 hpos3
                  hb3).1 items' c₄' hr4
              have hmeasured : c₄.pos - d₁.pos = size := by rw [hc4.2, hc1.2]; exact hsz
              refine ⟨.array ctor items, c₄, ?_, ?_, hc4, ?_⟩
              · simp only [SpecAMQP.Spec.Codec.readArrayData]
                rw [hs1, except_bind_ok, hs2, except_bind_ok]
                dsimp only
                have hlimS : ¬ (count > arrayElementLimit) := hlim
                rw [if_neg hlimS]
                rw [hs3, except_bind_ok, hed, except_bind_ok]
                simp only [SpecAMQP.Spec.Codec.readElements]
                rw [hs4, except_bind_ok]
                dsimp only
                rw [if_pos hmeasured]
              · simp only [BodiesAgree]
                exact ⟨trivial, hbl⟩
              · rw [(readRows_data H).2.2.2.2.2 ed count d₃ items c₄ hs4, hdata3]
      · intro failure hr
        unfold SpecAMQP.Ref.readArray at hr
        cases hr1 : SpecAMQP.Ref.takeBeU decl.width c' with
        | error e =>
          rw [hr1, except_bind_error] at hr
          simp only [Except.error.injEq] at hr
          subst hr
          obtain ⟨refusal, hs, hcl⟩ := takeBe_fails hc decl.width e hr1
          refine ⟨refusal, ?_, hcl⟩
          simp only [SpecAMQP.Spec.Codec.readArrayData]
          rw [hs, except_bind_error]
        | ok p =>
          obtain ⟨size, c₁'⟩ := p
          rw [hr1, except_bind_ok] at hr
          try dsimp only at hr
          cases hr2 : SpecAMQP.Ref.takeBeU decl.width c₁' with
          | error e =>
            rw [hr2, except_bind_error] at hr
            simp only [Except.error.injEq] at hr
            subst hr
            obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
            obtain ⟨refusal, hs2, hcl⟩ := takeBe_fails hc1 decl.width e hr2
            refine ⟨refusal, ?_, hcl⟩
            simp only [SpecAMQP.Spec.Codec.readArrayData]
            rw [hs1, except_bind_ok, hs2, except_bind_error]
          | ok q =>
            obtain ⟨count, c₂'⟩ := q
            rw [hr2, except_bind_ok] at hr
            try dsimp only at hr
            by_cases hlim : count > SpecAMQP.Ref.arrayElementLimit
            · rw [if_pos hlim] at hr
              simp only [Except.error.injEq] at hr
              subst hr
              obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
              obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
              have hspec : SpecAMQP.Spec.Codec.readArrayData (H + 2) decl c =
                  .error (SpecAMQP.Spec.Codec.refusal "limit" s!"an array declares {count} element(s): this reader materialises at most {SpecAMQP.Spec.Codec.arrayElementLimit}") := by
                simp only [SpecAMQP.Spec.Codec.readArrayData]
                rw [hs1, except_bind_ok, hs2, except_bind_ok]
                dsimp only
                have hlimT : count > arrayElementLimit := hlim
                rw [if_pos hlimT]
              exact ⟨_, hspec, by simp only [SpecAMQP.Ref.Frame.valueFailure]; rfl⟩
            · rw [if_neg hlim] at hr
              cases hr3 : SpecAMQP.Ref.takeU8 c₂' with
              | error e =>
                rw [hr3, except_bind_error] at hr
                simp only [Except.error.injEq] at hr
                subst hr
                obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
                obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
                obtain ⟨refusal, hs3, hcl⟩ := takeU8_fails hc2 e hr3
                refine ⟨refusal, ?_, hcl⟩
                simp only [SpecAMQP.Spec.Codec.readArrayData]
                rw [hs1, except_bind_ok, hs2, except_bind_ok]
                dsimp only
                have hlimS : ¬ (count > arrayElementLimit) := hlim
                rw [if_neg hlimS, hs3, except_bind_error]
              | ok p3 =>
                obtain ⟨ctor, c₃'⟩ := p3
                rw [hr3, except_bind_ok] at hr
                try dsimp only at hr
                by_cases hctor : (!(SpecAMQP.Ref.assignedConstructor ctor)) = true
                · rw [if_pos hctor] at hr
                  simp only [Except.error.injEq] at hr
                  subst hr
                  obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
                  obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
                  obtain ⟨d₃, hs3, hc3⟩ := takeU8_agrees hc2 ctor c₃' hr3
                  obtain ⟨r, hr', hcl⟩ := elementDecl?_refusal
                    (by cases hac : SpecAMQP.Ref.assignedConstructor ctor <;> simp_all)
                  refine ⟨r, ?_, ?_⟩
                  · simp only [SpecAMQP.Spec.Codec.readArrayData]
                    rw [hs1, except_bind_ok, hs2, except_bind_ok]
                    dsimp only
                    have hlimS : ¬ (count > arrayElementLimit) := hlim
                    rw [if_neg hlimS, hs3, except_bind_ok, hr', except_bind_error]
                  · simp only [SpecAMQP.Ref.Frame.valueFailure]
                    exact hcl.symm
                · rw [if_neg hctor] at hr
                  obtain ⟨d₁, hs1, hc1⟩ := takeBe_agrees hc decl.width size c₁' hr1
                  obtain ⟨d₂, hs2, hc2⟩ := takeBe_agrees hc1 decl.width count c₂' hr2
                  obtain ⟨d₃, hs3, hc3⟩ := takeU8_agrees hc2 ctor c₃' hr3
                  have hdata2 : d₂.data = c.data := by
                    rw [spec_takeBe_data hs2, spec_takeBe_data hs1]
                  have hdata3 : d₃.data = c.data := by rw [spec_takeU8_data hs3, hdata2]
                  have hpos3 : d₃.pos ≤ d₃.data.size := spec_takeU8_next_le hs3
                  have hp1 := takeBe_advances decl.width c size d₁ hs1
                  have hp2 := takeBe_advances decl.width d₁ count d₂ hs2
                  have hp3 := spec_takeU8_pos hs3
                  have hb3 : d₃.data.size - d₃.pos ≤ H := by rw [hdata3, hp3, hp2, hp1]; omega
                  obtain ⟨ed, hed⟩ := elementDecl?_of_assigned
                    (by cases hac : SpecAMQP.Ref.assignedConstructor ctor <;> simp_all)
                  cases hr5 : SpecAMQP.Ref.readElements (H + 1) ctor count c₃' with
                  | error e =>
                    rw [hr5, except_bind_error] at hr
                    simp only [Except.error.injEq] at hr
                    subst hr
                    obtain ⟨refusal, hs4, hcl⟩ :=
                      (elementsLoop_agrees H (hdec H (by omega)) ctor ed hed count d₃ c₃' hc3
                        hpos3 hb3).2 e hr5
                    refine ⟨refusal, ?_, hcl⟩
                    simp only [SpecAMQP.Spec.Codec.readArrayData]
                    rw [hs1, except_bind_ok, hs2, except_bind_ok]
                    dsimp only
                    have hlimS : ¬ (count > arrayElementLimit) := hlim
                    rw [if_neg hlimS, hs3, except_bind_ok, hed, except_bind_ok]
                    simp only [SpecAMQP.Spec.Codec.readElements]
                    rw [hs4, except_bind_error]
                  | ok r =>
                    obtain ⟨items', c₄'⟩ := r
                    rw [hr5, except_bind_ok] at hr
                    try dsimp only at hr
                    split at hr
                    · simp only [Except.error.injEq] at hr
                      subst hr
                      obtain ⟨items, c₄, hs4, hc4, hbl⟩ :=
                        (elementsLoop_agrees H (hdec H (by omega)) ctor ed hed count d₃ c₃' hc3
                          hpos3 hb3).1 items' c₄' hr5
                      rename_i hfail
                      have hne : c₄.pos - d₁.pos ≠ size := by
                        intro hcon
                        have hz : c₄'.pos - c₁'.pos = size := by
                          rw [← hc4.2, ← hc1.2]; exact hcon
                        rw [hz] at hfail
                        exact absurd hfail (by simp)
                      refine ⟨SpecAMQP.Spec.Codec.refusal "sizeMismatch" s!"an array declares {size} octet(s) after its size field and measures {c₄.pos - d₁.pos}", ?_, ?_⟩
                      · simp only [SpecAMQP.Spec.Codec.readArrayData]
                        rw [hs1, except_bind_ok, hs2, except_bind_ok]
                        dsimp only
                        have hlimS : ¬ (count > arrayElementLimit) := hlim
                        rw [if_neg hlimS, hs3, except_bind_ok, hed, except_bind_ok]
                        simp only [SpecAMQP.Spec.Codec.readElements]
                        rw [hs4, except_bind_ok]
                        dsimp only
                        rw [if_neg hne]
                      · simp only [SpecAMQP.Ref.Frame.valueFailure]
                        rfl
                    · exact absurd hr (by simp)

/-! ## The element decision, row by row

The decision the element loop and the array body take as `ElementsDecideAt`: one lemma per constructor
octet, each its own theorem so that the rows that are done are done. A row's content is its declared
row (a `decide`-checked fact naming the octet's `elementDecl?`), its payload step and its value
equation; the three stems above are what keeps the shape from being repeated forty times. The rows
landed here are the twenty whose element data is a payload the two artefacts already read the same way
- the six zero-width rows, the one-octet payloads, the wide unsigned and `char` widths and the six
opaque widths; the signed rows, the variable rows, the descriptor prefix and the six container rows are
owed, and the header's account names them. -/

theorem elementData_ok {g : Nat} {ctor : UInt8} {ed : Option EncodingDecl}
    (Sv : Value) (Rv : SpecAMQP.Ref.Value) (hval : BodiesAgree Sv Rv)
    (hspec : ∀ c : Cursor, c.pos ≤ c.data.size → specElementData g ed c = .ok (Sv, c))
    (href : ∀ c' : SpecAMQP.Ref.Cursor, SpecAMQP.Ref.readElement (g + 1) ctor c' = .ok (Rv, c'))
    {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c') (hpos : c.pos ≤ c.data.size) :
    ElementDataAgrees g ctor ed c c' := by
  constructor
  · intro other d' h
    rw [href c'] at h
    obtain ⟨hother, hcur'⟩ := Prod.mk.inj (Except.ok.inj h)
    subst hother
    subst hcur'
    exact ⟨Sv, c, hspec c hpos, hval, hc, rfl⟩
  · intro failure h
    rw [href c'] at h
    exact absurd h (by simp)

theorem elementData_step {α β : Type} {R : α → β → Prop}
    {StepS : Cursor → Except Refusal (α × Cursor)}
    {StepR : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    {g : Nat} {ctor : UInt8} {ed : Option EncodingDecl}
    {c : Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hstep : StepAgreesAt R StepS StepR c c')
    (Sv : α → Value) (Rv : β → SpecAMQP.Ref.Value)
    (hval : ∀ (a : α) (b : β), R a b → ∀ f : Cursor, StepS c = .ok (a, f) →
      BodiesAgree (Sv a) (Rv b))
    (hspec : ∀ x : Cursor, specElementData g ed x = StepS x >>= fun p => .ok (Sv p.1, p.2))
    (href : ∀ x' : SpecAMQP.Ref.Cursor,
      SpecAMQP.Ref.readElement (g + 1) ctor x' = StepR x' >>= fun p => .ok (Rv p.1, p.2)) :
    ElementDataAgrees g ctor ed c c' := by
  constructor
  · intro other d' h
    rw [href c'] at h
    obtain ⟨⟨b, d₂'⟩, hb, h⟩ := exists_of_bind_ok h
    try dsimp only at h
    obtain ⟨hother, hcur'⟩ := Prod.mk.inj (Except.ok.inj h)
    subst hother
    subst hcur'
    obtain ⟨a, d₂, hf, hrel, hcd, hdat⟩ := hstep.1 b d₂' hb
    exact ⟨Sv a, d₂, by rw [hspec c, hf, except_bind_ok], hval a b hrel d₂ hf, hcd, hdat⟩
  · intro failure h
    rw [href c'] at h
    cases hb : StepR c' with
    | error e =>
      rw [hb, except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hStep, hcl⟩ := hstep.2 e hb
      exact ⟨refusal, by rw [hspec c, hStep, except_bind_error], hcl⟩
    | ok p =>
      rw [hb, except_bind_ok] at h
      exact absurd h (by simp)

theorem element_0x40 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    (hpos : c.pos ≤ c.data.size) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0x40 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x40 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x40 : UInt8) = .ok (some ⟨64, none, Generated.Oasis.Category.fixed, 0, "null", "the null value"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_ok (Value.null) (SpecAMQP.Ref.Value.null) (by simp only [BodiesAgree]) ?_ ?_ hc hpos
  · intro x hx
    simp only [specElementData, SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero x hx, except_bind_ok]
    rfl
  · intro x'
    simp only [SpecAMQP.Ref.readElement]

theorem element_0x41 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    (hpos : c.pos ≤ c.data.size) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0x41 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x41 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x41 : UInt8) = .ok (some ⟨65, some "true", Generated.Oasis.Category.fixed, 0, "boolean", "the boolean value true"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_ok (Value.boolean true) (SpecAMQP.Ref.Value.boolean true) (by simp only [BodiesAgree]) ?_ ?_ hc hpos
  · intro x hx
    simp only [specElementData, SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero x hx, except_bind_ok]
    rfl
  · intro x'
    simp only [SpecAMQP.Ref.readElement]

theorem element_0x42 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    (hpos : c.pos ≤ c.data.size) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0x42 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x42 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x42 : UInt8) = .ok (some ⟨66, some "false", Generated.Oasis.Category.fixed, 0, "boolean", "the boolean value false"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_ok (Value.boolean false) (SpecAMQP.Ref.Value.boolean false) (by simp only [BodiesAgree]) ?_ ?_ hc hpos
  · intro x hx
    simp only [specElementData, SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero x hx, except_bind_ok]
    rfl
  · intro x'
    simp only [SpecAMQP.Ref.readElement]

theorem element_0x43 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    (hpos : c.pos ≤ c.data.size) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0x43 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x43 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x43 : UInt8) = .ok (some ⟨67, some "uint0", Generated.Oasis.Category.fixed, 0, "uint", "the uint value 0"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_ok (Value.uint 0) (SpecAMQP.Ref.Value.uint 0) (by simp only [BodiesAgree]; decide) ?_ ?_ hc hpos
  · intro x hx
    simp only [specElementData, SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero x hx, except_bind_ok]
    rfl
  · intro x'
    simp only [SpecAMQP.Ref.readElement]

theorem element_0x44 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    (hpos : c.pos ≤ c.data.size) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0x44 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x44 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x44 : UInt8) = .ok (some ⟨68, some "ulong0", Generated.Oasis.Category.fixed, 0, "ulong", "the ulong value 0"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_ok (Value.ulong 0) (SpecAMQP.Ref.Value.ulong 0) (by simp only [BodiesAgree]; decide) ?_ ?_ hc hpos
  · intro x hx
    simp only [specElementData, SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero x hx, except_bind_ok]
    rfl
  · intro x'
    simp only [SpecAMQP.Ref.readElement]

theorem element_0x45 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    (hpos : c.pos ≤ c.data.size) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0x45 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x45 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x45 : UInt8) = .ok (some ⟨69, some "list0", Generated.Oasis.Category.fixed, 0, "list", "the empty list (i.e. the list with no elements)"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_ok (Value.list []) (SpecAMQP.Ref.Value.list []) (by simp only [BodiesAgree, BodiesAgreeList]) ?_ ?_ hc hpos
  · intro x hx
    simp only [specElementData, SpecAMQP.Spec.Codec.readScalarData, SpecAMQP.Spec.Codec.readFixed]
    rw [spec_takeBytes_zero x hx, except_bind_ok]
    rfl
  · intro x'
    simp only [SpecAMQP.Ref.readElement]


/-! ### The one-octet payloads (`0x50`, `0x52`, `0x53`, `0x56`)

One octet, read by the specification through `takeBytes 1` and by the reference through `takeU8`, so the
relation is `payloadNat` against the octet's own value and the value equations are the width-carrying
round trips the value arms already use. -/

theorem element_0x50 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x50 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x50 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x50 : UInt8) =
      .ok (some ⟨80, none, Generated.Oasis.Category.fixed, 1, "ubyte",
        "8-bit unsigned integer"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeU8Nat c c' hc))
    (Sv := fun a => Value.ubyte (payloadNat a)) (Rv := fun b => SpecAMQP.Ref.Value.ubyte b)
    (hval := fun a b hrel _ _ => by simp only [BodiesAgree]; exact hrel) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨80, none, Generated.Oasis.Category.fixed, 1, "ubyte",
        "8-bit unsigned integer"⟩) x = SpecAMQP.Spec.Codec.takeBytes 1 x >>= fun p =>
          .ok (Value.ubyte (payloadNat p.1), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x52 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x52 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x52 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x52 : UInt8) =
      .ok (some ⟨82, some "smalluint", Generated.Oasis.Category.fixed, 1, "uint",
        "unsigned integer value in the range 0 to 255 inclusive"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeU8Nat c c' hc))
    (Sv := fun a => Value.uint (payloadNat a)) (Rv := fun b => SpecAMQP.Ref.Value.uint b.toUInt32)
    (hval := fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt8.toNat_toUInt32 b).symm) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨82, some "smalluint", Generated.Oasis.Category.fixed, 1,
        "uint", "unsigned integer value in the range 0 to 255 inclusive"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 1 x >>= fun p =>
          .ok (Value.uint (payloadNat p.1), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x53 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x53 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x53 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x53 : UInt8) =
      .ok (some ⟨83, some "smallulong", Generated.Oasis.Category.fixed, 1, "ulong",
        "unsigned long value in the range 0 to 255 inclusive"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeU8Nat c c' hc))
    (Sv := fun a => Value.ulong (payloadNat a)) (Rv := fun b => SpecAMQP.Ref.Value.ulong b.toUInt64)
    (hval := fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt8.toNat_toUInt64 b).symm) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨83, some "smallulong", Generated.Oasis.Category.fixed, 1,
        "ulong", "unsigned long value in the range 0 to 255 inclusive"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 1 x >>= fun p =>
          .ok (Value.ulong (payloadNat p.1), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x56 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x56 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x56 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x56 : UInt8) =
      .ok (some ⟨86, none, Generated.Oasis.Category.fixed, 1, "boolean",
        "boolean with the octet 0x00 being false and octet 0x01 being true"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeU8Nat c c' hc))
    (Sv := fun a => Value.boolean (payloadNat a != 0))
    (Rv := fun b => SpecAMQP.Ref.Value.boolean (b != 0x00))
    (hval := fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact uint8_ne_zero_bool b) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨86, none, Generated.Oasis.Category.fixed, 1, "boolean",
        "boolean with the octet 0x00 being false and octet 0x01 being true"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 1 x >>= fun p =>
          .ok (Value.boolean (payloadNat p.1 != 0), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl


theorem element_0x60 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x60 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x60 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x60 : UInt8) = .ok (some ⟨96, none, Generated.Oasis.Category.fixed, 2, "ushort", "16-bit unsigned integer in network byte order"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBeNat 2 c c' hc))
    (Sv := fun a => Value.ushort (payloadNat a)) (Rv := fun n => SpecAMQP.Ref.Value.ushort n.toUInt16)
    (hval := fun a b hrel f hf => by
      have hlt : b < 2 ^ 16 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt16.toNat_ofNat_of_lt (n := b) hlt).symm) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨96, none, Generated.Oasis.Category.fixed, 2, "ushort", "16-bit unsigned integer in network byte order"⟩) x = SpecAMQP.Spec.Codec.takeBytes 2 x >>= fun p =>
        .ok (Value.ushort (payloadNat p.1), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x70 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x70 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x70 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x70 : UInt8) = .ok (some ⟨112, none, Generated.Oasis.Category.fixed, 4, "uint", "32-bit unsigned integer in network byte order"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBeNat 4 c c' hc))
    (Sv := fun a => Value.uint (payloadNat a)) (Rv := fun n => SpecAMQP.Ref.Value.uint n.toUInt32)
    (hval := fun a b hrel f hf => by
      have hlt : b < 2 ^ 32 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt32.toNat_ofNat_of_lt (n := b) hlt).symm) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨112, none, Generated.Oasis.Category.fixed, 4, "uint", "32-bit unsigned integer in network byte order"⟩) x = SpecAMQP.Spec.Codec.takeBytes 4 x >>= fun p =>
        .ok (Value.uint (payloadNat p.1), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x73 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x73 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x73 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x73 : UInt8) = .ok (some ⟨115, some "utf32", Generated.Oasis.Category.fixed, 4, "char", "a UTF-32BE encoded Unicode character"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBeNat 4 c c' hc))
    (Sv := fun a => Value.char (payloadNat a)) (Rv := fun n => SpecAMQP.Ref.Value.char n.toUInt32)
    (hval := fun a b hrel f hf => by
      have hlt : b < 2 ^ 32 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt32.toNat_ofNat_of_lt (n := b) hlt).symm) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨115, some "utf32", Generated.Oasis.Category.fixed, 4, "char", "a UTF-32BE encoded Unicode character"⟩) x = SpecAMQP.Spec.Codec.takeBytes 4 x >>= fun p =>
        .ok (Value.char (payloadNat p.1), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x80 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x80 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x80 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x80 : UInt8) = .ok (some ⟨128, none, Generated.Oasis.Category.fixed, 8, "ulong", "64-bit unsigned integer in network byte order"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBeNat 8 c c' hc))
    (Sv := fun a => Value.ulong (payloadNat a)) (Rv := fun n => SpecAMQP.Ref.Value.ulong n.toUInt64)
    (hval := fun a b hrel f hf => by
      have hlt : b < 2 ^ 64 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact (UInt64.toNat_ofNat_of_lt (n := b) hlt).symm) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨128, none, Generated.Oasis.Category.fixed, 8, "ulong", "64-bit unsigned integer in network byte order"⟩) x = SpecAMQP.Spec.Codec.takeBytes 8 x >>= fun p =>
        .ok (Value.ulong (payloadNat p.1), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x72 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x72 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x72 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x72 : UInt8) = .ok (some ⟨114, some "ieee-754", Generated.Oasis.Category.fixed, 4, "float", "IEEE 754-2008 binary32"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBytes 4 c c' hc))
    (Sv := fun a => Value.float a) (Rv := fun b => SpecAMQP.Ref.Value.float b)
    (hval := fun a b hrel _ _ => by simp only [BodiesAgree]; exact hrel) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨114, some "ieee-754", Generated.Oasis.Category.fixed, 4, "float", "IEEE 754-2008 binary32"⟩) x = SpecAMQP.Spec.Codec.takeBytes 4 x >>= fun p =>
        .ok (Value.float p.1, p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x74 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x74 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x74 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x74 : UInt8) = .ok (some ⟨116, some "ieee-754", Generated.Oasis.Category.fixed, 4, "decimal32", "IEEE 754-2008 decimal32 using the Binary Integer Decimal encoding"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBytes 4 c c' hc))
    (Sv := fun a => Value.decimal32 a) (Rv := fun b => SpecAMQP.Ref.Value.decimal32 b)
    (hval := fun a b hrel _ _ => by simp only [BodiesAgree]; exact hrel) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨116, some "ieee-754", Generated.Oasis.Category.fixed, 4, "decimal32", "IEEE 754-2008 decimal32 using the Binary Integer Decimal encoding"⟩) x = SpecAMQP.Spec.Codec.takeBytes 4 x >>= fun p =>
        .ok (Value.decimal32 p.1, p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x82 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x82 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x82 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x82 : UInt8) = .ok (some ⟨130, some "ieee-754", Generated.Oasis.Category.fixed, 8, "double", "IEEE 754-2008 binary64"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBytes 8 c c' hc))
    (Sv := fun a => Value.double a) (Rv := fun b => SpecAMQP.Ref.Value.double b)
    (hval := fun a b hrel _ _ => by simp only [BodiesAgree]; exact hrel) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨130, some "ieee-754", Generated.Oasis.Category.fixed, 8, "double", "IEEE 754-2008 binary64"⟩) x = SpecAMQP.Spec.Codec.takeBytes 8 x >>= fun p =>
        .ok (Value.double p.1, p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x84 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x84 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x84 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x84 : UInt8) = .ok (some ⟨132, some "ieee-754", Generated.Oasis.Category.fixed, 8, "decimal64", "IEEE 754-2008 decimal64 using the Binary Integer Decimal encoding"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBytes 8 c c' hc))
    (Sv := fun a => Value.decimal64 a) (Rv := fun b => SpecAMQP.Ref.Value.decimal64 b)
    (hval := fun a b hrel _ _ => by simp only [BodiesAgree]; exact hrel) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨132, some "ieee-754", Generated.Oasis.Category.fixed, 8, "decimal64", "IEEE 754-2008 decimal64 using the Binary Integer Decimal encoding"⟩) x = SpecAMQP.Spec.Codec.takeBytes 8 x >>= fun p =>
        .ok (Value.decimal64 p.1, p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x94 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x94 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x94 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x94 : UInt8) = .ok (some ⟨148, some "ieee-754", Generated.Oasis.Category.fixed, 16, "decimal128", "IEEE 754-2008 decimal128 using the Binary Integer Decimal encoding"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBytes 16 c c' hc))
    (Sv := fun a => Value.decimal128 a) (Rv := fun b => SpecAMQP.Ref.Value.decimal128 b)
    (hval := fun a b hrel _ _ => by simp only [BodiesAgree]; exact hrel) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨148, some "ieee-754", Generated.Oasis.Category.fixed, 16, "decimal128", "IEEE 754-2008 decimal128 using the Binary Integer Decimal encoding"⟩) x = SpecAMQP.Spec.Codec.takeBytes 16 x >>= fun p =>
        .ok (Value.decimal128 p.1, p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

theorem element_0x98 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x98 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x98 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x98 : UInt8) = .ok (some ⟨152, none, Generated.Oasis.Category.fixed, 16, "uuid", "UUID as defined in section 4.1.2 of RFC-4122"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBytes 16 c c' hc))
    (Sv := fun a => Value.uuid a) (Rv := fun b => SpecAMQP.Ref.Value.uuid b)
    (hval := fun a b hrel _ _ => by simp only [BodiesAgree]; exact hrel) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨152, none, Generated.Oasis.Category.fixed, 16, "uuid", "UUID as defined in section 4.1.2 of RFC-4122"⟩) x = SpecAMQP.Spec.Codec.takeBytes 16 x >>= fun p =>
        .ok (Value.uuid p.1, p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl


/-! ## The variable element rows' stem -/

/-- **A variable element row: a length field, then the payload it announced.** -/
theorem elementData_var {α β : Type} {R : α → β → Prop}
    {StepS : Cursor → Except Refusal (α × Cursor)}
    {StepR : SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError (β × SpecAMQP.Ref.Cursor)}
    {g : Nat} {ctor : UInt8} {ed : Option EncodingDecl}
    {c : Cursor} {c' : SpecAMQP.Ref.Cursor}
    (Step2S : α → Cursor → Except Refusal (Value × Cursor))
    (Step2R : β → SpecAMQP.Ref.Cursor → Except SpecAMQP.Ref.DecodeError
      (SpecAMQP.Ref.Value × SpecAMQP.Ref.Cursor))
    (hstep : StepAgreesAt R StepS StepR c c')
    (h2 : ∀ (a : α) (b : β), R a b → ReadersAgree (Step2S a) (Step2R b))
    (hspec : ∀ x : Cursor, specElementData g ed x = StepS x >>= fun p => Step2S p.1 p.2)
    (href : ∀ x' : SpecAMQP.Ref.Cursor,
      SpecAMQP.Ref.readElement (g + 1) ctor x' = StepR x' >>= fun p => Step2R p.1 p.2) :
    ElementDataAgrees g ctor ed c c' := by
  constructor
  · intro other d' h
    rw [href c'] at h
    obtain ⟨⟨b, d₁'⟩, hb, h⟩ := exists_of_bind_ok h
    try dsimp only at h
    obtain ⟨a, d₁, hf, hrel, hcd, hdat⟩ := hstep.1 b d₁' hb
    obtain ⟨body, d₂, hk, hcd2, hdat2, hba⟩ := (h2 a b hrel d₁ d₁' hcd).1 other d' h
    refine ⟨body, d₂, ?_, hba, hcd2, ?_⟩
    · rw [hspec c, hf, except_bind_ok]
      exact hk
    · rw [hdat2, hdat]
  · intro failure h
    rw [href c'] at h
    cases hb : StepR c' with
    | error e =>
      rw [hb, except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hspec', hcl⟩ := hstep.2 e hb
      exact ⟨refusal, by rw [hspec c, hspec', except_bind_error], hcl⟩
    | ok p =>
      obtain ⟨b, d₁'⟩ := p
      rw [hb, except_bind_ok] at h
      try dsimp only at h
      obtain ⟨a, d₁, hf, hrel, hcd, -⟩ := hstep.1 b d₁' hb
      cases hb2 : Step2R b d₁' with
      | error e =>
        rw [hb2] at h
        simp only [Except.error.injEq] at h
        subst h
        obtain ⟨refusal, hspec2, hcl⟩ := (h2 a b hrel d₁ d₁' hcd).2 e hb2
        exact ⟨refusal, by rw [hspec c, hf, except_bind_ok]; exact hspec2, hcl⟩
      | ok q =>
        rw [hb2] at h
        exact absurd h (by simp)

/-! ## The signed and variable rows -/

/-- **The `byte` element row (`0x51`).** -/
theorem element_0x51 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x51 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x51 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x51 : UInt8) =
      .ok (some ⟨81, none, Generated.Oasis.Category.fixed, 1, "byte",
        "8-bit two's-complement integer"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeU8Nat c c' hc))
    (Sv := fun a => Value.byte (signedOfOctets 1 (payloadNat a)))
    (Rv := fun b => SpecAMQP.Ref.Value.byte (Int8.ofBitVec (BitVec.ofNat 8 b.toNat)))
    (hval := fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_8 b.toNat b.toNat_lt) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨81, none, Generated.Oasis.Category.fixed, 1, "byte",
        "8-bit two's-complement integer"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 1 x >>= fun p =>
          .ok (Value.byte (signedOfOctets 1 (payloadNat p.1)), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `smallint` element row (`0x54`).** -/
theorem element_0x54 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x54 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x54 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x54 : UInt8) =
      .ok (some ⟨84, some "smallint", Generated.Oasis.Category.fixed, 1, "int",
        "8-bit two's-complement integer"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeU8Nat c c' hc))
    (Sv := fun a => Value.int (signedOfOctets 1 (payloadNat a)))
    (Rv := fun b => SpecAMQP.Ref.Value.int (Int32.ofBitVec (BitVec.ofNat 32
      (SpecAMQP.Ref.signedOctet b % 4294967296).toNat)))
    (hval := fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (signedOctet_int32 b).symm) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨84, some "smallint", Generated.Oasis.Category.fixed, 1,
        "int", "8-bit two's-complement integer"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 1 x >>= fun p =>
          .ok (Value.int (signedOfOctets 1 (payloadNat p.1)), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `smalllong` element row (`0x55`).** -/
theorem element_0x55 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x55 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x55 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x55 : UInt8) =
      .ok (some ⟨85, some "smalllong", Generated.Oasis.Category.fixed, 1, "long",
        "8-bit two's-complement integer"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeU8Nat c c' hc))
    (Sv := fun a => Value.long (signedOfOctets 1 (payloadNat a)))
    (Rv := fun b => SpecAMQP.Ref.Value.long (Int64.ofBitVec (BitVec.ofNat 64
      (SpecAMQP.Ref.signedOctet b % 18446744073709551616).toNat)))
    (hval := fun a b hrel _ _ => by
      simp only [BodiesAgree]
      rw [hrel]
      exact (signedOctet_int64 b).symm) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨85, some "smalllong", Generated.Oasis.Category.fixed, 1,
        "long", "8-bit two's-complement integer"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 1 x >>= fun p =>
          .ok (Value.long (signedOfOctets 1 (payloadNat p.1)), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `short` element row (`0x61`).** -/
theorem element_0x61 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x61 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x61 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x61 : UInt8) =
      .ok (some ⟨97, none, Generated.Oasis.Category.fixed, 2, "short",
        "16-bit two's-complement integer in network byte order"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBeNat 2 c c' hc))
    (Sv := fun a => Value.short (signedOfOctets 2 (payloadNat a)))
    (Rv := fun n => SpecAMQP.Ref.Value.short (Int16.ofBitVec (BitVec.ofNat 16 n)))
    (hval := fun a b hrel f hf => by
      have hlt : b < 2 ^ 16 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_16 b hlt) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨97, none, Generated.Oasis.Category.fixed, 2, "short",
        "16-bit two's-complement integer in network byte order"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 2 x >>= fun p =>
          .ok (Value.short (signedOfOctets 2 (payloadNat p.1)), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `int` element row (`0x71`).** -/
theorem element_0x71 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x71 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x71 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x71 : UInt8) =
      .ok (some ⟨113, none, Generated.Oasis.Category.fixed, 4, "int",
        "32-bit two's-complement integer in network byte order"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBeNat 4 c c' hc))
    (Sv := fun a => Value.int (signedOfOctets 4 (payloadNat a)))
    (Rv := fun n => SpecAMQP.Ref.Value.int (Int32.ofBitVec (BitVec.ofNat 32 n)))
    (hval := fun a b hrel f hf => by
      have hlt : b < 2 ^ 32 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_32 b hlt) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨113, none, Generated.Oasis.Category.fixed, 4, "int",
        "32-bit two's-complement integer in network byte order"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 4 x >>= fun p =>
          .ok (Value.int (signedOfOctets 4 (payloadNat p.1)), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `long` element row (`0x81`).** -/
theorem element_0x81 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x81 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x81 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x81 : UInt8) =
      .ok (some ⟨129, none, Generated.Oasis.Category.fixed, 8, "long",
        "64-bit two's-complement integer in network byte order"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBeNat 8 c c' hc))
    (Sv := fun a => Value.long (signedOfOctets 8 (payloadNat a)))
    (Rv := fun n => SpecAMQP.Ref.Value.long (Int64.ofBitVec (BitVec.ofNat 64 n)))
    (hval := fun a b hrel f hf => by
      have hlt : b < 2 ^ 64 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_64 b hlt) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨129, none, Generated.Oasis.Category.fixed, 8, "long",
        "64-bit two's-complement integer in network byte order"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 8 x >>= fun p =>
          .ok (Value.long (signedOfOctets 8 (payloadNat p.1)), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `timestamp` element row (`0x83`).** -/
theorem element_0x83 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0x83 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x83 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x83 : UInt8) =
      .ok (some ⟨131, some "ms64", Generated.Oasis.Category.fixed, 8, "timestamp",
        "64-bit two's-complement integer representing milliseconds since the unix epoch"⟩) := by
    decide
  rw [hd] at hed
  cases hed
  refine elementData_step (hstep := (stepAgreesAll_takeBeNat 8 c c' hc))
    (Sv := fun a => Value.timestamp (signedOfOctets 8 (payloadNat a)))
    (Rv := fun n => SpecAMQP.Ref.Value.timestamp (Int64.ofBitVec (BitVec.ofNat 64 n)))
    (hval := fun a b hrel f hf => by
      have hlt : b < 2 ^ 64 := by
        have h1 := payloadNat_lt_of_takeBytes hf
        rw [hrel] at h1
        have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h2] at h1
        exact h1
      simp only [BodiesAgree]
      rw [hrel]
      exact signedOfOctets_64 b hlt) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨131, some "ms64", Generated.Oasis.Category.fixed, 8,
        "timestamp",
        "64-bit two's-complement integer representing milliseconds since the unix epoch"⟩) x =
        SpecAMQP.Spec.Codec.takeBytes 8 x >>= fun p =>
          .ok (Value.timestamp (signedOfOctets 8 (payloadNat p.1)), p.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-! ## The variable rows -/

/-- **The `vbin8` element row (`0xA0`).** -/
theorem element_0xA0 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0xA0 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xA0 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xA0 : UInt8) =
      .ok (some ⟨160, some "vbin8", Generated.Oasis.Category.variable, 1, "binary",
        "up to 2^8 - 1 octets of binary data"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_var
    (Step2S := fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q => .ok (.binary q.1, q.2))
    (Step2R := fun b f' => SpecAMQP.Ref.takeBytes b.toNat f' >>= fun q =>
      .ok (.binary q.1.toList, q.2))
    (hstep := (stepAgreesAll_takeBeOne c c' hc))
    (h2 := fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_ok (.binary bytes) (.binary bytes.toList)
            (by simp only [BodiesAgree]))) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨160, some "vbin8", Generated.Oasis.Category.variable, 1,
        "binary", "up to 2^8 - 1 octets of binary data"⟩) x =
        SpecAMQP.Spec.Codec.takeBe 1 x >>= fun p =>
          SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q => .ok (.binary q.1, q.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `str8-utf8` element row (`0xA1`).** -/
theorem element_0xA1 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0xA1 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xA1 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xA1 : UInt8) =
      .ok (some ⟨161, some "str8-utf8", Generated.Oasis.Category.variable, 1, "string",
        "up to 2^8 - 1 octets worth of UTF-8 Unicode (with no byte order mark)"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_var
    (Step2S := fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2))
    (Step2R := fun b f' => SpecAMQP.Ref.takeBytes b.toNat f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2))
    (hstep := (stepAgreesAll_takeBeOne c c' hc))
    (h2 := fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "string" bytes (fun s => .string s) (fun s => .string s)
            (fun s => by simp only [BodiesAgree]))) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨161, some "str8-utf8",
        Generated.Oasis.Category.variable, 1, "string",
        "up to 2^8 - 1 octets worth of UTF-8 Unicode (with no byte order mark)"⟩) x =
        SpecAMQP.Spec.Codec.takeBe 1 x >>= fun p =>
          SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
            SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `sym8` element row (`0xA3`).** -/
theorem element_0xA3 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0xA3 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xA3 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xA3 : UInt8) =
      .ok (some ⟨163, some "sym8", Generated.Oasis.Category.variable, 1, "symbol",
        "up to 2^8 - 1 seven bit ASCII characters representing a symbolic value"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_var
    (Step2S := fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2))
    (Step2R := fun b f' => SpecAMQP.Ref.takeBytes b.toNat f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2))
    (hstep := (stepAgreesAll_takeBeOne c c' hc))
    (h2 := fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "symbol" bytes (fun s => .symbol s) (fun s => .symbol s)
            (fun s => by simp only [BodiesAgree]))) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨163, some "sym8", Generated.Oasis.Category.variable, 1,
        "symbol", "up to 2^8 - 1 seven bit ASCII characters representing a symbolic value"⟩) x =
        SpecAMQP.Spec.Codec.takeBe 1 x >>= fun p =>
          SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
            SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `vbin32` element row (`0xB0`).** -/
theorem element_0xB0 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0xB0 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xB0 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xB0 : UInt8) =
      .ok (some ⟨176, some "vbin32", Generated.Oasis.Category.variable, 4, "binary",
        "up to 2^32 - 1 octets of binary data"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_var
    (Step2S := fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q => .ok (.binary q.1, q.2))
    (Step2R := fun b f' => SpecAMQP.Ref.takeBytes b f' >>= fun q => .ok (.binary q.1.toList, q.2))
    (hstep := (stepAgreesAll_takeBeEq 4 c c' hc))
    (h2 := fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_ok (.binary bytes) (.binary bytes.toList)
            (by simp only [BodiesAgree]))) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨176, some "vbin32", Generated.Oasis.Category.variable, 4,
        "binary", "up to 2^32 - 1 octets of binary data"⟩) x =
        SpecAMQP.Spec.Codec.takeBe 4 x >>= fun p =>
          SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q => .ok (.binary q.1, q.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `str32-utf8` element row (`0xB1`).** -/
theorem element_0xB1 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0xB1 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xB1 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xB1 : UInt8) =
      .ok (some ⟨177, some "str32-utf8", Generated.Oasis.Category.variable, 4, "string",
        "up to 2^32 - 1 octets worth of UTF-8 Unicode (with no byte order mark)"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_var
    (Step2S := fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2))
    (Step2R := fun b f' => SpecAMQP.Ref.takeBytes b f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "string" q.2 >>= fun r => .ok (.string r.1, r.2))
    (hstep := (stepAgreesAll_takeBeEq 4 c c' hc))
    (h2 := fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "string" bytes (fun s => .string s) (fun s => .string s)
            (fun s => by simp only [BodiesAgree]))) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨177, some "str32-utf8",
        Generated.Oasis.Category.variable, 4, "string",
        "up to 2^32 - 1 octets worth of UTF-8 Unicode (with no byte order mark)"⟩) x =
        SpecAMQP.Spec.Codec.takeBe 4 x >>= fun p =>
          SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
            SpecAMQP.Spec.Codec.utf8Of q.1 "string" >>= fun s => .ok (.string s, q.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl

/-- **The `sym32` element row (`0xB3`).** -/
theorem element_0xB3 {g : Nat} {c : Cursor} {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c')
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0xB3 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xB3 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xB3 : UInt8) =
      .ok (some ⟨179, some "sym32", Generated.Oasis.Category.variable, 4, "symbol",
        "up to 2^32 - 1 seven bit ASCII characters representing a symbolic value"⟩) := by decide
  rw [hd] at hed
  cases hed
  refine elementData_var
    (Step2S := fun n f => SpecAMQP.Spec.Codec.takeBytes n f >>= fun q =>
      SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2))
    (Step2R := fun b f' => SpecAMQP.Ref.takeBytes b f' >>= fun q =>
      SpecAMQP.Ref.decodeStringAt q.1 "symbol" q.2 >>= fun r => .ok (.symbol r.1, r.2))
    (hstep := (stepAgreesAll_takeBeEq 4 c c' hc))
    (h2 := fun a b hab => by
      rw [← hab]
      exact readersAgree_bind (stepAgreesAll_takeBytes a)
        (fun bytes bytes' hb => by
          subst hb
          exact readersAgree_utf8 "symbol" bytes (fun s => .symbol s) (fun s => .symbol s)
            (fun s => by simp only [BodiesAgree]))) ?_ ?_
  · intro x
    rw [(show specElementData g (some ⟨179, some "sym32", Generated.Oasis.Category.variable, 4,
        "symbol", "up to 2^32 - 1 seven bit ASCII characters representing a symbolic value"⟩) x =
        SpecAMQP.Spec.Codec.takeBe 4 x >>= fun p =>
          SpecAMQP.Spec.Codec.takeBytes p.1 p.2 >>= fun q =>
            SpecAMQP.Spec.Codec.utf8Of q.1 "symbol" >>= fun s => .ok (.symbol s, q.2) from rfl)]
  · intro x'
    simp only [SpecAMQP.Ref.readElement]
    rfl


/-- **The `list8` element row (`0xC0`).** -/
theorem element_0xC0 {g : Nat} (hup : WireAgreesUpTo g) {c : Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (hb : c.data.size - c.pos ≤ g) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0xC0 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xC0 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xC0 : UInt8) =
      .ok (some ⟨192, some "list8", Generated.Oasis.Category.compound, 1, "list",
        "up to 2^8 - 1 list elements with total size less than 2^8 octets"⟩) := by decide
  rw [hd] at hed
  cases hed
  unfold ElementDataAgrees
  rw [show specElementData g (some ⟨192, some "list8", Generated.Oasis.Category.compound, 1,
        "list", "up to 2^8 - 1 list elements with total size less than 2^8 octets"⟩) =
        SpecAMQP.Spec.Codec.readCompound g ⟨192, some "list8",
          Generated.Oasis.Category.compound, 1, "list",
          "up to 2^8 - 1 list elements with total size less than 2^8 octets"⟩ from rfl,
      show SpecAMQP.Ref.readElement (g + 1) (0xC0 : UInt8) = SpecAMQP.Ref.readCompound g 1 from
        funext (fun x' => by simp only [SpecAMQP.Ref.readElement])]
  exact readCompound_list_body g (wireAgreesUpTo_mono hup (by omega)) ⟨192, some "list8",
    Generated.Oasis.Category.compound, 1, "list",
    "up to 2^8 - 1 list elements with total size less than 2^8 octets"⟩ (by decide) rfl hc hb

/-- **The `map8` element row (`0xC1`).** -/
theorem element_0xC1 {g : Nat} (hup : WireAgreesUpTo g) {c : Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (hb : c.data.size - c.pos ≤ g) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0xC1 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xC1 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xC1 : UInt8) =
      .ok (some ⟨193, some "map8", Generated.Oasis.Category.compound, 1, "map",
        "up to 2^8 - 1 octets of encoded map data"⟩) := by decide
  rw [hd] at hed
  cases hed
  unfold ElementDataAgrees
  rw [show specElementData g (some ⟨193, some "map8", Generated.Oasis.Category.compound, 1,
        "map", "up to 2^8 - 1 octets of encoded map data"⟩) =
        SpecAMQP.Spec.Codec.readCompound g ⟨193, some "map8",
          Generated.Oasis.Category.compound, 1, "map",
          "up to 2^8 - 1 octets of encoded map data"⟩ from rfl,
      show SpecAMQP.Ref.readElement (g + 1) (0xC1 : UInt8) = SpecAMQP.Ref.readMap g 1 from
        funext (fun x' => by simp only [SpecAMQP.Ref.readElement])]
  exact readCompound_map_body g (wireAgreesUpTo_mono hup (by omega)) ⟨193, some "map8",
    Generated.Oasis.Category.compound, 1, "map",
    "up to 2^8 - 1 octets of encoded map data"⟩ (by decide) rfl hc hb

/-- **The `list32` element row (`0xD0`).** -/
theorem element_0xD0 {g : Nat} (hup : WireAgreesUpTo g) {c : Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (hb : c.data.size - c.pos ≤ g) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0xD0 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xD0 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xD0 : UInt8) =
      .ok (some ⟨208, some "list32", Generated.Oasis.Category.compound, 4, "list",
        "up to 2^32 - 1 list elements with total size less than 2^32 octets"⟩) := by decide
  rw [hd] at hed
  cases hed
  unfold ElementDataAgrees
  rw [show specElementData g (some ⟨208, some "list32", Generated.Oasis.Category.compound, 4,
        "list", "up to 2^32 - 1 list elements with total size less than 2^32 octets"⟩) =
        SpecAMQP.Spec.Codec.readCompound g ⟨208, some "list32",
          Generated.Oasis.Category.compound, 4, "list",
          "up to 2^32 - 1 list elements with total size less than 2^32 octets"⟩ from rfl,
      show SpecAMQP.Ref.readElement (g + 1) (0xD0 : UInt8) = SpecAMQP.Ref.readCompound g 4 from
        funext (fun x' => by simp only [SpecAMQP.Ref.readElement])]
  exact readCompound_list_body g (wireAgreesUpTo_mono hup (by omega)) ⟨208, some "list32",
    Generated.Oasis.Category.compound, 4, "list",
    "up to 2^32 - 1 list elements with total size less than 2^32 octets"⟩ (by decide) rfl hc hb

/-- **The `map32` element row (`0xD1`).** -/
theorem element_0xD1 {g : Nat} (hup : WireAgreesUpTo g) {c : Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (hb : c.data.size - c.pos ≤ g) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0xD1 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xD1 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xD1 : UInt8) =
      .ok (some ⟨209, some "map32", Generated.Oasis.Category.compound, 4, "map",
        "up to 2^32 - 1 octets of encoded map data"⟩) := by decide
  rw [hd] at hed
  cases hed
  unfold ElementDataAgrees
  rw [show specElementData g (some ⟨209, some "map32", Generated.Oasis.Category.compound, 4,
        "map", "up to 2^32 - 1 octets of encoded map data"⟩) =
        SpecAMQP.Spec.Codec.readCompound g ⟨209, some "map32",
          Generated.Oasis.Category.compound, 4, "map",
          "up to 2^32 - 1 octets of encoded map data"⟩ from rfl,
      show SpecAMQP.Ref.readElement (g + 1) (0xD1 : UInt8) = SpecAMQP.Ref.readMap g 4 from
        funext (fun x' => by simp only [SpecAMQP.Ref.readElement])]
  exact readCompound_map_body g (wireAgreesUpTo_mono hup (by omega)) ⟨209, some "map32",
    Generated.Oasis.Category.compound, 4, "map",
    "up to 2^32 - 1 octets of encoded map data"⟩ (by decide) rfl hc hb

/-- **The `array8` element row (`0xE0`).** -/
theorem element_0xE0 {g : Nat} (hdec : ElementsDecideBelow g) {c : Cursor}
    {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c') (hb : c.data.size - c.pos ≤ g)
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0xE0 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xE0 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xE0 : UInt8) =
      .ok (some ⟨224, some "array8", Generated.Oasis.Category.array, 1, "array",
        "up to 2^8 - 1 array elements with total size less than 2^8 octets"⟩) := by decide
  rw [hd] at hed
  cases hed
  unfold ElementDataAgrees
  rw [show specElementData g (some ⟨224, some "array8", Generated.Oasis.Category.array, 1,
        "array", "up to 2^8 - 1 array elements with total size less than 2^8 octets"⟩) =
        SpecAMQP.Spec.Codec.readArrayData g ⟨224, some "array8",
          Generated.Oasis.Category.array, 1, "array",
          "up to 2^8 - 1 array elements with total size less than 2^8 octets"⟩ from rfl,
      show SpecAMQP.Ref.readElement (g + 1) (0xE0 : UInt8) = SpecAMQP.Ref.readArray g 1 from
        funext (fun x' => by simp only [SpecAMQP.Ref.readElement])]
  exact readArray_body g hdec ⟨224, some "array8", Generated.Oasis.Category.array, 1, "array",
    "up to 2^8 - 1 array elements with total size less than 2^8 octets"⟩ (by decide) hc hb

/-- **The `array32` element row (`0xF0`).** -/
theorem element_0xF0 {g : Nat} (hdec : ElementsDecideBelow g) {c : Cursor}
    {c' : SpecAMQP.Ref.Cursor} (hc : CursorAgrees c c') (hb : c.data.size - c.pos ≤ g)
    {ed : Option EncodingDecl} (hed : SpecAMQP.Spec.Codec.elementDecl? (0xF0 : UInt8) = .ok ed) :
    ElementDataAgrees g (0xF0 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0xF0 : UInt8) =
      .ok (some ⟨240, some "array32", Generated.Oasis.Category.array, 4, "array",
        "up to 2^32 - 1 array elements with total size less than 2^32 octets"⟩) := by decide
  rw [hd] at hed
  cases hed
  unfold ElementDataAgrees
  rw [show specElementData g (some ⟨240, some "array32", Generated.Oasis.Category.array, 4,
        "array", "up to 2^32 - 1 array elements with total size less than 2^32 octets"⟩) =
        SpecAMQP.Spec.Codec.readArrayData g ⟨240, some "array32",
          Generated.Oasis.Category.array, 4, "array",
          "up to 2^32 - 1 array elements with total size less than 2^32 octets"⟩ from rfl,
      show SpecAMQP.Ref.readElement (g + 1) (0xF0 : UInt8) = SpecAMQP.Ref.readArray g 4 from
        funext (fun x' => by simp only [SpecAMQP.Ref.readElement])]
  exact readArray_body g hdec ⟨240, some "array32", Generated.Oasis.Category.array, 4, "array",
    "up to 2^32 - 1 array elements with total size less than 2^32 octets"⟩ (by decide) hc hb

/-! ## The descriptor prefix -/

/-- **The descriptor prefix (`0x00`).** An element under the prefix states its own descriptor and
value, so the decision is the value law twice: the descriptor first, then the value at the cursor the
first read left, exactly as `arm_0x00` reads the same two values behind the octet. -/
theorem element_0x00 {g : Nat} (ih : WireAgrees g) {c : Cursor} {c' : SpecAMQP.Ref.Cursor}
    (hc : CursorAgrees c c') (hb : c.data.size - c.pos ≤ g) {ed : Option EncodingDecl}
    (hed : SpecAMQP.Spec.Codec.elementDecl? (0x00 : UInt8) = .ok ed) :
    ElementDataAgrees g (0x00 : UInt8) ed c c' := by
  have hd : SpecAMQP.Spec.Codec.elementDecl? (0x00 : UInt8) = .ok (none : Option EncodingDecl) := by
    decide
  rw [hd] at hed
  cases hed
  have hS : specElementData g (none : Option EncodingDecl) c =
      (SpecAMQP.Spec.Codec.readValue g c >>= fun p =>
        (SpecAMQP.Spec.Codec.readValue g p.2) >>= fun q =>
          .ok (.described p.1 q.1, q.2)) := by
    simp only [specElementData, except_pure_ok]
  have hR : SpecAMQP.Ref.readElement (g + 1) (0x00 : UInt8) c' =
      (SpecAMQP.Ref.readValue g c' >>= fun p =>
        (SpecAMQP.Ref.readValue g p.2) >>= fun q =>
          .ok (.described p.1 q.1, q.2)) := by
    simp only [SpecAMQP.Ref.readElement, except_pure_ok]
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨⟨desc, d₂'⟩, h1, h⟩ := exists_of_bind_ok h
    try dsimp only at h
    obtain ⟨⟨val, d₃'⟩, h2, h⟩ := exists_of_bind_ok h
    try dsimp only at h
    obtain ⟨hother, hcur⟩ : .described desc val = other ∧ d₃' = c₂' := by
      have hp := Except.ok.inj h
      simpa only [Prod.mk.injEq] using hp
    subst hother
    subst hcur
    obtain ⟨sdesc, d₂, hs1, hc1, hdat1, hb1⟩ := (ih c c' hc hb).1 desc d₂' h1
    obtain ⟨sval, d₃, hs2, hc2, hdat2, hb2⟩ :=
      (ih d₂ d₂' hc1 (bound_of_read hs1 hdat1 hb)).1 val d₃' h2
    refine ⟨.described sdesc sval, d₃, ?_, ?_, hc2, ?_⟩
    · rw [hS, hs1, except_bind_ok, hs2, except_bind_ok]
    · unfold BodiesAgree
      exact ⟨hb1, hb2⟩
    · rw [hdat2, hdat1]
  · intro failure h
    rw [hR] at h
    cases h1 : SpecAMQP.Ref.readValue g c' with
    | error e =>
      rw [h1] at h
      rw [except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hspec, hcl⟩ := (ih c c' hc hb).2 e h1
      refine ⟨refusal, ?_, hcl⟩
      rw [hS, hspec, except_bind_error]
    | ok p =>
      obtain ⟨desc, d₂'⟩ := p
      rw [h1] at h
      rw [except_bind_ok] at h
      cases h2 : SpecAMQP.Ref.readValue g d₂' with
      | error e =>
        rw [h2] at h
        rw [except_bind_error] at h
        simp only [Except.error.injEq] at h
        subst h
        obtain ⟨sdesc, d₂, hs1, hc1, hdat1, -⟩ := (ih c c' hc hb).1 desc d₂' h1
        obtain ⟨refusal, hspec, hcl⟩ :=
          (ih d₂ d₂' hc1 (bound_of_read hs1 hdat1 hb)).2 e h2
        refine ⟨refusal, ?_, hcl⟩
        rw [hS, hs1, except_bind_ok, hspec, except_bind_error]
      | ok q =>
        rw [h2] at h
        rw [except_bind_ok] at h
        exact absurd h (by simp)


/-! ## The element decision, dispatched over the constructor octets -/

/-- The constructor octets an array's element can name: the descriptor prefix, and every octet the
declared surface assigns. A successor who adds a row to the table must add it here as well, which the
sweep below makes fail rather than pass silently. -/
def elementCtors : List UInt8 :=
  [0x00, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x60, 0x61, 0x70, 0x71, 0x72, 0x73, 0x74, 0x80, 0x81, 0x82, 0x83, 0x84, 0x94, 0x98, 0xA0, 0xA1, 0xA3, 0xB0, 0xB1, 0xB3, 0xC0, 0xC1, 0xD0, 0xD1, 0xE0, 0xF0]

set_option maxRecDepth 10000 in
/-- **Every octet the element lookup refuses is outside the list, and the descriptor prefix is
inside.** One finite evaluation of the lookup over all 256 octets. -/
theorem elementCtors_sweep :
    (List.range 256).all (fun n =>
      !(SpecAMQP.Spec.Codec.elementDecl? (UInt8.ofNat n)).isOk
        || elementCtors.contains (UInt8.ofNat n)) = true := by
  decide

/-- The sweep as a membership: an octet the element lookup accepts is one of the list's. -/
theorem elementDecl?_ctor_mem {ctor : UInt8}
    (h : (SpecAMQP.Spec.Codec.elementDecl? ctor).isOk = true) : ctor ∈ elementCtors := by
  have hall := List.all_eq_true.mp elementCtors_sweep ctor.toNat (List.mem_range.mpr ctor.toNat_lt)
  have hof : UInt8.ofNat ctor.toNat = ctor := by
    apply UInt8.toNat_inj.mp
    simp
  rw [hof] at hall
  simpa only [h, Bool.not_true, Bool.false_or, List.contains_iff_mem] using hall

/-- **The element decision, at every fuel the value law reaches.** The decision's rows are the value
law's own material: the four container rows are the compound and array bodies at the fuel the octet
handed down, the descriptor prefix is the value law twice, and the rest read a declared row's data
against the reference's own literal arm. The fuel family is an argument rather than something read off
the value law because the array's own row needs it, and nothing else in the dispatch does. -/
theorem elementsDecideAt_of_upTo {g : Nat} (hup : WireAgreesUpTo g) (hdec : ElementsDecideBelow g) :
    ElementsDecideAt g := by
  intro ctor ed hed c c' hc hpos hb
  have hmem : ctor ∈ elementCtors :=
    elementDecl?_ctor_mem (by rw [hed]; rfl)
  simp only [elementCtors, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact element_0x00 (g := g) (ih := wireAgreesUpTo_self hup) (c := c) (c' := c')
      (hc := hc) (hb := hb) (ed := ed) (hed := hed)
  ·
    exact element_0x40 (g := g) (c := c) (c' := c') (hc := hc) (hpos := hpos)
      (ed := ed) (hed := hed)
  ·
    exact element_0x41 (g := g) (c := c) (c' := c') (hc := hc) (hpos := hpos)
      (ed := ed) (hed := hed)
  ·
    exact element_0x42 (g := g) (c := c) (c' := c') (hc := hc) (hpos := hpos)
      (ed := ed) (hed := hed)
  ·
    exact element_0x43 (g := g) (c := c) (c' := c') (hc := hc) (hpos := hpos)
      (ed := ed) (hed := hed)
  ·
    exact element_0x44 (g := g) (c := c) (c' := c') (hc := hc) (hpos := hpos)
      (ed := ed) (hed := hed)
  ·
    exact element_0x45 (g := g) (c := c) (c' := c') (hc := hc) (hpos := hpos)
      (ed := ed) (hed := hed)
  ·
    exact element_0x50 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x51 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0x52 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x53 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x54 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0x55 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0x56 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x60 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x61 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0x70 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x71 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0x72 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x73 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x74 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x80 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x81 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0x82 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x83 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0x84 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x94 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0x98 (g := g) (c := c) (c' := c') (hc := hc)
      (ed := ed) (hed := hed)
  ·
    exact element_0xA0 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0xA1 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0xA3 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0xB0 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0xB1 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0xB3 (g := g) (c := c) (c' := c') (hc := hc) (ed := ed) (hed := hed)
  ·
    exact element_0xC0 (g := g) (hup := hup) (c := c) (c' := c') (hc := hc)
      (hb := hb) (ed := ed) (hed := hed)
  ·
    exact element_0xC1 (g := g) (hup := hup) (c := c) (c' := c') (hc := hc)
      (hb := hb) (ed := ed) (hed := hed)
  ·
    exact element_0xD0 (g := g) (hup := hup) (c := c) (c' := c') (hc := hc)
      (hb := hb) (ed := ed) (hed := hed)
  ·
    exact element_0xD1 (g := g) (hup := hup) (c := c) (c' := c') (hc := hc)
      (hb := hb) (ed := ed) (hed := hed)
  ·
    exact element_0xE0 (g := g) (hdec := hdec) (c := c) (c' := c') (hc := hc)
      (hb := hb) (ed := ed) (hed := hed)
  ·
    exact element_0xF0 (g := g) (hdec := hdec) (c := c) (c' := c') (hc := hc)
      (hb := hb) (ed := ed) (hed := hed)


/-- **The `array8` value row (`0xE0`).** The specification's `readValue` resolves the octet to the
table's one-octet array row and hands its cursor to `readArrayData`; the reference matches the octet
and reads at width one. Both are the array body at the fuel the octet handed down, which is what
`readArray_body` relates — and the body is where the elements' one-fuel offset lives, so it takes the
element decision *below* that fuel as the hypothesis the induction discharges. -/
theorem arm_0xE0 (fuel : Nat) (hdec : ElementsDecideBelow fuel) (c : SpecAMQP.Spec.Codec.Cursor)
    (c' : SpecAMQP.Ref.Cursor) (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor)
    (hd : CursorAgrees d d') (hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xE0, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xE0, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0xE0 : UInt8).toNat = .array 1 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xE0 : UInt8) =
      .ok ⟨224, some "array8", Generated.Oasis.Category.array, 1, "array",
        "up to 2^8 - 1 array elements with total size less than 2^8 octets"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.readArrayData fuel ⟨224, some "array8",
        Generated.Oasis.Category.array, 1, "array",
        "up to 2^8 - 1 array elements with total size less than 2^8 octets"⟩ d := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = SpecAMQP.Ref.readArray fuel 1 d' := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  obtain ⟨hok, herr⟩ := readArray_body fuel hdec ⟨224, some "array8",
    Generated.Oasis.Category.array, 1, "array",
    "up to 2^8 - 1 array elements with total size less than 2^8 octets"⟩ (by decide) hd hb
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨body, c₂, hf, hba, hcd, hdat⟩ := hok other c₂' h
    exact ⟨body, c₂, by rw [hS]; exact hf, hcd, by rw [hdat, hdata], hba⟩
  · intro failure h
    rw [hR] at h
    obtain ⟨refusal, hf, hcl⟩ := herr failure h
    exact ⟨refusal, by rw [hS]; exact hf, hcl⟩

/-- **The `array32` value row (`0xF0`).** The same body behind a four-octet array row. -/
theorem arm_0xF0 (fuel : Nat) (hdec : ElementsDecideBelow fuel) (c : SpecAMQP.Spec.Codec.Cursor)
    (c' : SpecAMQP.Ref.Cursor) (d : SpecAMQP.Spec.Codec.Cursor) (d' : SpecAMQP.Ref.Cursor)
    (hd : CursorAgrees d d') (hb : d.data.size - d.pos ≤ fuel)
    (hs : SpecAMQP.Spec.Codec.takeU8 c = .ok (0xF0, d))
    (hr : SpecAMQP.Ref.takeU8 c' = .ok (0xF0, d')) :
    StepAgrees (fuel + 1) c c' := by
  have hdata : d.data = c.data := spec_takeU8_data hs
  have hclass : SpecAMQP.Spec.Value.classify (0xF0 : UInt8).toNat = .array 4 := by decide
  have hdecl : SpecAMQP.Spec.Codec.dataDecl (0xF0 : UInt8) =
      .ok ⟨240, some "array32", Generated.Oasis.Category.array, 4, "array",
        "up to 2^32 - 1 array elements with total size less than 2^32 octets"⟩ := by decide
  have hS : SpecAMQP.Spec.Codec.readValue (fuel + 1) c =
      SpecAMQP.Spec.Codec.readArrayData fuel ⟨240, some "array32",
        Generated.Oasis.Category.array, 4, "array",
        "up to 2^32 - 1 array elements with total size less than 2^32 octets"⟩ d := by
    simp only [SpecAMQP.Spec.Codec.readValue]
    rw [hs, except_bind_ok, hclass, hdecl, except_bind_ok]
  have hR : SpecAMQP.Ref.readValue (fuel + 1) c' = SpecAMQP.Ref.readArray fuel 4 d' := by
    simp only [SpecAMQP.Ref.readValue]
    rw [hr, except_bind_ok]
    rfl
  obtain ⟨hok, herr⟩ := readArray_body fuel hdec ⟨240, some "array32",
    Generated.Oasis.Category.array, 4, "array",
    "up to 2^32 - 1 array elements with total size less than 2^32 octets"⟩ (by decide) hd hb
  constructor
  · intro other c₂' h
    rw [hR] at h
    obtain ⟨body, c₂, hf, hba, hcd, hdat⟩ := hok other c₂' h
    exact ⟨body, c₂, by rw [hS]; exact hf, hcd, by rw [hdat, hdata], hba⟩
  · intro failure h
    rw [hR] at h
    obtain ⟨refusal, hf, hcl⟩ := herr failure h
    exact ⟨refusal, by rw [hS]; exact hf, hcl⟩


/-! ## The value law's dispatch

The forty value-level arms are one per constructor octet, so the step of the fuel induction is a
dispatch over the octets the reference's reader assigns: an assigned octet is one of forty literals and
is the arm's own hypothesis, and an octet the declared surface does not assign is refused on both
sides in the same class. The list below is the same forty octets the element dispatch uses; the sweep
reads the *reference's* own test, which is what the refusal family is stated against. -/

/-- The constructor octets the reference's value reader assigns: the descriptor prefix and every
octet the declared surface holds a row for. -/
def wireCtors : List UInt8 :=
  [0x00, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x60, 0x61, 0x70, 0x71, 0x72, 0x73, 0x74, 0x80, 0x81, 0x82, 0x83, 0x84, 0x94, 0x98, 0xA0, 0xA1, 0xA3, 0xB0, 0xB1, 0xB3, 0xC0, 0xC1, 0xD0, 0xD1, 0xE0, 0xF0]

set_option maxRecDepth 10000 in
/-- **Every octet the reference does not accept as a constructor is outside the list.** One finite
evaluation of the reference's own test over all 256 octets. -/
theorem wireCtors_sweep :
    (List.range 256).all (fun n =>
      wireCtors.contains (UInt8.ofNat n)
        || !(SpecAMQP.Ref.assignedConstructor (UInt8.ofNat n))) = true := by
  decide

/-- The sweep as a fact about one octet: outside the list, the reference's test is false. -/
theorem assignedConstructor_false_of_not_mem {code : UInt8} (h : code ∉ wireCtors) :
    SpecAMQP.Ref.assignedConstructor code = false := by
  have hall := List.all_eq_true.mp wireCtors_sweep code.toNat (List.mem_range.mpr code.toNat_lt)
  have hof : UInt8.ofNat code.toNat = code := by
    apply UInt8.toNat_inj.mp
    simp
  rw [hof] at hall
  have hc : wireCtors.contains code = false := by
    cases hcon : wireCtors.contains code with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.mp hcon) h
  rw [hc, Bool.false_or] at hall
  simpa using hall

/-- **The step of the fuel induction.** At one fuel more than the invariant reaches, the readers agree:
the octet is taken on both sides (`takeU8_agrees`, or `takeU8_fails` when one side runs out), and then
the octet's own arm — one of the forty landed arms — is the whole of the value, with the element
decision below the fuel for the two array rows and the value law below for the four container rows and
the descriptor prefix. -/
theorem wireAgrees_succ (K : Nat) (hup : WireAgreesUpTo K) (hdec : ElementsDecideBelow K) :
    WireAgrees (K + 1) := by
  intro c c' hc hb
  cases hr : SpecAMQP.Ref.takeU8 c' with
  | error e =>
    constructor
    · intro other c₂' h
      simp only [SpecAMQP.Ref.readValue] at h
      rw [hr, except_bind_error] at h
      exact absurd h (by simp)
    · intro failure h
      simp only [SpecAMQP.Ref.readValue] at h
      rw [hr, except_bind_error] at h
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨refusal, hsU8, hcl⟩ := takeU8_fails hc e hr
      refine ⟨refusal, ?_, hcl⟩
      simp only [SpecAMQP.Spec.Codec.readValue]
      rw [hsU8, except_bind_error]
  | ok p =>
    obtain ⟨code, d'⟩ := p
    obtain ⟨d, hs, hcd⟩ := takeU8_agrees hc code d' hr
    have hb' : d.data.size - d.pos ≤ K := by
      rw [spec_takeU8_data hs, spec_takeU8_pos hs]
      omega
    by_cases hmem : code ∈ wireCtors
    · simp only [wireCtors, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact arm_0x00 K (wireAgreesUpTo_self hup) c c' d d' hcd hb' hs hr
      · exact arm_0x40 K c c' d d' hcd hb' hs hr
      · exact arm_0x41 K c c' d d' hcd hb' hs hr
      · exact arm_0x42 K c c' d d' hcd hb' hs hr
      · exact arm_0x43 K c c' d d' hcd hb' hs hr
      · exact arm_0x44 K c c' d d' hcd hb' hs hr
      · exact arm_0x45 K c c' d d' hcd hb' hs hr
      · exact arm_0x50 K c c' d d' hcd hb' hs hr
      · exact arm_0x51 K c c' d d' hcd hb' hs hr
      · exact arm_0x52 K c c' d d' hcd hb' hs hr
      · exact arm_0x53 K c c' d d' hcd hb' hs hr
      · exact arm_0x54 K c c' d d' hcd hb' hs hr
      · exact arm_0x55 K c c' d d' hcd hb' hs hr
      · exact arm_0x56 K c c' d d' hcd hb' hs hr
      · exact arm_0x60 K c c' d d' hcd hb' hs hr
      · exact arm_0x61 K c c' d d' hcd hb' hs hr
      · exact arm_0x70 K c c' d d' hcd hb' hs hr
      · exact arm_0x71 K c c' d d' hcd hb' hs hr
      · exact arm_0x72 K c c' d d' hcd hb' hs hr
      · exact arm_0x73 K c c' d d' hcd hb' hs hr
      · exact arm_0x74 K c c' d d' hcd hb' hs hr
      · exact arm_0x80 K c c' d d' hcd hb' hs hr
      · exact arm_0x81 K c c' d d' hcd hb' hs hr
      · exact arm_0x82 K c c' d d' hcd hb' hs hr
      · exact arm_0x83 K c c' d d' hcd hb' hs hr
      · exact arm_0x84 K c c' d d' hcd hb' hs hr
      · exact arm_0x94 K c c' d d' hcd hb' hs hr
      · exact arm_0x98 K c c' d d' hcd hb' hs hr
      · exact arm_0xA0 K c c' d d' hcd hb' hs hr
      · exact arm_0xA1 K c c' d d' hcd hb' hs hr
      · exact arm_0xA3 K c c' d d' hcd hb' hs hr
      · exact arm_0xB0 K c c' d d' hcd hb' hs hr
      · exact arm_0xB1 K c c' d d' hcd hb' hs hr
      · exact arm_0xB3 K c c' d d' hcd hb' hs hr
      · exact arm_0xC0 K (wireAgreesUpTo_mono hup (by omega)) c c' d d' hcd hb' hs hr
      · exact arm_0xC1 K (wireAgreesUpTo_mono hup (by omega)) c c' d d' hcd hb' hs hr
      · exact arm_0xD0 K (wireAgreesUpTo_mono hup (by omega)) c c' d d' hcd hb' hs hr
      · exact arm_0xD1 K (wireAgreesUpTo_mono hup (by omega)) c c' d d' hcd hb' hs hr
      · exact arm_0xE0 K hdec c c' d d' hcd hb' hs hr
      · exact arm_0xF0 K hdec c c' d d' hcd hb' hs hr
    · have hass : SpecAMQP.Ref.assignedConstructor code = false :=
        assignedConstructor_false_of_not_mem hmem
      have hne : code ≠ 0x00 := by
        intro h0
        exact hmem (by rw [h0]; decide)
      constructor
      · intro other c₂' h
        rw [ref_readValue_unassigned K c' code d' hr hass] at h
        exact absurd h (by simp)
      · intro failure h
        rw [ref_readValue_unassigned K c' code d' hr hass] at h
        injection h with hf
        subst hf
        obtain ⟨r, hspec, hcl⟩ :=
          spec_readValue_unassigned K c code d hs (encodingOf_none_of_not_assigned hass) hne
        exact ⟨r, hspec, by rw [hcl]; rfl⟩


/-! ## The joint induction, and the entry point -/

/-- **The invariant of one induction.** The value law at every fuel up to `n`, together with the
element decision at every fuel below `n`.

The two are *not* provable separately, which is the thing a successor needs to know before trying: the
four container element rows are the compound and array bodies, so `ElementsDecideAt k` needs the value
law at the fuels beneath `k`, and the two array arms of the value law need `ElementsDecideBelow k`,
which is the same decision family one fuel down. One induction over the pair closes both, and the
reading of each half off the pair is what `wireAgrees_all` and `elementsDecideBelow_all` below do. -/
theorem wireInvariant : ∀ n : Nat, WireAgreesUpTo n ∧ ElementsDecideBelow n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact wireAgrees_zero
    · intro k hk
      exact absurd hk (by omega)
  | succ m ih =>
    have hdec : ElementsDecideBelow (m + 1) := by
      intro k hk
      exact elementsDecideAt_of_upTo (wireAgreesUpTo_mono ih.1 (by omega))
        (fun j hj => ih.2 j (by omega))
    have hw : WireAgrees (m + 1) := wireAgrees_succ m ih.1 ih.2
    refine ⟨?_, hdec⟩
    intro k hk
    by_cases hkm : k ≤ m
    · exact ih.1 k hkm
    · have hk1 : k = m + 1 := by omega
      subst hk1
      exact hw

/-- **The value law at every fuel.** Read off the joint invariant at its own top. -/
theorem wireAgrees_all (n : Nat) : WireAgrees n := (wireInvariant n).1 n le_rfl

/-- **The element decision at every fuel below `n`**, the hypothesis `elementsLoop_agrees` and
`readArray_body` take. -/
theorem elementsDecideBelow_all (n : Nat) : ElementsDecideBelow n := (wireInvariant n).2

/-- **The element decision at one fuel**, the named hypothesis discharged. -/
theorem elementsDecideAt_all (g : Nat) : ElementsDecideAt g :=
  elementsDecideBelow_all (g + 1) g (by omega)

/-- **The value layer's reader agreement, in the contract's own vocabulary.** The wire law at
`fuel = region.size` and the initial cursors — `region.size - 0 ≤ region.size` is the octet bound's
base case, and the two initial cursors are the same buffer at the same position — with the
`BodiesAgree` the law carries turned into the *view* equality the contract states by
`bodyView_of_BodiesAgree`, and the consumed cursor read off the two readers' own entry points. -/
theorem valueLayersAgree : ValueLayersAgree := by
  intro region
  have h := wireAgrees_all region.size ⟨region, 0⟩ ⟨region, 0⟩ ⟨rfl, rfl⟩ (by simp)
  constructor
  · intro other used hd
    unfold SpecAMQP.Ref.decode at hd
    cases hrv : SpecAMQP.Ref.readValue region.size ⟨region, 0⟩ with
    | error e =>
      rw [hrv] at hd
      exact absurd hd (by simp)
    | ok p =>
      obtain ⟨v, cx⟩ := p
      rw [hrv] at hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hd
      obtain ⟨hother, hused⟩ := hd
      subst hother
      subst hused
      obtain ⟨body, c₂, hspec, hcd, -, hba⟩ := h.1 v cx hrv
      refine ⟨body, ?_, bodyView_of_BodiesAgree hba⟩
      unfold SpecAMQP.Spec.Codec.decodeValue
      rw [hspec]
      simp only [hcd.2]
  · intro failure hd
    unfold SpecAMQP.Ref.decode at hd
    cases hrv : SpecAMQP.Ref.readValue region.size ⟨region, 0⟩ with
    | error e =>
      rw [hrv] at hd
      simp only [Except.error.injEq] at hd
      subst hd
      obtain ⟨refusal, hspec, hcl⟩ := h.2 e hrv
      refine ⟨refusal, ?_, hcl⟩
      unfold SpecAMQP.Spec.Codec.decodeValue
      rw [hspec]
    | ok p =>
      rw [hrv] at hd
      exact absurd hd (by simp)


end SpecAMQP.Proofs
