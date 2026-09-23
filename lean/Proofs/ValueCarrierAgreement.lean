import Proofs.FrameSendConformance
import Ref.Vectors

open Lean (Json)

/-!
# The corpus-vocabulary readers, clause by clause

`FrameSendConformance.ValueCarrierAgree` is the value layer's claim in the corpus vocabulary: a
value the reference's carrier reads is one the specification's also reads, and the two readings
agree as values. This module is its proof, one clause at a time, and it is **in progress**: the
three clauses below are proved, and the remaining twenty-two are the work this module exists for.

## Why clause by clause, and why the discriminant is a hypothesis

The two readers ask the same questions of the same `Json` — the same keys, through the same
`getObjValAs?`/`getObjVal?` helpers — and dispatched the same twenty-five clauses in **different
orders**:

```text
Spec.Codec.valueOfJson   null boolean ubyte ushort uint ulong byte short int long
                         float double decimal32 decimal64 decimal128 char timestamp uuid
                         binary string symbol list array described map
Ref.Vectors.valueOfJson  null boolean ubyte ushort uint ulong byte short int long
                         char timestamp float double decimal32 decimal64 decimal128 uuid
                         string symbol binary list map array described
```

(`PLAN.md` §10 records that as a fact about two independently authored artefacts, and one no
differential could surface, since the same clauses in another order give the same answers.) A
single `split` on both dispatches would therefore pair `float` with `char` and every later branch
with the wrong clause. Taking the **discriminant as a hypothesis** — `json.getObjValAs? String
"type" = .ok "k"` — makes each clause's own `match` reduce against a *literal* on both sides, and
then one `simp only [hk] at h ⊢` collapses both dispatches at once; the ordering question never
arises inside a clause, and the dispatcher carries it once.

## What a clause proof looks like

Three steps, and the third is the only one that knows anything about the type:

1. `unfold` both readers and expand the binds (`simp only [Bind.bind, Except.bind]`);
2. `simp only [hk] at h ⊢` — which reduces *both* `match kind with` trees to the clause for `k`;
3. the clause's own shared reads, as `cases` on the `Json` accessor, with the reference's success
   (`h`) deciding every branch; the specification's answer is then constructed, and the
   `BodiesAgree` obligation discharged by `simp only [BodiesAgree]` — it is a recursive `Prop` and
   does *not* reduce to `True` definitionally, so `trivial` does not typecheck where `simp` will.

The integer clauses add the arithmetic the two value types need (`BodiesAgree` compares a `Nat`
against a `UInt8`/`UInt32`/…, or an `Int` against the bound-checked `Int8`/`Int16`/…); the
compound clauses (`list`, `map`, `array`, `described`) add recursion, at the fuel the reader hands
down, through `List.mapM` for the items and a pair-level analogue for a map's.
-/

namespace SpecAMQP.Proofs

open SpecAMQP

/-- **The `"null"` clause.** Both readers answer the value with no further read. -/
theorem carrier_clause_null (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "null") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨.null, rfl, by simp only [BodiesAgree]⟩

/-- **The `"boolean"` clause.** One shared read, `value`, and the two readings are the same
boolean. -/
theorem carrier_clause_boolean (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "boolean") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases hb : json.getObjValAs? Bool "value" with
  | error err => simp [hb] at h
  | ok b =>
    simp only [hb] at h ⊢
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨.boolean b, rfl, by simp only [BodiesAgree]⟩

/-- **The `"string"` clause.** One shared read, `text`, and `BodiesAgree`'s `.string` case is
equality of the two strings. -/
theorem carrier_clause_string (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "string") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases ht : json.getObjValAs? String "text" with
  | error err => simp [ht] at h
  | ok text =>
    simp only [ht] at h ⊢
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨.string text, rfl, by simp only [BodiesAgree]⟩

end SpecAMQP.Proofs
