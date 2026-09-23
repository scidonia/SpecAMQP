import Proofs.FrameSendConformance
import Ref.Vectors

open Lean (Json)

/-!
# The corpus-vocabulary readers, clause by clause

`FrameSendConformance.ValueCarrierAgree` is the value layer's claim in the corpus vocabulary: a
value the reference's carrier reads is one the specification's also reads, and the two readings
agree as values. This module is its proof, one clause at a time, and it is **in progress**: twenty
of the twenty-five clauses are proved, in five families —

* the structured scalars `null`, `boolean`, `string`, `symbol`;
* the octet payloads `binary`, `float`, `double`, `decimal32`, `decimal64`, `decimal128`, `uuid`;
* the unsigned widths `ubyte`, `ushort`, `uint`, `ulong`;
* the signed widths `byte`, `short`, `int`, `long`, and `timestamp`;

and the remaining five are `char` and the four compounds `list`, `map`, `array`, `described`.
The route to each is named at the end of this header. What is *not* yet done is the join: the
statement is at fuel 64 (`Ref.Vectors.valueOfJson 64 json = .ok other → ∃ body, …`), while every
clause here is at `valueOfJson (fuel + 1)` with the discriminant as a hypothesis, so discharging it
needs a 25-way case on the kind, the extraction of the discriminant equality from the reference's
own success, and the instantiation at fuel 63.

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

## The unsigned clauses: two bridges and one round trip

Three facts carry every unsigned width, and they are stated below rather than inlined so the next
clause costs three lines:

* `unsignedOf_eq` — the two readers' range-check helpers are *one function written twice*, so a
  clause can `rw [← unsignedOf_eq]` and case on a single call, reading the answer off both sides;
* `unsignedOf_le` — the width bound the reference's check enforces, read off its own success;
  without it the round trip is not an identity;
* `uN_toNat` — `(n.toUIntN).toNat = n` for `n < 2^N`, which is `UIntN.toNat_ofNat_of_lt` with the
  size goal discharged (`show n < 2 ^ N; omega`).

`BodiesAgree`'s unsigned case compares the *specification's* `Nat` against the reference's carrier,
so the identity is used at `.symm`.

Two shapes of the reference's answers appear in the clauses and they do not take the same proof:
some branches are written `.ok v` and some `return v`, the latter leaving a `pure`, so
`simp only [Except.ok.injEq] at h` **makes no progress** on those. `injection h with hb` handles
both, and is what the symbol, binary and unsigned-widest clauses use.

## The octet payloads: one bridge each, and a rewrite detail

`float`, `double`, the three decimals and `uuid` read a fixed-width opaque payload through two
differently named helpers — the specification's `hexPayloadOf`, the reference's `fixedHex` — which
do the same reads and the same width check and differ only in the failure text. They are therefore
related by `fixedHex_ok_hexPayloadOf`, a one-directional agreement on the success path, rather
than by an equality of functions. The two payload types are two abbreviations of `Array UInt8`
(`Harness.Octets` and `Ref.Octets`), so the bridge names the reference's spelling.

The clause then reads

```lean
have hspec : SpecAMQP.Spec.Codec.hexPayloadOf json 4 "float" = .ok bytes :=
  fixedHex_ok_hexPayloadOf json 4 "float" bytes hf
simp only [hf, hspec] at h ⊢
```

— a *local hypothesis* used as the rewrite rule, because `simp only`'s argument list takes
identifiers and not applied terms.

## The signed widths: what the route needed

Each signed clause is a bound-checked shared read (`signedOf`) plus the reference's width-carrying
carrier read back to the specification's `Int`. Three moves, and two of them are core-only
corrections worth naming because the obvious spellings are Mathlib's and do not exist here:

* `signedOf_range` reads the bounds off the reference's own success, the way `unsignedOf_le` does
  for the unsigned widths. Note that `cases … ` must be *followed* by `simp only [hv] at h`; on
  its own the `cases` does not rewrite the hypothesis.
* the round trip: `BitVec.toInt_ofNat'` turns
  `(IntN.ofBitVec (BitVec.ofNat N x)).toInt` into an `Int.bmod`, `Int.bmod_eq_iff` turns that into
  the two range facts plus the divisibility, and `Int.emod_add_mul_ediv` supplies the divisibility.
  `norm_num` and `ring` are Mathlib and are not available; `decide` and `omega` replace them.
* `BodiesAgree`'s signed case compares the *specification's* `Int` on the left, so the round trip is
  used at `.symm` — as in the unsigned clauses.

`timestamp` is the exception that carries a read agreement: the reference range-checks
`"milliseconds"` through `boundedField` where the specification reads it bare, so the clause needs
`boundedField_ok_getObjValAs` (a successful bounded read *is* a read of that key) and
`boundedField_range`. Its failure branch closes with `simp_all` and not with a named hypothesis,
because the two branches of the reader spell the bounds differently — symbolically in one,
numerically in the other — and a closer that depends on the spelling is a closer that breaks.

## What remains, and the route to it

* **`char`** — the same round trip as `ubyte`, at 1114111, but *not* on the same read: the
  specification reads `getObjValAs? Nat "codepoint"` through `codePointOf`, the reference reads
  `boundedField json "codepoint" 0 1114111` through `getObjValAs? Int`. The disagreement is in the
  *accessor*, so the clause needs a bridge whose exact goal is

  ```lean
  theorem getObjValAs_nat_of_int (json : Json) (key : String) (i : Int) (h0 : 0 ≤ i)
      (h : json.getObjValAs? Int key = .ok i) : json.getObjValAs? Nat key = .ok i.toNat
  ```

  Through the instances (`FromJson Nat := ⟨Json.getNat?⟩`, `FromJson Int := ⟨Json.getInt?⟩`, both
  in `Lean/Data/Json/FromToJson/Basic.lean`) this reduces to the *number* layer: from
  `n.toInt? = some i` and `0 ≤ i`, `n.toNat? = some i.toNat` for `n : JsonNumber`
  (`Lean/Data/Json/Basic.lean`). That is where the work is, and it is not in this repository's
  imports - so `char` is blocked on a `JsonNumber` lemma rather than on any AMQP content. It is
  also worth the planner's eye as a *fact about the two artefacts*: the specification accepts a
  code point written as a JSON natural, the reference as a JSON integer, and the corpus writes
  them as naturals, which is why no differential sees the difference.
* **The four compounds** — `list`, `map`, `array`, `described` — where the recursion's fuel and the
  item reads are the work, and where `BodiesAgree` recurses (`BodiesAgreeList`, `BodiesAgreePairs`,
  and the constructor pair for `array`).
* **Then the joint development**: prefix determinism and fuel monotonicity, which is what lets
  the clause lemmas be joined into one `valueOfJson` agreement over all buffers rather than
  re-derived per `Json`. `ValueLayersAgree` (`Proofs/ValueLayerLaws`) needs the same treatment on
  the wire-reading side.
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

/-! ## The numeric helpers the scalar clauses need -/

/-- `n` below 2^8 read back from its `UInt8` spelling: the reference's value domain is
width-carrying where the specification's is not, so `BodiesAgree` compares a `Nat` against the
unsigned round trip of one. -/
theorem u8_toNat (n : Nat) (h : n < 2 ^ 8) : (n.toUInt8).toNat = n :=
  UInt8.toNat_ofNat_of_lt (n := n) h

theorem u16_toNat (n : Nat) (h : n < 2 ^ 16) : (n.toUInt16).toNat = n :=
  UInt16.toNat_ofNat_of_lt (n := n) h

theorem u32_toNat (n : Nat) (h : n < 2 ^ 32) : (n.toUInt32).toNat = n :=
  UInt32.toNat_ofNat_of_lt (n := n) h

theorem u64_toNat (n : Nat) (h : n < 2 ^ 64) : (n.toUInt64).toNat = n :=
  UInt64.toNat_ofNat_of_lt (n := n) h

/-- The bound the reference's unsigned range check enforces, read off its own success: the answer
a successful `unsignedOf` gives is within the width it was asked for, which is what makes the
`UInt` round trip an identity. -/
theorem unsignedOf_le (json : Json) (bound : Nat) (n : Nat)
    (h : SpecAMQP.Ref.Vectors.unsignedOf json bound = .ok n) : n ≤ bound := by
  unfold SpecAMQP.Ref.Vectors.unsignedOf at h
  simp only [Bind.bind, Except.bind] at h
  cases hv : json.getObjValAs? Nat "value" with
  | error err => simp [hv] at h
  | ok v =>
    simp only [hv] at h
    split at h
    · rename_i hle
      injection h with hb
      subst hb
      exact hle
    · simp at h

/-- The two readers' range-check helpers are one function written twice, so a clause can case on
one call and read the answer off both. -/
theorem unsignedOf_eq : SpecAMQP.Ref.Vectors.unsignedOf = SpecAMQP.Harness.unsignedOf := rfl

theorem signedOf_eq : SpecAMQP.Ref.Vectors.signedOf = SpecAMQP.Harness.signedOf := rfl

/-- **The `"symbol"` clause**, on the same read as `"string"`. -/
theorem carrier_clause_symbol (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "symbol") (other : SpecAMQP.Ref.Value)
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
    injection h with hb
    subst hb
    exact ⟨.symbol text, rfl, by simp only [BodiesAgree]⟩

/-- **The `"binary"` clause.** Both read the same hex, one as octets and one as a list;
`BodiesAgree`'s `.binary` case is `a.toList = b`, which is what the two spellings of one
`ofHex` give. -/
theorem carrier_clause_binary (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "binary") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases hs : json.getObjValAs? String "hex" with
  | error err => simp [hs] at h
  | ok hex =>
    simp only [hs] at h ⊢
    cases hx : SpecAMQP.Harness.ofHex hex with
    | error err => simp [hx] at h
    | ok bytes =>
      simp only [hx] at h ⊢
      injection h with hb
      subst hb
      exact ⟨.binary bytes, rfl, by simp only [BodiesAgree]⟩

/-- **The `"ubyte"` clause.** One shared read through the two spellings of `unsignedOf`; the
bound the answer carries is what makes the round trip an identity. -/
theorem carrier_clause_ubyte (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "ubyte") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  rw [← unsignedOf_eq] at ⊢
  cases hu : SpecAMQP.Ref.Vectors.unsignedOf json 255 with
  | error err => simp [hu] at h
  | ok n =>
    simp only [hu] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.ubyte n, rfl,
      by simp only [BodiesAgree]; exact (u8_toNat n (by have := unsignedOf_le json 255 n hu; omega)).symm⟩

/-- **The `"ushort"` clause.** The same shared read and the same width-carrying round trip as
`"ubyte"`, at 65535. -/
theorem carrier_clause_ushort (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "ushort") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  rw [← unsignedOf_eq] at ⊢
  cases hu : SpecAMQP.Ref.Vectors.unsignedOf json 65535 with
  | error err => simp [hu] at h
  | ok n =>
    simp only [hu] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.ushort n, rfl,
      by simp only [BodiesAgree];
         exact (u16_toNat n (by have := unsignedOf_le json 65535 n hu; omega)).symm⟩

/-- **The `"uint"` clause.** The same shared read and the same width-carrying round trip as
`"ubyte"`, at 4294967295. -/
theorem carrier_clause_uint (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "uint") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  rw [← unsignedOf_eq] at ⊢
  cases hu : SpecAMQP.Ref.Vectors.unsignedOf json 4294967295 with
  | error err => simp [hu] at h
  | ok n =>
    simp only [hu] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.uint n, rfl,
      by simp only [BodiesAgree];
         exact (u32_toNat n (by have := unsignedOf_le json 4294967295 n hu; omega)).symm⟩

/-- **The `"ulong"` clause.** The same shared read and the same width-carrying round trip as
`"ubyte"`, at 18446744073709551615. -/
theorem carrier_clause_ulong (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "ulong") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  rw [← unsignedOf_eq] at ⊢
  cases hu : SpecAMQP.Ref.Vectors.unsignedOf json 18446744073709551615 with
  | error err => simp [hu] at h
  | ok n =>
    simp only [hu] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.ulong n, rfl,
      by simp only [BodiesAgree];
         exact (u64_toNat n (by have := unsignedOf_le json 18446744073709551615 n hu; omega)).symm⟩

/-- The two readers' fixed-width opaque payloads agree on success: the same reads and the same
width check, differing only in the failure text, which is why this is a one-directional agreement
on the success path rather than an equality of the two functions. -/
theorem fixedHex_ok_hexPayloadOf (json : Json) (width : Nat) (kind : String)
    (bytes : SpecAMQP.Ref.Octets)
    (h : SpecAMQP.Ref.Vectors.fixedHex json width = .ok bytes) :
    SpecAMQP.Spec.Codec.hexPayloadOf json width kind = .ok bytes := by
  unfold SpecAMQP.Ref.Vectors.fixedHex at h
  unfold SpecAMQP.Spec.Codec.hexPayloadOf
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hv : json.getObjValAs? String "hex" with
  | error err => simp [hv] at h
  | ok hex =>
    simp only [hv] at h ⊢
    cases hx : SpecAMQP.Harness.ofHex hex with
    | error err => simp [hx] at h
    | ok octets =>
      simp only [hx] at h ⊢
      by_cases hw : octets.size = width
      · simp only [hw, beq_iff_eq] at h ⊢
        injection h with hb
        subst hb
        rfl
      · simp only [hw, beq_iff_eq] at h ⊢
        simp at h

/-- **The `"float"` clause** — a fixed-width opaque payload, the same read and the same octets on
both sides. -/
theorem carrier_clause_float (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "float") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases hf : SpecAMQP.Ref.Vectors.fixedHex json 4 with
  | error err => simp [hf] at h
  | ok bytes =>
    have hspec : SpecAMQP.Spec.Codec.hexPayloadOf json 4 "float" = .ok bytes :=
      fixedHex_ok_hexPayloadOf json 4 "float" bytes hf
    simp only [hf, hspec] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.float bytes, rfl, by simp only [BodiesAgree]⟩

/-- **The `"double"` clause** — a fixed-width opaque payload, the same read and the same octets on
both sides. -/
theorem carrier_clause_double (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "double") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases hf : SpecAMQP.Ref.Vectors.fixedHex json 8 with
  | error err => simp [hf] at h
  | ok bytes =>
    have hspec : SpecAMQP.Spec.Codec.hexPayloadOf json 8 "double" = .ok bytes :=
      fixedHex_ok_hexPayloadOf json 8 "double" bytes hf
    simp only [hf, hspec] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.double bytes, rfl, by simp only [BodiesAgree]⟩

/-- **The `"decimal32"` clause** — a fixed-width opaque payload, the same read and the same octets on
both sides. -/
theorem carrier_clause_decimal32 (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "decimal32") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases hf : SpecAMQP.Ref.Vectors.fixedHex json 4 with
  | error err => simp [hf] at h
  | ok bytes =>
    have hspec : SpecAMQP.Spec.Codec.hexPayloadOf json 4 "decimal32" = .ok bytes :=
      fixedHex_ok_hexPayloadOf json 4 "decimal32" bytes hf
    simp only [hf, hspec] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.decimal32 bytes, rfl, by simp only [BodiesAgree]⟩

/-- **The `"decimal64"` clause** — a fixed-width opaque payload, the same read and the same octets on
both sides. -/
theorem carrier_clause_decimal64 (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "decimal64") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases hf : SpecAMQP.Ref.Vectors.fixedHex json 8 with
  | error err => simp [hf] at h
  | ok bytes =>
    have hspec : SpecAMQP.Spec.Codec.hexPayloadOf json 8 "decimal64" = .ok bytes :=
      fixedHex_ok_hexPayloadOf json 8 "decimal64" bytes hf
    simp only [hf, hspec] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.decimal64 bytes, rfl, by simp only [BodiesAgree]⟩

/-- **The `"decimal128"` clause** — a fixed-width opaque payload, the same read and the same octets on
both sides. -/
theorem carrier_clause_decimal128 (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "decimal128") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases hf : SpecAMQP.Ref.Vectors.fixedHex json 16 with
  | error err => simp [hf] at h
  | ok bytes =>
    have hspec : SpecAMQP.Spec.Codec.hexPayloadOf json 16 "decimal128" = .ok bytes :=
      fixedHex_ok_hexPayloadOf json 16 "decimal128" bytes hf
    simp only [hf, hspec] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.decimal128 bytes, rfl, by simp only [BodiesAgree]⟩

/-- **The `"uuid"` clause** — a fixed-width opaque payload, the same read and the same octets on
both sides. -/
theorem carrier_clause_uuid (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "uuid") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases hf : SpecAMQP.Ref.Vectors.fixedHex json 16 with
  | error err => simp [hf] at h
  | ok bytes =>
    have hspec : SpecAMQP.Spec.Codec.hexPayloadOf json 16 "uuid" = .ok bytes :=
      fixedHex_ok_hexPayloadOf json 16 "uuid" bytes hf
    simp only [hf, hspec] at h ⊢
    injection h with hb
    subst hb
    exact ⟨.uuid bytes, rfl, by simp only [BodiesAgree]⟩

/-! ## The signed clauses: a bound-checked read and a bitvector round trip -/

/-- `n` read back from its `Int8` spelling, for `n` in range: the reference's carrier is width
carrying where the specification's value is not. -/
theorem i8_toInt (n : Int) (h₁ : -(2 ^ 7) ≤ n) (h₂ : n ≤ 2 ^ 7 - 1) :
    (Int8.ofBitVec (BitVec.ofNat 8 (n % 256).toNat)).toInt = n := by
  show (BitVec.ofNat 8 (n % 256).toNat).toInt = n
  rw [BitVec.toInt_ofNat']
  rw [Int.bmod_eq_iff (by decide : (0 : Nat) < 256)]
  refine ⟨by omega, by omega, ?_⟩
  have hnn : (0 : Int) ≤ n % 256 := Int.emod_nonneg n (by decide)
  have hcast : (((n % 256).toNat : Nat) : Int) = n % 256 := Int.toNat_of_nonneg hnn
  rw [hcast]
  refine ⟨n / 256, ?_⟩
  have hsplit : n % 256 + 256 * (n / 256) = n := Int.emod_add_mul_ediv n 256
  omega

theorem i16_toInt (n : Int) (h₁ : -(2 ^ 15) ≤ n) (h₂ : n ≤ 2 ^ 15 - 1) :
    (Int16.ofBitVec (BitVec.ofNat 16 (n % 65536).toNat)).toInt = n := by
  show (BitVec.ofNat 16 (n % 65536).toNat).toInt = n
  rw [BitVec.toInt_ofNat']
  rw [Int.bmod_eq_iff (by decide : (0 : Nat) < 65536)]
  refine ⟨by omega, by omega, ?_⟩
  have hnn : (0 : Int) ≤ n % 65536 := Int.emod_nonneg n (by decide)
  have hcast : (((n % 65536).toNat : Nat) : Int) = n % 65536 := Int.toNat_of_nonneg hnn
  rw [hcast]
  refine ⟨n / 65536, ?_⟩
  have hsplit : n % 65536 + 65536 * (n / 65536) = n := Int.emod_add_mul_ediv n 65536
  omega

theorem i32_toInt (n : Int) (h₁ : -(2 ^ 31) ≤ n) (h₂ : n ≤ 2 ^ 31 - 1) :
    (Int32.ofBitVec (BitVec.ofNat 32 (n % 4294967296).toNat)).toInt = n := by
  show (BitVec.ofNat 32 (n % 4294967296).toNat).toInt = n
  rw [BitVec.toInt_ofNat']
  rw [Int.bmod_eq_iff (by decide : (0 : Nat) < 4294967296)]
  refine ⟨by omega, by omega, ?_⟩
  have hnn : (0 : Int) ≤ n % 4294967296 := Int.emod_nonneg n (by decide)
  have hcast : (((n % 4294967296).toNat : Nat) : Int) = n % 4294967296 :=
    Int.toNat_of_nonneg hnn
  rw [hcast]
  refine ⟨n / 4294967296, ?_⟩
  have hsplit : n % 4294967296 + 4294967296 * (n / 4294967296) = n :=
    Int.emod_add_mul_ediv n 4294967296
  omega

theorem i64_toInt (n : Int) (h₁ : -(2 ^ 63) ≤ n) (h₂ : n ≤ 2 ^ 63 - 1) :
    (Int64.ofBitVec (BitVec.ofNat 64 (n % 18446744073709551616).toNat)).toInt = n := by
  show (BitVec.ofNat 64 (n % 18446744073709551616).toNat).toInt = n
  rw [BitVec.toInt_ofNat']
  rw [Int.bmod_eq_iff (by decide : (0 : Nat) < 18446744073709551616)]
  refine ⟨by omega, by omega, ?_⟩
  have hnn : (0 : Int) ≤ n % 18446744073709551616 := Int.emod_nonneg n (by decide)
  have hcast : (((n % 18446744073709551616).toNat : Nat) : Int) = n % 18446744073709551616 :=
    Int.toNat_of_nonneg hnn
  rw [hcast]
  refine ⟨n / 18446744073709551616, ?_⟩
  have hsplit : n % 18446744073709551616 + 18446744073709551616 * (n / 18446744073709551616) = n :=
    Int.emod_add_mul_ediv n 18446744073709551616
  omega

/-- The signed range the reference's `signedOf` enforces, read off its own success. -/
theorem signedOf_range (json : Json) (width : Nat) (n : Int)
    (h : SpecAMQP.Ref.Vectors.signedOf json width = .ok n) :
    -((2 : Int) ^ (width - 1)) ≤ n ∧ n ≤ (2 : Int) ^ (width - 1) - 1 := by
  unfold SpecAMQP.Ref.Vectors.signedOf at h
  simp only [Bind.bind, Except.bind] at h
  cases hv : json.getObjValAs? Int "value" with
  | error err => simp [hv] at h
  | ok v =>
    simp only [hv] at h
    split at h
    · rename_i hcond
      injection h with hb
      subst hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact hcond
    · simp at h

/-- A successful bounded read is a read of the same key giving the same value: the timestamp
clause needs it, because the specification's reader does not range-check `"milliseconds"` where
the reference's does. -/
theorem boundedField_ok_getObjValAs (json : Json) (key : String) (lo hi n : Int)
    (h : SpecAMQP.Ref.Vectors.boundedField json key lo hi = .ok n) :
    json.getObjValAs? Int key = .ok n := by
  unfold SpecAMQP.Ref.Vectors.boundedField at h
  simp only [Bind.bind, Except.bind] at h
  cases hv : json.getObjValAs? Int key with
  | error err => simp [hv] at h
  | ok v =>
    simp only [hv] at h
    split at h
    · rename_i hcond
      injection h with hb
      subst hb
      first | rfl | exact hv
    · simp at h

/-- The bounds a successful bounded read enforces. -/
theorem boundedField_range (json : Json) (key : String) (lo hi n : Int)
    (h : SpecAMQP.Ref.Vectors.boundedField json key lo hi = .ok n) : lo ≤ n ∧ n ≤ hi := by
  unfold SpecAMQP.Ref.Vectors.boundedField at h
  simp only [Bind.bind, Except.bind] at h
  cases hv : json.getObjValAs? Int key with
  | error err => simp [hv] at h
  | ok v =>
    simp only [hv] at h
    split at h
    · rename_i hcond
      injection h with hb
      subst hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact hcond
    · simp at h

/-- **The `"byte"` clause.** One shared bound-checked read, and the reference's width-carrying
carrier read back to the specification's `Int` through the bitvector round trip. -/
theorem carrier_clause_byte (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "byte") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  rw [← signedOf_eq] at ⊢
  cases hu : SpecAMQP.Ref.Vectors.signedOf json 8 with
  | error err => simp [hu] at h
  | ok n =>
    simp only [hu] at h ⊢
    injection h with hb
    subst hb
    have hrange := signedOf_range json 8 n hu
    exact ⟨.byte n, rfl, by
      simp only [BodiesAgree]
      exact (i8_toInt n (by omega) (by omega)).symm⟩

/-- **The `"short"` clause.** One shared bound-checked read, and the reference's width-carrying
carrier read back to the specification's `Int` through the bitvector round trip. -/
theorem carrier_clause_short (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "short") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  rw [← signedOf_eq] at ⊢
  cases hu : SpecAMQP.Ref.Vectors.signedOf json 16 with
  | error err => simp [hu] at h
  | ok n =>
    simp only [hu] at h ⊢
    injection h with hb
    subst hb
    have hrange := signedOf_range json 16 n hu
    exact ⟨.short n, rfl, by
      simp only [BodiesAgree]
      exact (i16_toInt n (by omega) (by omega)).symm⟩

/-- **The `"int"` clause.** One shared bound-checked read, and the reference's width-carrying
carrier read back to the specification's `Int` through the bitvector round trip. -/
theorem carrier_clause_int (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "int") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  rw [← signedOf_eq] at ⊢
  cases hu : SpecAMQP.Ref.Vectors.signedOf json 32 with
  | error err => simp [hu] at h
  | ok n =>
    simp only [hu] at h ⊢
    injection h with hb
    subst hb
    have hrange := signedOf_range json 32 n hu
    exact ⟨.int n, rfl, by
      simp only [BodiesAgree]
      exact (i32_toInt n (by omega) (by omega)).symm⟩

/-- **The `"long"` clause.** One shared bound-checked read, and the reference's width-carrying
carrier read back to the specification's `Int` through the bitvector round trip. -/
theorem carrier_clause_long (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "long") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  rw [← signedOf_eq] at ⊢
  cases hu : SpecAMQP.Ref.Vectors.signedOf json 64 with
  | error err => simp [hu] at h
  | ok n =>
    simp only [hu] at h ⊢
    injection h with hb
    subst hb
    have hrange := signedOf_range json 64 n hu
    exact ⟨.long n, rfl, by
      simp only [BodiesAgree]
      exact (i64_toInt n (by omega) (by omega)).symm⟩

/-- **The `"timestamp"` clause.** The reference range-checks `"milliseconds"` where the
specification reads it bare, so the clause carries the read agreement (`boundedField` reads the
key it read) as well as the range and the round trip. -/
theorem carrier_clause_timestamp (fuel : Nat) (json : Json)
    (hk : json.getObjValAs? String "type" = .ok "timestamp") (other : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Vectors.valueOfJson (fuel + 1) json = .ok other) :
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson (fuel + 1) json = .ok body ∧ BodiesAgree body other := by
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  unfold SpecAMQP.Spec.Codec.valueOfJson
  simp only [Bind.bind, Except.bind] at h ⊢
  simp only [hk] at h ⊢
  cases hb : SpecAMQP.Ref.Vectors.boundedField json "milliseconds" (-(2 ^ 63)) (2 ^ 63 - 1) with
  | error err => simp_all
  | ok n =>
    have hread : json.getObjValAs? Int "milliseconds" = .ok n :=
      boundedField_ok_getObjValAs json "milliseconds" (-(2 ^ 63)) (2 ^ 63 - 1) n hb
    simp only [hb, hread] at h ⊢
    injection h with hb'
    subst hb'
    have hrange := boundedField_range json "milliseconds" (-(2 ^ 63)) (2 ^ 63 - 1) n hb
    exact ⟨.timestamp n, rfl, by
      simp only [BodiesAgree]
      exact (i64_toInt n (by omega) (by omega)).symm⟩

/-! ## The join: the family at a given fuel

The clauses above are stated at `valueOfJson (fuel + 1)` with the discriminant as a hypothesis,
because that is what makes each clause's own `match` reduce against a literal. The contract's
`ValueCarrierAgree` is at fuel 64 and states the claim over *every* `Json`, so the two are joined by
a fuel-indexed restatement: `ValueCarrierAgrees fuel` is the claim at `fuel`, and it is the shape
the compound clauses need, since they read their items with `valueOfJson fuel` and so consume the
claim at the fuel beneath them.

That fixes the induction: `ValueCarrierAgrees 0` holds vacuously (both readers refuse at fuel 0),
and the step is a lemma whose cases are the clauses above — the scalar ones used as they stand, the
compound ones consuming the induction hypothesis at `fuel`. The step is not written yet; the
statement, its base case and the reduction to the contract's form are, and they are what the step
will be stated against. -/

/-- **The corpus readers' agreement at a given fuel.** `ValueCarrierAgree` is this at 64. -/
def ValueCarrierAgrees (fuel : Nat) : Prop :=
  ∀ (json : Json) (other : SpecAMQP.Ref.Value),
    SpecAMQP.Ref.Vectors.valueOfJson fuel json = .ok other →
    ∃ body : SpecAMQP.Spec.Codec.Value,
      SpecAMQP.Spec.Codec.valueOfJson fuel json = .ok body ∧ BodiesAgree body other

/-- Nothing is read at fuel 0: both readers refuse, so the claim holds vacuously. -/
theorem valueCarrierAgrees_zero : ValueCarrierAgrees 0 := by
  intro json other h
  unfold SpecAMQP.Ref.Vectors.valueOfJson at h
  simp at h

/-- **The contract's statement is this one at fuel 64**, so the step lemma is what stands between
the clause family and `ValueCarrierAgree`. -/
theorem valueCarrierAgree_of_agrees (h : ValueCarrierAgrees 64) : ValueCarrierAgree := h

end SpecAMQP.Proofs
