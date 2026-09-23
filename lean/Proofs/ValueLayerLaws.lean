import Contracts.Conformance
import Proofs.FrameConformance
import Proofs.FrameSendConformance

/-!
# The value layer's hypotheses, at the evidence

`Proofs.FrameConformance.ValueLayersAgree`, `Proofs.FrameSendConformance.ValueCarrierAgree` and
`Proofs.FrameSendConformance.ValueWriterAgree` are the three value-layer hypotheses the frame
layer's two `Conforms` instances rest on. This module asks what is provable about them, and the
answer is not the one the instances' prose hoped for: **`ValueWriterAgree` is false as stated**, at a
witness in the repository's own vocabulary; **`ValueLayersAgree` was false as stated and is
undecided now**, because the divergence it named has been fixed and what remains is a statement with
no witness and no available proof; and **`ValueCarrierAgree` is untested here**.

## What the evidence says, statement by statement

* **`ValueLayersAgree` was false when this module was written, and is undecided now.** Its
  divergence was a check-order difference inside the map path: the specification reads a compound's
  `size` and `count` fields and asks whether the count is even *before* it reads the items, while the
  reference read the items, compared the declared size with what they measured, and asked about
  parity afterwards. Part 1 forbids an odd count outright ("Map encodings MUST contain an even
  number of items", `amqp-core-types-v1.0-os.xml` `…/type:map.1`), so `mapWitness` — odd count *and*
  a declared size that disagrees with its items — was the smallest buffer the two answered
  differently. `Ref.Value.readMap`'s parity guard has since moved ahead of the items read, so both
  now refuse it `malformed`; a sweep of 114,225 buffers (every length 1-3 buffer over a 45-octet
  alphabet, every length-4 buffer over a 12-octet alphabet, and a structured set of arrays,
  compounds and described values) now finds **no class divergence at all**. So the receive direction
  has no witness: a refutation is not provable because the divergence is gone, and a proof is not
  available here because it would need the value layer's own `Conforms` instance, which does not
  exist. That state is *undecided*, and this module leaves it there rather than writing either
  direction.
* **`ValueWriterAgree` is false**, and its first conjunct alone is enough: the reference's writer
  writes a raw payload at whatever width the value carries (`#[0x72] ++ payload`), while the
  specification's writer looks the width up in the declared surface and refuses a payload the type
  has no encoding for. The reference's octets for that value are not the specification's answer, and
  the hypothesis demands they be the same octets.
* **`ValueCarrierAgree` is untouched here**: it is a claim about the two corpus-vocabulary readers
  (`Spec.Codec.valueOfJson` against `Ref.Vectors.valueOfJson`), not about the wire, and this module
  has no evidence against it.
* **The send *endpoint* is not refutable here, and the reason is a type rather than a missing
  witness.** Every divergence between the two writers that the corpus vocabulary can express is
  *class-only* — both refuse, with different classes (`.array 0x00 [null]` and `.array 0xE0 [null]`
  were `malformed:` against `limit:`) — and the reference's writer answers `Except String Octets`, so
  its class can only be recovered by `Ref.Frame.classOf`, i.e. by splitting prose. The only *shape*
  divergence (one writes, the other refuses) is the ill-width family, which `valueOfJson`'s
  fixed-width payload checks put out of the carrier's reach. So `¬ Conforms specFrameSend
  refFrameSend` has no witness a kernel proof can carry until the reference's value writer reports
  its class as a field, the way `Spec.Codec` now does.

## Where the class comparison now stands

The vocabulary that blocked the class-comparing statements has been removed on one side. The
specification's class is a **field** (`Spec.Codec.Refusal.reasonClass`), and the reference's
*reader* carries its class as a variant (`Ref.DecodeError`), so a comparison between those two is a
`decide`-able goal — measured, not assumed: `(Spec.Codec.refusal "malformed" "prose").reasonClass =
"malformed"` closes by `rfl`, and a mismatch between a `Ref.DecodeError` variant's class and a
`Spec.Codec.Refusal` field's class closes by `decide`.

What is still prose is the reference's *writer*: `Ref.encode` returns `Except String Octets`, so its
class exists only as the leading token of a message that `Ref.Frame.classOf` recovers with
`String.splitOn ":"`. That function is not reducible in the kernel — it is
`if sep == "" then [s] else splitOnAux s sep 0 0 0 []`, and `splitOnAux` is a well-founded scan over
`String.Pos.Raw` whose `atEnd`/`get`/`next` do not reduce either, so

  `example : ("a:b".splitOn ":") == ["a", "b"]` is closed by neither `decide`, `simp`, nor
  `with_unfolding_all decide`; only `native_decide`, which this repository does not use.

`ValueWriterAgree`'s second conjunct compares exactly that prose, which is why the landed refutation
is written against the first conjunct, where no class appears at all.

What this module lands, then, is the artefacts' answers for a witness, in each artefact's own terms:
the two readers' answers to `mapWitness`, the two writers' answers for the ill-width and
array-constructor families, and the reference's size accounting. Where a class-comparing statement
follows from them it is named in the docstring beside the fact, and where no witness exists it is
named as undecided rather than written.
-/

-- The cursor types carry no `DecidableEq`, because no proof has needed to compare cursors yet.
-- The walks below do, and these are proof-side instances: neither artefact changes.
deriving instance DecidableEq for SpecAMQP.Spec.Codec.Cursor
deriving instance DecidableEq for SpecAMQP.Ref.Cursor
deriving instance DecidableEq for SpecAMQP.Ref.DecodeError

namespace SpecAMQP.Proofs

open SpecAMQP.Contracts
open SpecAMQP.Harness (Octets)


/-! ## The witness for the readers

`map8` (`%xC1`), its size field `%x03`, its count field `%x01`, then one `null` (`%x40`).

Two defects in one buffer, which is what made the readers' check order observable: the count is odd,
which Part 1 forbids, *and* the size field says three octets follow it while the count field and the
one item measure two. When the two readers ranked those checks differently this buffer was the
smallest witness of a class divergence (`sizeMismatch` against `malformed`); `Ref.Value.readMap` now
decides parity first, as `Spec.Codec` always has, so the two answers below agree. -/
def mapWitness : Octets := #[0xC1, 0x03, 0x01, 0x40]

theorem mapWitness_size : mapWitness.size = 4 := by decide

/-! ## The reference's reader, stepped

Each lemma walks one decision of `Ref.readValue` (or of the map path beneath it) with the branch
fact its caller supplies, which is how the repository's frame proofs walk a reader: the recursive
definition is unfolded once, the branch that the concrete octets select is reduced, and the
remaining work is the caller's hypotheses. -/

theorem ref_readValue_map (fuel : Nat) (c c' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeU8 c = .ok (0xC1, c')) :
    SpecAMQP.Ref.readValue (fuel + 1) c = SpecAMQP.Ref.readMap fuel 1 c' := by
  unfold SpecAMQP.Ref.readValue
  try dsimp only []
  rw [h]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

theorem ref_readItems_nil (fuel : Nat) (c : SpecAMQP.Ref.Cursor) :
    SpecAMQP.Ref.readItems (fuel + 1) 0 c = .ok ([], c) := by
  unfold SpecAMQP.Ref.readItems
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The reference's map read up to its parity guard.** The count field alone decides whether the
items are read at all: an odd count is refused before `readItems` is reached and before the declared
size is compared. This is the order the specification has always had, and the order this reader now
shares with its own array path. -/
theorem ref_readMap_odd (fuel width : Nat) (c c₁ c₂ : SpecAMQP.Ref.Cursor)
    (size count : Nat)
    (h₁ : SpecAMQP.Ref.takeBeU width c = .ok (size, c₁))
    (h₂ : SpecAMQP.Ref.takeBeU width c₁ = .ok (count, c₂))
    (hodd : (count % 2 != 0) = true) :
    SpecAMQP.Ref.readMap (fuel + 1) width c =
      .error (.malformed "a map must have an even number of items") := by
  unfold SpecAMQP.Ref.readMap
  try dsimp only []
  rw [h₁]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [h₂]
  try dsimp only []
  rw [hodd]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The reference's answer to the witness, now the aligned one**: the parity refusal, the same
class the specification names for the same buffer in `spec_mapWitness_decodeValue`. Before
`Ref.Value.readMap`'s parity guard was moved ahead of the items read this theorem read
`.error (.sizeMismatch "map" 3 2)`, and the two artefacts disagreed about the class. -/
theorem ref_mapWitness_decode :
    SpecAMQP.Ref.decode mapWitness = .error (.malformed "a map must have an even number of items") := by
  have hstep : SpecAMQP.Ref.readValue 4 { data := mapWitness, pos := 0 } =
      SpecAMQP.Ref.readMap 3 1 { data := mapWitness, pos := 1 } :=
    ref_readValue_map 3 _ _ (by decide)
  have hmap : SpecAMQP.Ref.readMap 3 1 { data := mapWitness, pos := 1 } =
      .error (.malformed "a map must have an even number of items") :=
    ref_readMap_odd (fuel := 2) (width := 1)
      (c := { data := mapWitness, pos := 1 }) (c₁ := { data := mapWitness, pos := 2 })
      (c₂ := { data := mapWitness, pos := 3 }) (size := 3) (count := 1)
      (by decide) (by decide) (by decide)
  unfold SpecAMQP.Ref.decode
  rw [mapWitness_size, hstep, hmap]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-! ## The specification's reader, stepped -/

/-- The specification's reader at a compound constructor: the octet is looked up in the declared
surface and the compound is read, with no branch on the count before the items. -/
theorem spec_readValue_compound (fuel : Nat) (c c' : SpecAMQP.Spec.Codec.Cursor)
    (code : UInt8) (decl : SpecAMQP.Generated.Oasis.EncodingDecl)
    (h : SpecAMQP.Spec.Codec.takeU8 c = .ok (code, c'))
    (hclass : SpecAMQP.Spec.Value.classify code.toNat =
      SpecAMQP.Spec.Value.Constructor.compound 1)
    (hdecl : SpecAMQP.Spec.Codec.dataDecl code = .ok decl)
    (hcat : decl.category = SpecAMQP.Generated.Oasis.Category.compound) :
    SpecAMQP.Spec.Codec.readValue (fuel + 1) c = SpecAMQP.Spec.Codec.readCompound fuel decl c' := by
  unfold SpecAMQP.Spec.Codec.readValue
  try dsimp only []
  rw [h]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [hclass]
  try dsimp only []
  rw [hdecl]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [hcat]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The specification's map read**: the parity of the count is decided *before* the items are
read and before the declared size is compared, which is the other half of the divergence. -/
theorem spec_readCompound_map_odd (fuel : Nat) (decl : SpecAMQP.Generated.Oasis.EncodingDecl)
    (c c₁ c₂ : SpecAMQP.Spec.Codec.Cursor) (size count : Nat)
    (howner : decl.owner = "map")
    (h₁ : SpecAMQP.Spec.Codec.takeBe decl.width c = .ok (size, c₁))
    (h₂ : SpecAMQP.Spec.Codec.takeBe decl.width c₁ = .ok (count, c₂))
    (hodd : (count % 2 != 0) = true) :
    SpecAMQP.Spec.Codec.readCompound (fuel + 1) decl c =
      .error (SpecAMQP.Spec.Codec.refusal "malformed"
        s!"a map declares {count} item(s): keys and values come in pairs, so an odd count is not a map") := by
  unfold SpecAMQP.Spec.Codec.readCompound
  try dsimp only []
  rw [h₁]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [h₂]
  try dsimp only []
  rw [howner]
  try dsimp only []
  rw [hodd]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The specification's answer to the witness**: the parity refusal, its class a field of the
`Spec.Codec.Refusal` this reader answers with (and its message that class, a colon and the prose).
The reference's answer to the same buffer is `ref_mapWitness_decode`'s, whose class is `.malformed` —
the same class, since `Ref.Value.readMap`'s parity guard now runs first, so the two answers agree
where they once disagreed. -/
theorem spec_mapWitness_decodeValue :
    SpecAMQP.Spec.Codec.decodeValue mapWitness =
      .error (SpecAMQP.Spec.Codec.refusal "malformed"
        "a map declares 1 item(s): keys and values come in pairs, so an odd count is not a map") := by
  have hrow : (SpecAMQP.Spec.Codec.dataDecl 0xC1).map
      (fun d => (d.owner, d.category, d.width)) =
      .ok ("map", SpecAMQP.Generated.Oasis.Category.compound, 1) := by decide
  cases hdecl : SpecAMQP.Spec.Codec.dataDecl 0xC1 with
  | error err => rw [hdecl] at hrow; cases hrow
  | ok decl =>
    rw [hdecl] at hrow
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hrow
    obtain ⟨howner, hcat, hwidth⟩ := hrow
    have hstep : SpecAMQP.Spec.Codec.readValue 4 { data := mapWitness, pos := 0 } =
        SpecAMQP.Spec.Codec.readCompound 3 decl { data := mapWitness, pos := 1 } :=
      spec_readValue_compound (fuel := 3) (c := { data := mapWitness, pos := 0 })
        (c' := { data := mapWitness, pos := 1 }) (code := 0xC1) (decl := decl)
        (by decide) (by decide) hdecl hcat
    have hmap : SpecAMQP.Spec.Codec.readCompound 3 decl { data := mapWitness, pos := 1 } =
        .error (SpecAMQP.Spec.Codec.refusal "malformed"
          "a map declares 1 item(s): keys and values come in pairs, so an odd count is not a map") :=
      spec_readCompound_map_odd (fuel := 2) (decl := decl)
        (c := { data := mapWitness, pos := 1 }) (c₁ := { data := mapWitness, pos := 2 })
        (c₂ := { data := mapWitness, pos := 3 }) (size := 3) (count := 1)
        howner (by rw [hwidth]; decide) (by rw [hwidth]; decide) (by decide)
    unfold SpecAMQP.Spec.Codec.decodeValue
    rw [mapWitness_size, hstep, hmap]
    try dsimp only []
    try simp only [Except.error.injEq, SpecAMQP.Spec.Codec.refusal,
      SpecAMQP.Spec.Codec.refusalMessage]
    try decide

/-! ## The writer's witness

The reference's writer writes a fixed-width payload unchanged (`#[0x72] ++ payload`); the
specification's writer looks the payload's width up in the declared surface
(`rowOf "float" bits.size`) and refuses a width the surface does not declare. Values reach a writer
from a reader, so this witness is outside the corpus vocabulary — `valueOfJson` and `hexPayloadOf`
fix a `float`'s payload at four octets — and `ValueWriterAgree` quantifies over every pair of
values `BodiesAgree` relates, not only over the reachable ones. The specification's refusal for
this value leads with `limit` — it spelled the bare prose until the classless refusals in
`Spec/Codec.lean` were given their class, and that change moved this theorem's message and
nothing else in this module. Another divergence in the same
hypothesis is reachable through the vocabulary (an array whose element does not fit its declared
element constructor), and it is reported with its two messages below. -/

theorem bodiesAgree_floatEmpty : BodiesAgree (.float #[]) (.float #[]) := by
  unfold BodiesAgree
  rfl

theorem ref_encode_floatEmpty : SpecAMQP.Ref.encode (.float #[]) = .ok #[0x72] := by
  unfold SpecAMQP.Ref.encode
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

theorem spec_encodeValue_floatEmpty :
    SpecAMQP.Spec.Codec.encodeValue (.float #[]) =
      .error (SpecAMQP.Spec.Codec.refusal "limit"
        "the declared surface has no float encoding of width 0") := by
  unfold SpecAMQP.Spec.Codec.encodeValue SpecAMQP.Spec.Codec.writeValue
    SpecAMQP.Spec.Codec.emitScalar SpecAMQP.Spec.Codec.rowOf
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

/-- **`ValueWriterAgree` is false.** Its first conjunct demands that wherever the reference's writer
succeeds, the specification's writer produces the same octets; for the empty-payload `float` the
reference writes one octet and the specification refuses. -/
theorem not_valueWriterAgree : ¬ ValueWriterAgree := by
  intro h
  obtain ⟨hok, _⟩ := h (.float #[]) (.float #[]) bodiesAgree_floatEmpty
  have hspec := hok #[0x72] ref_encode_floatEmpty
  rw [spec_encodeValue_floatEmpty] at hspec
  cases hspec

/-! ## The reachable writer divergence, at the answers

Both writers are asked for an array whose declared element constructor is `%x57` — an octet inside
the fixed-width range that the declared surface assigns no encoding — carrying one `null`. The
corpus vocabulary can produce that pair (`"constructor": "57"`), so this is a *reachable* pair, and
it is the one that mattered: the specification refused it `unassigned` while the reference's catch-all
said `limit`. `Ref.arrayElement`'s catch-all has since been split — `unassigned` where the surface
assigns the constructor no encoding, `malformed` where the value does not fit the constructor it does
assign — so the two now agree, and these two theorems are the pair that goes red if either side's
class is weakened rather than aligned. The specification's two *classless* refusals in this family
(`.array %x00 [x]` and `.array %xE0 [x]`) were given `malformed` in the same pass. -/

theorem ref_encode_arrayUnassigned :
    SpecAMQP.Ref.encode (.array 0x57 [.null]) =
      .error "unassigned: octet 87 is not an encoding the constructor grammar assigns" := by
  unfold SpecAMQP.Ref.encode SpecAMQP.Ref.arrayElementItems SpecAMQP.Ref.arrayElement
  try dsimp only []
  try simp only [SpecAMQP.Ref.assignedConstructor]
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

theorem spec_encodeValue_arrayUnassigned :
    SpecAMQP.Spec.Codec.encodeValue (.array 0x57 [.null]) =
      .error (SpecAMQP.Spec.Codec.refusal "unassigned"
        "octet 0x57 lies in the fixed range of width 1 but the declared surface assigns it no encoding") := by
  unfold SpecAMQP.Spec.Codec.encodeValue SpecAMQP.Spec.Codec.writeValue
    SpecAMQP.Spec.Codec.elementDecl?
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

theorem bodiesAgree_arrayUnassigned :
    BodiesAgree (.array 0x57 [.null]) (.array 0x57 [.null]) := by
  simp [BodiesAgree, BodiesAgreeList]

/-! ## The size accounting, settled by the artefacts

The divergence above is an *order* difference, not an *accounting* difference, and this section is
the measurement rather than the claim: `list8` with a size field of `1`, a count field of `0` and no
items is **accepted by both readers**, consuming its three octets. A size field of one octet covers
exactly the count field, in both artefacts — so a compound's size counts the octets that follow the
size field (the count field included), which is `ledger/ambiguities/compound-size-field.json`'s
adopted reading with its arithmetic evidence from Part 1's own worked examples.

The odd-count maps above are therefore not two readings of `size`; they are two readings of *when*
the parity rule is consulted. -/

def listWitness : Octets := #[0xC0, 0x01, 0x00]

theorem listWitness_size : listWitness.size = 3 := by decide

theorem ref_readValue_compound (fuel : Nat) (c c' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeU8 c = .ok (0xC0, c')) :
    SpecAMQP.Ref.readValue (fuel + 1) c = SpecAMQP.Ref.readCompound fuel 1 c' := by
  unfold SpecAMQP.Ref.readValue
  try dsimp only []
  rw [h]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

theorem ref_readCompound_list_ok (fuel width : Nat) (c c₁ c₂ c₃ : SpecAMQP.Ref.Cursor)
    (size count : Nat) (items : List SpecAMQP.Ref.Value)
    (h₁ : SpecAMQP.Ref.takeBeU width c = .ok (size, c₁))
    (h₂ : SpecAMQP.Ref.takeBeU width c₁ = .ok (count, c₂))
    (h₃ : SpecAMQP.Ref.readItems fuel count c₂ = .ok (items, c₃))
    (heq : (c₃.pos - c₁.pos != size) = false) :
    SpecAMQP.Ref.readCompound (fuel + 1) width c = .ok (.list items, c₃) := by
  unfold SpecAMQP.Ref.readCompound
  try dsimp only []
  rw [h₁]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [h₂]
  try dsimp only []
  rw [h₃]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [heq]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The reference accepts a `list8` whose size field covers only its count field**, consuming
its three octets: a size field of one octet is the count field and nothing else. -/
theorem ref_listWitness_decode :
    SpecAMQP.Ref.decode listWitness = .ok (.list [], 3) := by
  have hstep : SpecAMQP.Ref.readValue 3 { data := listWitness, pos := 0 } =
      SpecAMQP.Ref.readCompound 2 1 { data := listWitness, pos := 1 } :=
    ref_readValue_compound 2 _ _ (by decide)
  have hlist : SpecAMQP.Ref.readCompound 2 1 { data := listWitness, pos := 1 } =
      .ok (.list [], { data := listWitness, pos := 3 }) :=
    ref_readCompound_list_ok (fuel := 1) (width := 1)
      (c := { data := listWitness, pos := 1 }) (c₁ := { data := listWitness, pos := 2 })
      (c₂ := { data := listWitness, pos := 3 }) (c₃ := { data := listWitness, pos := 3 })
      (size := 1) (count := 0) (items := [])
      (by decide) (by decide) (ref_readItems_nil 0 _) (by decide)
  unfold SpecAMQP.Ref.decode
  rw [listWitness_size, hstep, hlist]
  try dsimp only []

end SpecAMQP.Proofs
