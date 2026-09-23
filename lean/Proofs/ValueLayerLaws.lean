import Contracts.Conformance
import Proofs.FrameConformance
import Proofs.FrameSendConformance

/-!
# The value layer's hypotheses, at the evidence

`Proofs.FrameConformance.ValueLayersAgree`, `Proofs.FrameSendConformance.ValueCarrierAgree` and
`Proofs.FrameSendConformance.ValueWriterAgree` are the three value-layer hypotheses the frame
layer's two `Conforms` instances rest on. This module asks what is provable about them, and the
answer is not the one the instances' prose hoped for: **two of the three are false as stated**, at
witnesses that are in the repository's own vocabulary, and the third is untested here.

## What is refuted, and what is not

* **`ValueLayersAgree` is false**, and the divergence is a check-order difference inside the map
  path. The specification reads a compound's `size` and `count` fields and asks whether the count
  is even *before* it reads the items; the reference reads the items, compares the declared size
  with what they measured, and asks about parity afterwards. Part 1 forbids an odd count outright
  ("Map encodings MUST contain an even number of items", `amqp-core-types-v1.0-os.xml`
  `…/type:map.1`), so a buffer whose `count` field is odd *and* whose declared size disagrees with
  its items is a legal buffer to hand either reader — and the two answer with different reason
  classes. `mapWitness` is the smallest such buffer.
* **`ValueWriterAgree` is false**, and its first conjunct alone is enough: the reference's writer
  writes a raw payload at whatever width the value carries (`#[0x72] ++ payload`), while the
  specification's writer looks the width up in the declared surface and refuses a payload the type
  has no encoding for. `floatEmpty` is the smallest witness. The reference's octets for that value
  are not the specification's answer, and the hypothesis demands they be the same octets.
* **`ValueCarrierAgree` is untouched here**: it is a claim about the two corpus-vocabulary readers
  (`Spec.Codec.valueOfJson` against `Ref.Vectors.valueOfJson`), not about the wire, and this module
  has no evidence against it.

## The step this module cannot take, and it is the same step for every class-comparing statement

`ValueLayersAgree` and `ValueWriterAgree` compare reason classes, and the specification's reason
class is not a field: it is the token `Spec.Frame.reasonClassOf` recovers from prose by
`String.splitOn ":"`. `String.splitOn` is not reducible in the kernel — it is
`if sep == "" then [s] else splitOnAux s sep 0 0 0 []`, and `splitOnAux` is a well-founded scan over
`String.Pos.Raw`, whose `atEnd`/`get`/`next` do not reduce either:

  `example : ("a:b".splitOn ":") = ["a", "b"]` is not closed by `decide`, by `simp`, or by
  `with_unfolding_all decide`; only `native_decide` closes it, which this repository does not use.

So the class equality is one prose-splitting step beyond what a kernel proof can reach, in both
directions: it can neither be proved nor refuted from the artefacts' texts. That is not a gap in
this module; it is the reason `Spec.Frame`'s own documentation gives for carrying the class as a
*field* ("a class read back out of prose by `String.splitOn` is one no kernel proof can reason
about"). The frame layer honoured that on its own refusals and did not honour it on this
hypothesis, and every statement that compares a specification class with a reference class —
`ValueLayersAgree`, `ValueWriterAgree`, `AnswerMatched`, `ReadersAgree`, and with them the two
conditional frame instances and the connection instance — is stated in that vocabulary.

What this module therefore lands is the divergence *at the artefacts' answers*: what each reader
and each writer actually answers for a witness, in each artefact's own terms, with no class
recovered from prose. The class-comparing statements follow from these facts by exactly one step,
and the step is named in each docstring rather than taken.
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

Two defects in one buffer, which is what makes the readers' check order observable: the count is
odd, which Part 1 forbids, *and* the size field says three octets follow it while the count field
and the one item measure two. -/
def mapWitness : Octets := #[0xC1, 0x03, 0x01, 0x40]

theorem mapWitness_size : mapWitness.size = 4 := by decide

/-! ## The reference's reader, stepped

Each lemma walks one decision of `Ref.readValue` (or of the map path beneath it) with the branch
fact its caller supplies, which is how the repository's frame proofs walk a reader: the recursive
definition is unfolded once, the branch that the concrete octets select is reduced, and the
remaining work is the caller's hypotheses. -/

theorem ref_readValue_null (fuel : Nat) (c c' : SpecAMQP.Ref.Cursor)
    (h : SpecAMQP.Ref.takeU8 c = .ok (0x40, c')) :
    SpecAMQP.Ref.readValue (fuel + 1) c = .ok (.null, c') := by
  unfold SpecAMQP.Ref.readValue
  try dsimp only []
  rw [h]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

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

theorem ref_readItems_cons (fuel count : Nat) (c c' c'' : SpecAMQP.Ref.Cursor)
    (item : SpecAMQP.Ref.Value) (items : List SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.readValue fuel c = .ok (item, c'))
    (hrest : SpecAMQP.Ref.readItems fuel count c' = .ok (items, c'')) :
    SpecAMQP.Ref.readItems (fuel + 1) (count + 1) c = .ok (item :: items, c'') := by
  unfold SpecAMQP.Ref.readItems
  try dsimp only []
  rw [h]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [hrest]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The reference's map read up to its size comparison.** The items are read first, the declared
size is compared with what they measured, and only then is the count's parity consulted. This is
the step whose order differs from the specification's. -/
theorem ref_readMap_sizeMismatch (fuel width : Nat) (c c₁ c₂ c₃ : SpecAMQP.Ref.Cursor)
    (size count : Nat) (items : List SpecAMQP.Ref.Value)
    (h₁ : SpecAMQP.Ref.takeBeU width c = .ok (size, c₁))
    (h₂ : SpecAMQP.Ref.takeBeU width c₁ = .ok (count, c₂))
    (h₃ : SpecAMQP.Ref.readItems fuel count c₂ = .ok (items, c₃))
    (hne : (c₃.pos - c₁.pos != size) = true) :
    SpecAMQP.Ref.readMap (fuel + 1) width c =
      .error (.sizeMismatch "map" size (c₃.pos - c₁.pos)) := by
  unfold SpecAMQP.Ref.readMap
  try dsimp only []
  rw [h₁]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [h₂]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [h₃]
  try simp only [Bind.bind, Except.bind]
  try dsimp only []
  rw [hne]
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))

/-- **The reference's answer to the witness**: a `sizeMismatch` naming the declared `3` and the
measured `2` — the count field's own octet plus the one item — and never a word about parity. -/
theorem ref_mapWitness_decode :
    SpecAMQP.Ref.decode mapWitness = .error (.sizeMismatch "map" 3 2) := by
  have hstep : SpecAMQP.Ref.readValue 4 { data := mapWitness, pos := 0 } =
      SpecAMQP.Ref.readMap 3 1 { data := mapWitness, pos := 1 } :=
    ref_readValue_map 3 _ _ (by decide)
  have hrest : SpecAMQP.Ref.readMap 3 1 { data := mapWitness, pos := 1 } =
      .error (.sizeMismatch "map" 3 2) :=
    ref_readMap_sizeMismatch (fuel := 2) (width := 1)
      (c := { data := mapWitness, pos := 1 }) (c₁ := { data := mapWitness, pos := 2 })
      (c₂ := { data := mapWitness, pos := 3 }) (c₃ := { data := mapWitness, pos := 4 })
      (size := 3) (count := 1) (items := [.null])
      (by decide) (by decide)
      (ref_readItems_cons 1 0 _ _ _ .null [] (ref_readValue_null 0 _ _ (by decide))
        (ref_readItems_nil 0 _))
      (by decide)
  unfold SpecAMQP.Ref.decode
  rw [mapWitness_size, hstep, hrest]
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

/-- **The specification's answer to the witness**: the parity refusal, whose message is the class,
a colon and the prose. The reference's answer to the same buffer is
`ref_mapWitness_decode`'s — a `sizeMismatch` — so the two readers disagree about the buffer, and
the disagreement is visible here as the two messages' shapes rather than as a class comparison,
because the class is this message's first token and only `String.splitOn` can recover it. -/
theorem spec_mapWitness_decodeValue :
    SpecAMQP.Spec.Codec.decodeValue mapWitness =
      .error "malformed: a map declares 1 item(s): keys and values come in pairs, so an odd count is not a map" := by
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
    simp only [Except.error.injEq, SpecAMQP.Spec.Codec.refusal]
    decide

/-! ## The writer's witness

The reference's writer writes a fixed-width payload unchanged (`#[0x72] ++ payload`); the
specification's writer looks the payload's width up in the declared surface
(`rowOf "float" bits.size`) and refuses a width the surface does not declare. Values reach a writer
from a reader, so this witness is outside the corpus vocabulary — `valueOfJson` and `hexPayloadOf`
fix a `float`'s payload at four octets — and `ValueWriterAgree` quantifies over every pair of
values `BodiesAgree` relates, not only over the reachable ones. Another divergence in the same
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
      .error "the declared surface has no float encoding of width 0" := by
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
corpus vocabulary can produce that pair (`"constructor": "57"`), so this divergence is reachable
through the send instance's carrier, and it is the one that matters there. Both refuse; what
differs is the class, and the specification's is `unassigned` while the reference's is a catch-all
`limit` — and the specification's two *classless* refusals in this family (`.array %x00 [x]` and
`.array %xE0 [x]`) are a separate defect recorded in this module's report. -/

theorem ref_encode_arrayUnassigned :
    SpecAMQP.Ref.encode (.array 0x57 [.null]) =
      .error "limit: an array whose element constructor is 87 cannot carry a null" := by
  unfold SpecAMQP.Ref.encode SpecAMQP.Ref.arrayElementItems SpecAMQP.Ref.arrayElement
  try dsimp only []
  try (first | rfl | (split <;> first | rfl | simp_all))
  try decide

theorem spec_encodeValue_arrayUnassigned :
    SpecAMQP.Spec.Codec.encodeValue (.array 0x57 [.null]) =
      .error "unassigned: octet 0x57 lies in the fixed range of width 1 but the declared surface assigns it no encoding" := by
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
  try (first | rfl | (split <;> first | rfl | simp_all))

end SpecAMQP.Proofs
