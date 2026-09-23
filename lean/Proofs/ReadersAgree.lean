import Proofs.ConnectionConformance
import Proofs.ValueWireAgreement

/-!
# The connection layer's hypothesis, discharged

`Proofs.ConnectionConformance` declares the hypothesis its `Conforms` instance rests on — `ReadersAgree`,
the agreement of the two *frame* readers on every buffer — and records its status as an open question:
the frame layer's own instance had just become unconditional, and whether the connection layer's
hypothesis follows from that discharge "is an open question recorded here rather than assumed — answered
either by deriving it or by a buffer where the stronger relation fails while `ValueLayersAgree` holds."

This module answers it: **`readersAgree` below is `ReadersAgree`, with no hypotheses.** The hypothesis is
therefore a theorem of the tree rather than an assumption, `connection_conformance_public` is
dischargeable, and the connection layer's instance is unconditional in the same sense the frame layer's
became.

## Where the gap was, and why it was exactly the body relation

`ValueLayersAgree` — the frame layer's hypothesis, and now a theorem (`valueLayersAgree`) — states the
value readers' agreement in the *view* vocabulary: the same octets consumed, and a body the frame layer
reads the same way, `specBodyView body = refBodyView other`. `FramesAgree` asks for more of the same two
bodies: `ValuesAgree sb rb`, the whole value rather than the declared type its descriptor names. That
difference is not a technicality and cannot be closed by unfolding anything: a body's *contents* are not
determined by the type its descriptor names, so no lemma about views can produce `ValuesAgree` out of
`FrameAgrees`. What closes it is that the value layer's own development is *stronger than the claim it
exports*: `WireAgrees`/`StepAgrees` (`Proofs.ValueWireAgreement`) carries `BodiesAgree body other` on the
success conjunct and only weakens it to the view equality at the exported theorem — with
`bodyView_of_BodiesAgree` doing the weakening. So the missing step is in the other direction, from
`BodiesAgree` back up to `ValuesAgree`, and it does not exist in the tree: `BodiesAgree` is the corpus
side's relation (`Proofs.FrameSendConformance`), `ValuesAgree` is the connection layer's, and the two are
the same relation written twice. `valuesAgree_of_bodiesAgree` below is that step, and it is the only
place this module adds mathematics rather than plumbing.

The other half is plumbing, and it is plumbing over the *readers* rather than over the values: the value
law is stated at the readers' entry points (`readValue region.size ⟨region, 0⟩` on each side), while
`FramesAgree` is about the bodies the *frame* readers report. `ref_readFrame_body` and
`spec_readFrame_body` say what a frame reader puts in a frame's body — the value its layer's reader
answered on the body region, the octets `DOFF` places the body at to the end of the buffer — and
`bodiesAgree_of_decodes` puts the value law's answer and those two facts together. Nothing here decides
anything about frames: every frame-layer question is answered by `ref_answer_matched`, whose `FrameAgrees`
conjunct supplies every field of `FramesAgree` except the two about the body.

## What this module does not do

It does not touch `lean/Contracts`: `connection_conformance_public` still names `ReadersAgree` as its
hypothesis, because the contract's spelling is the planner's and a reader of it should still see what the
instance rests on. What changed is that the hypothesis is now dischargeable — `connection_conformance_public
SpecAMQP.Proofs.readersAgree` is the instance with nothing standing in — and wiring that into the
contract file is a planner edit rather than this module's.

## Why this is a module of its own

Because the proof needs the value layer's discharge, and `Proofs.ConnectionConformance` does not import
`Proofs.ValueWireAgreement`: that discharge is consumed at the *frame* layer, and the connection layer's
module declares the hypothesis rather than discharging it. A 278 KB module would gain a dependency on the
whole value law for a result about the layer beneath it, and the discharge of a hypothesis belongs beside
the layer that produces it.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Harness (Octets)

/-! ## The value layer's relation, in the connection layer's vocabulary

`BodiesAgree` and `ValuesAgree` are the same relation under two names: the same constructor, the same
payload equality in the reference's own width (`a = b.toNat`, `a = b.toInt`), the same elementwise
agreement on a compound's parts, and no `False` clause in either. The proof is a walk of the same case
tree the definition takes, one arm per constructor, and there is nothing to prove in an arm where the two
constructors differ: `BodiesAgree` is `False` there, so the hypothesis of the arm is already a
contradiction.

The arms that recurse carry the two auxiliary relations with them, because `BodiesAgree`'s compound arms
go through `BodiesAgreeList`/`BodiesAgreePairs` rather than through `BodiesAgree` directly, exactly as
`ValuesAgree`'s go through `List.Forall₂` of itself and of `PairAgree`. Hence the three motives in one
mutual block, and the `termination_by` measure `sizeOf` on both sides, which is `BodiesAgree`'s own. -/

mutual

/-- **Every pair of bodies the corpus side relates is a pair the connection layer relates.** The
`BodiesAgree` obligation the value law carries, read back in the relation `FramesAgree` states. -/
theorem valuesAgree_of_bodiesAgree : ∀ (a : SpecAMQP.Spec.Codec.Value) (b : SpecAMQP.Ref.Value),
    BodiesAgree a b → ValuesAgree a b
  | .null, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .null
  | .boolean a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .boolean h
  | .ubyte a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .ubyte h
  | .ushort a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .ushort h
  | .uint a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .uint h
  | .ulong a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .ulong h
  | .byte a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .byte h
  | .short a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .short h
  | .int a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .int h
  | .long a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .long h
  | .float a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .float h
  | .double a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .double h
  | .decimal32 a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .decimal32 h
  | .decimal64 a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .decimal64 h
  | .decimal128 a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .decimal128 h
  | .char a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .char h
  | .timestamp a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .timestamp h
  | .uuid a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .uuid h
  | .binary a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .binary h
  | .string a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .string h
  | .symbol a, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢; first | exact h.elim | exact .symbol h
  | .list xs, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢;
        first | exact h.elim | exact .list (forall₂_of_bodiesAgreeList _ _ h)
  | .map ps, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢;
        first | exact h.elim | exact .map (forall₂_of_bodiesAgreePairs _ _ h)
  | .array ca xs, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢;
        first | exact h.elim | exact .array h.1 (forall₂_of_bodiesAgreeList _ _ h.2)
  | .described d v, b, h => by
      cases b <;> simp only [BodiesAgree] at h ⊢;
        first
          | exact h.elim
          | exact .described (valuesAgree_of_bodiesAgree _ _ h.1)
              (valuesAgree_of_bodiesAgree _ _ h.2)
termination_by a b => sizeOf a + sizeOf b

/-- The list arm of the bridge, on `BodiesAgreeList`'s own recursion: item by item, in order. -/
theorem forall₂_of_bodiesAgreeList :
    ∀ (xs : List SpecAMQP.Spec.Codec.Value) (ys : List SpecAMQP.Ref.Value),
    BodiesAgreeList xs ys → List.Forall₂ ValuesAgree xs ys
  | [], [], _ => .nil
  | [], _ :: _, h => by simp only [BodiesAgreeList] at h
  | _ :: _, [], h => by simp only [BodiesAgreeList] at h
  | x :: xs, y :: ys, h => by
      simp only [BodiesAgreeList] at h
      exact .cons (valuesAgree_of_bodiesAgree x y h.1) (forall₂_of_bodiesAgreeList xs ys h.2)
termination_by xs ys => sizeOf xs + sizeOf ys

/-- The map arm, on `BodiesAgreePairs`': key by key and value by value, in the order the wire carried
them. -/
theorem forall₂_of_bodiesAgreePairs :
    ∀ (ps : List (SpecAMQP.Spec.Codec.Value × SpecAMQP.Spec.Codec.Value))
      (qs : List (SpecAMQP.Ref.Value × SpecAMQP.Ref.Value)),
    BodiesAgreePairs ps qs → List.Forall₂ PairAgree ps qs
  | [], [], _ => .nil
  | [], _ :: _, h => by simp only [BodiesAgreePairs] at h
  | _ :: _, [], h => by simp only [BodiesAgreePairs] at h
  | (k, v) :: ps, (k', v') :: qs, h => by
      simp only [BodiesAgreePairs] at h
      exact .cons (.mk (valuesAgree_of_bodiesAgree k k' h.1) (valuesAgree_of_bodiesAgree v v' h.2.1))
        (forall₂_of_bodiesAgreePairs ps qs h.2.2)
termination_by ps qs => sizeOf ps + sizeOf qs

end

/-! ## What each frame reader puts in a frame's body

Each frame layer reads a frame's body region — from the octets `DOFF` places the body at to the end of the
buffer, the region `ValueLayersAgree`'s own statement names — with its own value reader, and the frame it
reports carries that reader's answer as its body. These two lemmas are that fact in the shape the
`FramesAgree` clause needs: a frame whose body is `some body` was read from a region the layer's value
reader answered `ok body` on. They are walks of each reader's own decision tree, and the branch that
accepts with a body is the only one that can satisfy the hypothesis: every refusal contradicts the frame
equation, and the empty frame carries `body := none`.

The two lemmas name the region with the *specification's* `beAt`, which is the reference's by
`beAt_eq`, so that the region term is one term for both and the value law can be consulted at it. -/

/-- The reference's frame reader, on a buffer it accepted with a body: that body is what the reference's
value reader answered on the frame's body region. -/
theorem ref_readFrame_body (bytes : Octets) (rframe : SpecAMQP.Ref.Frame.Frame)
    (used : Nat) (rb : SpecAMQP.Ref.Value)
    (h : SpecAMQP.Ref.Frame.readFrame bytes = .ok (rframe, used))
    (hb : rframe.body = some rb) :
    ∃ x, SpecAMQP.Ref.decode (bytes.extract (SpecAMQP.Spec.Frame.beAt bytes 4 1 * 4) bytes.size)
      = .ok (rb, x) := by
  unfold SpecAMQP.Ref.Frame.readFrame at h
  simp only [SpecAMQP.Ref.Frame.wordOctets] at h
  repeat' split at h
  all_goals try simp at h
  all_goals (rcases h with ⟨rfl, -⟩; simp_all [beAt_eq])

/-- The specification's frame reader, the same statement on the other reader. -/
theorem spec_readFrame_body (bytes : Octets) (sframe : SpecAMQP.Spec.Frame.Frame) (consumed : Nat)
    (sb : SpecAMQP.Spec.Codec.Value)
    (h : SpecAMQP.Spec.Frame.readFrame bytes = .ok (sframe, consumed))
    (hb : sframe.body = some sb) :
    ∃ x, SpecAMQP.Spec.Codec.decodeValue
        (bytes.extract (SpecAMQP.Spec.Frame.beAt bytes 4 1 * 4) bytes.size) = .ok (sb, x) := by
  unfold SpecAMQP.Spec.Frame.readFrame at h
  simp only [] at h
  repeat' split at h
  all_goals try simp at h
  all_goals rcases h with ⟨rfl, -⟩
  all_goals simp_all [SpecAMQP.Spec.Frame.bodyStart, SpecAMQP.Spec.Frame.declaredDoff,
    SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.doffWord,
    SpecAMQP.Spec.Frame.doffOctets, SpecAMQP.Spec.Frame.sizeOctets,
    SpecAMQP.Spec.Frame.headerOctets]

/-! ## Two bodies read from one buffer agree

The value law (`Proofs.ValueWireAgreement`) is about `readValue` at the two entry-point cursors, and the
two decoders are those cursors with the consumed position projected out; these three lemmas are the
whole of that accounting, and then the law's `BodiesAgree` conjunct is used exactly as it is stated. -/

/-- `decodeValue` is `readValue` at the buffer's own fuel, with the value and the position the read
consumed. -/
private theorem spec_decodeValue_readValue {bytes : Octets} {value : SpecAMQP.Spec.Codec.Value}
    {n : Nat} (h : SpecAMQP.Spec.Codec.decodeValue bytes = .ok (value, n)) :
    ∃ c, SpecAMQP.Spec.Codec.readValue bytes.size ⟨bytes, 0⟩ = .ok (value, c) ∧ c.pos = n := by
  cases hr : SpecAMQP.Spec.Codec.readValue bytes.size ⟨bytes, 0⟩ with
  | ok p =>
    obtain ⟨v, c⟩ := p
    unfold SpecAMQP.Spec.Codec.decodeValue at h
    rw [hr] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, hn⟩ := h
    exact ⟨c, by rw [hv], hn⟩
  | error e =>
    unfold SpecAMQP.Spec.Codec.decodeValue at h
    rw [hr] at h
    exact absurd h (by simp)

/-- And the reference's, the same statement on the other decoder. -/
private theorem ref_decode_readValue {bytes : Octets} {value : SpecAMQP.Ref.Value} {n : Nat}
    (h : SpecAMQP.Ref.decode bytes = .ok (value, n)) :
    ∃ c, SpecAMQP.Ref.readValue bytes.size ⟨bytes, 0⟩ = .ok (value, c) ∧ c.pos = n := by
  cases hr : SpecAMQP.Ref.readValue bytes.size ⟨bytes, 0⟩ with
  | ok p =>
    obtain ⟨v, c⟩ := p
    unfold SpecAMQP.Ref.decode at h
    rw [hr] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, hn⟩ := h
    exact ⟨c, by rw [hv], hn⟩
  | error e =>
    unfold SpecAMQP.Ref.decode at h
    rw [hr] at h
    exact absurd h (by simp)

/-- **The bodies two decoders read from one buffer agree.** The value law at the buffer's own fuel —
`region.size - 0 ≤ region.size` is its bound's base case and the two initial cursors are the same buffer
at the same position — with each decoder turned into the `readValue` the law is stated on. The two reads
land on the same value, which is what makes the law's `BodiesAgree` a statement about the two decoders'
answers rather than about two terms that merely reduce to them. -/
theorem bodiesAgree_of_decodes {region : Octets} {sb : SpecAMQP.Spec.Codec.Value}
    {rb : SpecAMQP.Ref.Value} {c d : Nat}
    (hs : SpecAMQP.Spec.Codec.decodeValue region = .ok (sb, c))
    (hr : SpecAMQP.Ref.decode region = .ok (rb, d)) : BodiesAgree sb rb := by
  obtain ⟨cs, hcs, -⟩ := spec_decodeValue_readValue hs
  obtain ⟨cr, hcr, -⟩ := ref_decode_readValue hr
  obtain ⟨body, c₂, hspec, -, -, hba⟩ :=
    (wireAgrees_all region.size ⟨region, 0⟩ ⟨region, 0⟩ ⟨rfl, rfl⟩ (by simp)).1 rb cr hcr
  rw [hcs] at hspec
  obtain ⟨hbody, -⟩ := Prod.mk.inj (Except.ok.inj hspec)
  rw [← hbody] at hba
  exact hba

/-! ## The discharge -/

/-- **The connection layer's hypothesis, proved.** For every buffer: whatever the reference's frame
reader reads, the specification's frame reader reads with the same extent and a frame `FramesAgree`
relates — the layout's fields and the frame type as the frame layer already had them from
`ref_answer_matched`, the two bodies agreeing under `ValuesAgree` by the value law and the bridge above,
and the frame's own empty/non-empty choice the same on both sides, which is the frame layer's body-view
equality read through `Option.map`; and on a refusal, the same reason class.

The refusal half is `ref_answer_matched`'s second conjunct unchanged: `ValueLayersAgree` was always enough
for it. The accept half is `ref_answer_matched`'s first conjunct with its `FrameAgrees` conjunct kept, and
its body-view conjunct replaced by the stronger relation `FramesAgree` states. -/
theorem readersAgree : ReadersAgree := by
  intro bytes
  refine ⟨?_, (ref_answer_matched valueLayersAgree bytes).2⟩
  intro rframe used hok
  obtain ⟨sframe, consumed, hread, hcount, hfa⟩ :=
    (ref_answer_matched valueLayersAgree bytes).1 rframe used hok
  refine ⟨sframe, consumed, hread, hcount, ?_⟩
  obtain ⟨hdoff, hkind, hchannel, hextended, hmap, hpayload⟩ := hfa
  refine ⟨hdoff, hkind, hchannel, hextended, hpayload, ?_, ?_⟩
  · intro sb rb hsb hrb
    obtain ⟨c, hdec⟩ := spec_readFrame_body bytes sframe consumed sb hread hsb
    obtain ⟨d, hrd⟩ := ref_readFrame_body bytes rframe used rb hok hrb
    exact valuesAgree_of_bodiesAgree sb rb (bodiesAgree_of_decodes hdec hrd)
  · constructor
    · intro hnone
      rw [hnone] at hmap
      simpa using hmap.symm
    · intro hnone
      rw [hnone] at hmap
      simpa using hmap

end SpecAMQP.Proofs
