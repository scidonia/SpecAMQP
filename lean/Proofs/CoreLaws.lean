/-
# Laws about the core's framing, where they need the proof library

`Impl.Stream` states what the byte-stream front end does and proves the laws that need nothing but its own
definitions: a unit is at least a header and at most the buffer, the loop stops with nothing complete left,
its remainder is a suffix of what arrived, and the framer's decision does not depend on octets that have not
arrived. This module holds the laws that need the *specification*'s own results — the reader's declared
extent, and the header decoder's dependence on eight octets — and it lives in `lean/Proofs/` rather than in
`lean/Impl/` for that reason alone: `Impl` is shipped code and must not depend on the proof library.

## What the laws say, and why the core needs them

The front end's whole decision is *how far to advance*. `Spec.Connection.step` hands the connection layer
the octets that arrived and does not report how many of them it consumed — `readFrame`'s count is passed to
`stepAmqpFrame` as a size and is not carried by the `Outcome` — so the advance is the core's own
computation, and what makes it the *specification's* arithmetic rather than ours is that the number it
computes **is** the extent the specification's own reader reports:

* `readFrame_ok_consumed_eq_declaredSize` and `frameExtent_eq_consumed_of_accepts`: where the reader accepts
  a frame, the octets it consumed are the `SIZE` the frame declares and the frame's extent is the same
  number. The loop therefore steps past exactly the frame the layer read — not a byte further, not a byte
  short — and it does so by asking `Spec.Frame.frameExtent`, which is the layout's arithmetic stated once in
  the module that owns the layout.
* `decodeHeader_extract`: where a header is due, the eight octets the framer takes carry the header —
  `decodeHeader` decides everything, including the magic it refuses on, from the first eight octets of a
  buffer — so the answer to the whole buffer and to its own header-octet prefix are the same answer.

## The obligation these laws do not discharge, stated rather than assumed

Stream safety — feeding a stream in one read equals feeding it in two — needs more than the framer's
decision being prefix-determined (which `Impl.Stream.nextUnitLength_prefix` and
`Impl.Stream.frameExtent_append` do prove). It needs the *layer's answer* to depend on the frame's own
window, and that is not a fact about this core:

* **`ValuePrefixDetermined`** below is the value reader's half: what a reader that succeeds consumes, and
  what it produces, do not change when the region is extended. Nothing in this tree proves it —
  `Proofs.ReadProgress.lean` proves cursor *progress*, not prefix determinacy — and it is the hypothesis of
  the frame-level statement.
* **`FrameWindowAgreed`** below is the frame-level statement itself, and one of the two things that stood
  in its way is now gone: the value layer's refusals carry their reason class as a **field**
  (`Spec.Codec.Refusal`), so the frame layer reads a class rather than recovering one from a message by
  `String.splitOn` — which no kernel proof could have reasoned about. What remains is the value reader's
  prefix determinacy, above.

Both are stated as `Prop`s with no proof and no axiom: what this module claims is everything above them,
and what it reports is their exact shape.
-/

import Impl.Stream

namespace SpecAMQP.Proofs

open SpecAMQP.Harness (Octets)

/-- The frame layer's field reads do not move when the octets after them move: a field at an offset the
shorter buffer already covers is the same field in the longer one. Stated for a buffer that is itself a
prefix of the buffer being read, which is the shape `decodeHeader_extract` needs. -/
theorem beAt_extract (inbox : Octets) (bound start width : Nat)
    (h : start + width ≤ bound) :
    SpecAMQP.Spec.Frame.beAt (inbox.extract 0 bound) start width =
      SpecAMQP.Spec.Frame.beAt inbox start width := by
  unfold SpecAMQP.Spec.Frame.beAt
  rw [Array.extract_extract]
  rw [show min (0 + (start + width)) bound = start + width from by omega]
  simp

/-- The connection layer's big-endian reader and the frame layer's are the same function, defined twice in
the specification. The core reads the layout's fields with the frame layer's, and the header decoder uses
its own, so the two are named here rather than left to be discovered at a proof site. -/
theorem connection_beAt_eq_frame_beAt (bytes : Octets) (start width : Nat) :
    SpecAMQP.Spec.Connection.beAt bytes start width =
      SpecAMQP.Spec.Frame.beAt bytes start width := rfl

/-- `beAt_extract` for the reader `decodeHeader` itself uses. -/
theorem beAt_extract_connection (inbox : Octets) (bound start width : Nat)
    (h : start + width ≤ bound) :
    SpecAMQP.Spec.Connection.beAt (inbox.extract 0 bound) start width =
      SpecAMQP.Spec.Connection.beAt inbox start width := by
  rw [connection_beAt_eq_frame_beAt, connection_beAt_eq_frame_beAt]
  exact beAt_extract inbox bound start width h

/--
**The eight octets the framer takes are the header.** `decodeHeader` decides everything — the layout's
width, the magic, the protocol id and its layer, and the three version octets — from the first eight octets
of a buffer. A buffer and its own eight-octet prefix are therefore read as the same header, or refused for
the same reason with the same message.

This is what makes the header branch of `nextUnitLength` faithful: the loop hands the layer the octets that
arrived (never a slice), and this says the answer it gets is the answer to the header the framer delimited.
-/
theorem decodeHeader_extract (inbox : Octets) (h : SpecAMQP.Spec.Frame.headerOctets ≤ inbox.size) :
    SpecAMQP.Spec.Connection.decodeHeader (inbox.extract 0 SpecAMQP.Spec.Frame.headerOctets) =
      SpecAMQP.Spec.Connection.decodeHeader inbox := by
  have hsize : (inbox.extract 0 SpecAMQP.Spec.Frame.headerOctets).size =
      SpecAMQP.Spec.Frame.headerOctets := by
    rw [Array.size_extract, min_eq_left h, Nat.sub_zero]
  have hmagic : (inbox.extract 0 SpecAMQP.Spec.Frame.headerOctets).extract 0 4 =
      inbox.extract 0 4 := by
    rw [Array.extract_extract]
    rw [show min (0 + 4) SpecAMQP.Spec.Frame.headerOctets = 4 from by
      simp [SpecAMQP.Spec.Frame.headerOctets]]
  have hshort : ¬ (inbox.extract 0 SpecAMQP.Spec.Frame.headerOctets).size <
      SpecAMQP.Spec.Connection.headerOctets := by
    rw [hsize]
    simp [SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Connection.headerOctets]
  have h4 : SpecAMQP.Spec.Connection.beAt (inbox.extract 0 SpecAMQP.Spec.Frame.headerOctets) 4 1 =
      SpecAMQP.Spec.Connection.beAt inbox 4 1 := by
    apply beAt_extract_connection
    simp [SpecAMQP.Spec.Frame.headerOctets]
  have h5 : SpecAMQP.Spec.Connection.beAt (inbox.extract 0 SpecAMQP.Spec.Frame.headerOctets) 5 1 =
      SpecAMQP.Spec.Connection.beAt inbox 5 1 := by
    apply beAt_extract_connection
    simp [SpecAMQP.Spec.Frame.headerOctets]
  have h6 : SpecAMQP.Spec.Connection.beAt (inbox.extract 0 SpecAMQP.Spec.Frame.headerOctets) 6 1 =
      SpecAMQP.Spec.Connection.beAt inbox 6 1 := by
    apply beAt_extract_connection
    simp [SpecAMQP.Spec.Frame.headerOctets]
  have h7 : SpecAMQP.Spec.Connection.beAt (inbox.extract 0 SpecAMQP.Spec.Frame.headerOctets) 7 1 =
      SpecAMQP.Spec.Connection.beAt inbox 7 1 := by
    apply beAt_extract_connection
    simp [SpecAMQP.Spec.Frame.headerOctets]
  have hshortInbox : ¬ inbox.size < SpecAMQP.Spec.Connection.headerOctets := by
    simp only [SpecAMQP.Spec.Frame.headerOctets, SpecAMQP.Spec.Connection.headerOctets] at h ⊢
    omega
  unfold SpecAMQP.Spec.Connection.decodeHeader
  rw [if_neg hshort, if_neg hshortInbox, hmagic, h4, h5, h6, h7]

/--
**A reader that accepts a frame consumed the `SIZE` it declares.** Where the reader succeeds, the count it
reports is the frame's declared size — the octets the frame occupies, which is the number the loop advances
by.

This is the same fact as the accepted contract `Contracts.consumed_is_the_declared_size` (proved in
`Proofs.CodecFrameLaws`), stated here against `Spec.Frame.declaredSize`: the two are one fact, and this one
is derived from the reader's own shape so that this module's laws do not depend on the module that states it
in terms of the raw field read.
-/
theorem readFrame_ok_facts {bytes : Octets} {frame : SpecAMQP.Spec.Frame.Frame} {consumed : Nat}
    (hr : SpecAMQP.Spec.Frame.readFrame bytes = .ok (frame, consumed)) :
    consumed = SpecAMQP.Spec.Frame.declaredSize bytes ∧ consumed ≤ bytes.size := by
  unfold SpecAMQP.Spec.Frame.readFrame at hr
  simp only [] at hr
  all_goals (repeat' split at hr)
  all_goals first
    | (cases hr; exact ⟨rfl, Nat.le_of_not_lt (by assumption)⟩)
    | (exact absurd hr (by intro he; cases he))

/-- The count the reader reports is the frame's declared `SIZE` — the law above, split out for a caller
that wants only the count. -/
theorem readFrame_ok_consumed_eq_declaredSize {bytes : Octets} {frame : SpecAMQP.Spec.Frame.Frame}
    {consumed : Nat} (hr : SpecAMQP.Spec.Frame.readFrame bytes = .ok (frame, consumed)) :
    consumed = SpecAMQP.Spec.Frame.declaredSize bytes :=
  (readFrame_ok_facts hr).1

/--
**The advance is the specification's own consumption.** Where the frame layer's reader accepts a frame from
the front of a buffer, the frame's extent — `Spec.Frame.frameExtent`, the number the front end advances by —
is exactly the `SIZE` the frame declares, i.e. the octets `readFrame` reports as consumed. The loop
therefore steps past exactly the frame the layer read.

The acceptance is all this needs: `Spec.Frame.readFrame_ok_declarationConsistent` gives the declaration's
self-consistency (which is what selects the extent's branch) and the count law above gives the number.
-/
theorem frameExtent_eq_consumed_of_accepts {bytes : Octets} {frame : SpecAMQP.Spec.Frame.Frame}
    {consumed : Nat} (hr : SpecAMQP.Spec.Frame.readFrame bytes = .ok (frame, consumed)) :
    SpecAMQP.Spec.Frame.frameExtent bytes = consumed := by
  rw [SpecAMQP.Spec.Frame.frameExtent_eq_declaredSize
      (SpecAMQP.Spec.Frame.readFrame_ok_declarationConsistent hr),
    readFrame_ok_consumed_eq_declaredSize hr]

/--
The same law where the loop asks for it: with a frame due, a buffer that is not header-shaped and a header
held, the extent the framer names is the octets the specification's reader consumed — so the front end's
waiting rule (`none` while the buffer is shorter than the extent) waits exactly where the reader would say
the frame is not all there yet.
-/
theorem nextUnitLength_eq_consumed {state : SpecAMQP.Spec.Connection.State} {inbox : Octets}
    {frame : SpecAMQP.Spec.Frame.Frame} {consumed : Nat}
    (hs : state.receiveClass ≠ .header)
    (hh : ¬ SpecAMQP.Spec.Connection.headerShaped inbox)
    (h8 : SpecAMQP.Spec.Frame.headerOctets ≤ inbox.size)
    (hr : SpecAMQP.Spec.Frame.readFrame inbox = .ok (frame, consumed)) :
    SpecAMQP.Impl.Stream.nextUnitLength state inbox = some consumed := by
  obtain ⟨_hcnt, hle⟩ := readFrame_ok_facts hr
  have hext : SpecAMQP.Spec.Frame.frameExtent inbox = consumed := frameExtent_eq_consumed_of_accepts hr
  have hshort : ¬ inbox.size < SpecAMQP.Impl.Stream.headerOctets := by
    simp only [SpecAMQP.Impl.Stream.headerOctets, SpecAMQP.Spec.Frame.headerOctets] at h8 ⊢
    omega
  have hwait : ¬ inbox.size < SpecAMQP.Spec.Frame.frameExtent inbox := by
    rw [hext]
    omega
  unfold SpecAMQP.Impl.Stream.nextUnitLength
  rw [if_neg hs, if_neg hshort, if_neg hh, if_neg hwait, hext]

/-! ## The obligations left open, stated exactly -/

/-- **The value reader's prefix determinacy**, as the frame layer needs it: a reader that succeeds on a
region consumes the same octets and produces the same value when the region is extended.

Nothing in this tree proves it. `Proofs.ReadProgress.lean` proves that the reader's cursor never moves
backwards, which is a different property; the frame layer's stream safety, on the other hand, needs this
one, because the reader is handed the octets that arrived rather than a slice of them. Stating it as a
`Prop` here is what makes the residual an obligation with a shape instead of a sentence in a report. -/
def ValuePrefixDetermined : Prop :=
  ∀ (region more : Octets) (value : SpecAMQP.Spec.Codec.Value) (consumed : Nat),
    SpecAMQP.Spec.Codec.decodeValue region = .ok (value, consumed) →
    SpecAMQP.Spec.Codec.decodeValue (region ++ more) = .ok (value, consumed)

/-- **The frame layer's answer is the answer to the frame's window.** Whenever the reader's answer to a
buffer is final within the frame's own extent — an `.ok`, or an `.error` whose reason class is the class of
the same defect — reading the buffer's window `bytes.extract 0 (Spec.Frame.frameExtent bytes)` gives the
same answer.

Two things stand between this and a proof, and both are named rather than glossed:

The one thing that stands between this and a proof is `ValuePrefixDetermined`, for the branch where the
reader accepts: the body region runs to the end of the *buffer* on purpose ("so a buffer may hold a
following frame"), so the accepted frame being the same one is exactly the value reader's prefix
determinacy. The class half of the gap was closed on the value layer's side while this law was being
written — `Spec.Codec`'s refusals now carry `reasonClass` as a field, so the frame layer's class is readable
rather than prose — and the geometry half is proved (`Impl.Stream.frameExtent_append`,
`Impl.Stream.nextUnitLength_prefix`, `Spec.Frame.declarationConsistent_eq_true_iff`).

What is proved on the way to it is in `Impl.Stream` and above: the framer's decision *is* prefix-determined
(`frameExtent_append`, `nextUnitLength_prefix`), and where the reader accepts, the extent is the reader's
own consumed count. -/
def FrameWindowAgreed : Prop :=
  ∀ (bytes : Octets),
    (SpecAMQP.Spec.Frame.readFrame
        (bytes.extract 0 (SpecAMQP.Spec.Frame.frameExtent bytes))).isOk =
      (SpecAMQP.Spec.Frame.readFrame bytes).isOk

end SpecAMQP.Proofs
