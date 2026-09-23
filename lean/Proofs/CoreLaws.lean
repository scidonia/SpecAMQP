/-
# Laws about the core's framing, where they need the proof library

`Impl.Stream` states what the byte-stream front end does and proves the laws that need nothing but its
own definitions: a unit is at least a header and at most the buffer, the loop stops with nothing complete
left, its remainder is a suffix of what arrived, and the framer's decision does not depend on octets that
have not arrived. This module holds the laws that need the *specification's* own results — one of them
`Proofs.CodecFrameLaws.consumed_is_the_declared_size`, already an accepted contract — and it lives in
`lean/Proofs/` rather than in `lean/Impl/` for that reason alone: `Impl` is shipped code and must not
depend on the proof library.

## What the laws say, and why the core needs them

The front end's whole decision is *how far to advance*. `Spec.Connection.step` hands the connection layer
the octets that arrived and does not report how many of them it consumed — `readFrame`'s count is passed
to `stepAmqpFrame` as a size and is not carried by the `Outcome` — so the advance is the core's own
computation, and what makes it the *specification's* arithmetic rather than ours is that it agrees with
the specification's own reader:

* `frameExtent_eq_consumed`: where the frame layer's reader accepts a frame from the front of a buffer,
  the advance is exactly the `SIZE` the frame declares — the octets that frame occupies, which is what
  `readFrame` reports as its consumed count. The loop therefore steps past exactly the frame the layer
  read: not one byte further, and not one byte short.
* `decodeHeader_extract`: where a header is due, the eight octets the framer takes carry the header —
  `decodeHeader` decides everything from the first eight octets of a buffer — so the answer to the whole
  buffer and the answer to its own header-octet prefix are the same answer.

Both are laws about the *framer*. The loop's remaining gap — that its answers are the same however the
transport split the stream — is the *layer's* suffix-independence (does a decoder that accepts a frame
accept the same frame when more octets follow it?), which nothing in this tree proves today; R2's report
names it as an obligation with its exact statement rather than assuming it here.
-/

import Impl.Stream
import Proofs.CodecFrameLaws
import Contracts.FrameCodec

namespace SpecAMQP.Proofs

open SpecAMQP.Harness (Octets)

/-- A big-endian field read at an offset the buffer covers is the same field in a buffer that extends it:
the octets after it move and the field does not. -/
theorem beAt_extract (inbox : Octets) (bound start width : Nat)
    (h : start + width ≤ bound) :
    SpecAMQP.Spec.Frame.beAt (inbox.extract 0 bound) start width =
      SpecAMQP.Spec.Frame.beAt inbox start width := by
  unfold SpecAMQP.Spec.Frame.beAt
  rw [Array.extract_extract]
  rw [show min (0 + (start + width)) bound = start + width from by omega]
  simp

/-- The connection layer's big-endian reader and the frame layer's are the same function, defined twice
in the specification. The core reads the layout's fields with the frame layer's, and the header decoder
uses its own, so the two are named here rather than left to be discovered at a proof site. -/
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
width, the magic, the protocol id and its layer, and the three version octets — from the first eight
octets of a buffer. A buffer and its own eight-octet prefix are therefore read as the same header, or
refused for the same reason with the same message.

This is what makes the header branch of `nextUnitLength` faithful: the loop hands the layer the octets
that arrived (never a slice), and this says the answer it gets is the answer to the header the framer
delimited.
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
**The advance is the specification's own consumption.** Where the frame layer's reader accepts a frame
from the front of a buffer — and the buffer does not begin with the header magic, which the connection
layer refuses before it reads any frame — the extent `frameExtent` computes is exactly the octets that
frame occupies: the `SIZE` the layout declares, which is the count `readFrame` reports.

The acceptance itself supplies the arithmetic: the four checks the reader makes before it reads a body
are exactly the conditions that make the framer trust the declaration, so the two agree by construction
rather than by a shared table of cases.
-/
theorem frameExtent_eq_consumed {inbox : Octets} {frame : SpecAMQP.Spec.Frame.Frame} {consumed : Nat}
    (hh : ¬ SpecAMQP.Spec.Connection.headerShaped inbox)
    (hr : SpecAMQP.Spec.Frame.readFrame inbox = .ok (frame, consumed)) :
    SpecAMQP.Impl.Stream.frameExtent inbox = some consumed := by
  have hdecl := SpecAMQP.Proofs.consumed_is_the_declared_size inbox frame consumed
    ((SpecAMQP.Spec.Frame.decodeFrame_eq_ok_iff inbox frame consumed).mpr hr)
  obtain ⟨hsize, hge, hle⟩ := hdecl
  -- two of the reader's checks are already in the contract: the declared size is at least a header and
  -- at most the buffer it was read from
  have hsize8 : SpecAMQP.Spec.Frame.headerOctets ≤ inbox.size := le_trans hge hle
  have hshort8 : ¬ inbox.size < SpecAMQP.Spec.Frame.headerOctets := by omega
  have hsizeOk : ¬ (SpecAMQP.Spec.Frame.beAt inbox 0 SpecAMQP.Spec.Frame.sizeOctets <
      SpecAMQP.Spec.Frame.headerOctets) := by rw [← hsize]; omega
  have hwaitOk : ¬ (inbox.size < SpecAMQP.Spec.Frame.beAt inbox 0 SpecAMQP.Spec.Frame.sizeOctets) := by
    rw [← hsize]; omega
  -- The other two checks are the reader's own arithmetic contradictions, and acceptance is exactly
  -- their negation: assuming one turns `readFrame` into the refusal it raises, which contradicts `hr`.
  -- The reader is a `do` block, so its checks are reached by the same case split the frame layer's own
  -- proof uses, and each branch is closed by whichever of the two refutations applies.
  have hdoff : ¬ (SpecAMQP.Spec.Frame.beAt inbox 4 SpecAMQP.Spec.Frame.doffOctets <
      SpecAMQP.Spec.Frame.minDoff) := by
    intro hbad
    unfold SpecAMQP.Spec.Frame.readFrame at hr
    simp only [] at hr
    all_goals (repeat' split at hr)
    all_goals first
      | (exact absurd hbad (by assumption))
      | (exact absurd hr (by intro h; cases h))
  have hbody : ¬ (SpecAMQP.Spec.Frame.beAt inbox 0 SpecAMQP.Spec.Frame.sizeOctets <
      SpecAMQP.Spec.Frame.bodyStart (SpecAMQP.Spec.Frame.beAt inbox 4
        SpecAMQP.Spec.Frame.doffOctets)) := by
    intro hbad
    unfold SpecAMQP.Spec.Frame.readFrame at hr
    simp only [] at hr
    all_goals (repeat' split at hr)
    all_goals first
      | (exact absurd hbad (by assumption))
      | (exact absurd hr (by intro h; cases h))
  unfold SpecAMQP.Impl.Stream.frameExtent
  dsimp only
  rw [if_neg hshort8]
  rw [if_neg hh, if_neg hsizeOk, if_neg hdoff, if_neg hbody, if_neg hwaitOk]
  rw [hsize]

/--
The same law where the loop asks for it: with a frame due and a buffer that is not header-shaped, the
extent the framer names is the octets the specification's reader consumed.
-/
theorem nextUnitLength_eq_consumed {state : SpecAMQP.Spec.Connection.State} {inbox : Octets}
    {frame : SpecAMQP.Spec.Frame.Frame} {consumed : Nat}
    (hs : state.receiveClass ≠ .header)
    (hh : ¬ SpecAMQP.Spec.Connection.headerShaped inbox)
    (hr : SpecAMQP.Spec.Frame.readFrame inbox = .ok (frame, consumed)) :
    SpecAMQP.Impl.Stream.nextUnitLength state inbox = some consumed := by
  unfold SpecAMQP.Impl.Stream.nextUnitLength
  rw [if_neg hs]
  exact frameExtent_eq_consumed hh hr

end SpecAMQP.Proofs
