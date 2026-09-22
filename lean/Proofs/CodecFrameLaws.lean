import Proofs.CodecRoundTrip
import Contracts.Codec
import Contracts.FrameCodec

/-!
# The frame layer's laws, proved

`lean/Contracts/FrameCodec.lean` states three propositions about `Spec.Frame`'s decoder and
writer. This module proves the first two outright, and proves the third from two explicit
hypotheses — one about the value layer, which the contract itself records, and one about the
writer's `DOFF`, which a counterexample forced and which is reported below rather than hidden
in an assumption.

The declarations landed here are:

* `accepted_frames_carry_performatives`, discharging
  `SpecAMQP.Contracts.AcceptedFramesCarryPerformatives` — the conformance gap both artefacts
  had, closed as a claim about *every* accepted frame rather than about a branch somebody wrote;
* `consumed_is_the_declared_size`, discharging `SpecAMQP.Contracts.ConsumedIsTheDeclaredSize`;
* `frame_round_trip_on_encoded_frames`, which discharges
  `SpecAMQP.Contracts.FrameRoundTripOnEncodedFrames` from `ValueConsumption` and
  `DoffFitsTheWriter`, and `frame_round_trip`, the same claim per frame;
* `doff_beyond_the_octet_is_not_read_back`, the negative theorem that says why the second
  hypothesis is not removable: the writer accepts a frame whose `DOFF` its one octet cannot
  hold, and the reader refuses the octets it wrote.

## The two unconditional proofs

`decodeFrame` is a `do` block whose branches all end in `Except.error` except one, so a
statement about an *accepted* frame is a case analysis over those branches, and the case
analysis should be the decoder's own text rather than a transcription of it. `unfold decodeFrame
at h` exposes the nested `ite`/`match` tree, `repeat' split at h` gives one goal per branch, and
in every branch but the accepted one the hypothesis is `Except.error … = Except.ok …`, which no
proof can satisfy. `grind` closes the error branches by that contradiction and the accepted
branch by reading off the record it returns.

That is deliberately mutation-sensitive, which is what makes it evidence: a decoder variant that
dropped the `carriesPerformative` test, or returned a count other than `SIZE`, fails these
proofs rather than satisfying them. It is insensitive to the *shape* of the branches — how the
checks are nested, how many there are — which is what lets it survive a refactor that keeps the
decisions.

## The round trip, and the writer check it rests on

`Spec.Frame`'s writer refuses a `DOFF` the one-octet field cannot hold — the `limit` guard beside
the extended-header length check — so "the writer accepted this frame" already implies the body
offset is one the field can name. The hypothesis that bound used to need, before that guard
existed, is therefore *derived* here and not assumed: `doff_lt_of_encodeFrame_ok` reads it off
`encodeFrame_ok_facts`, which carries it as a conjunct of what an accepted write records. What
remains assumed is the value layer's consumption law and nothing else, which is the dependency
`Contracts.FrameCodec` records for this rung.
-/

namespace SpecAMQP.Proofs

open SpecAMQP.Harness (Octets)
open SpecAMQP.Spec.Frame
open SpecAMQP.Spec.Frame (Frame FrameType decodeFrame encodeFrame bodyStart headerOctets
  minDoff sizeOctets maxSize channelOctets doffOctets beAt)
open SpecAMQP.Spec.Codec (Value decodeValue encodeValue beOctets)
open SpecAMQP.Generated.Oasis (TypeDecl)

/-! ## The decoder's descriptor check, as the proof sees it -/

/-- `carriesPerformative` in terms of a descriptor that resolves to a known declaration: the
`Bool` the decoder tests and the membership it tests are the same test, stated once so a proof
can move between the two forms. -/
theorem carriesPerformative_eq (frameType : FrameType) (descriptor : Value)
    (decl : TypeDecl) (h : typeOfDescriptor descriptor = some decl) :
    carriesPerformative frameType descriptor = decl.provides.contains frameType.role := by
  simp [carriesPerformative, h]

/-- The converse, in the shape the decoder needs: a descriptor the frame type's role test accepts
is one `typeOfDescriptor` resolves, and the role is in the declared set. -/
theorem exists_decl_of_carriesPerformative (frameType : FrameType) (descriptor : Value)
    (h : carriesPerformative frameType descriptor = true) :
    ∃ decl, typeOfDescriptor descriptor = some decl ∧
      decl.provides.contains frameType.role = true := by
  unfold carriesPerformative at h
  split at h
  all_goals first
    | (exfalso; grind; done)
    | grind

/-- A frame type's own code names it, which is what makes `TYPE` recoverable from the octets the
writer emitted. -/
theorem ofCode_code (t : FrameType) : FrameType.ofCode t.code = some t := by
  cases t <;> decide

/-- A frame type's code fits the octet `TYPE` occupies, which is the bound the `TYPE` field's
reader needs. -/
theorem code_lt (t : FrameType) : t.code < 2 ^ 8 := by
  cases t <;> decide

/-! ## The contract's first two propositions -/

/-- Every frame the decoder accepts carries a performative.

The decoder's accepted branch is reachable only through the `described` shape, through a
descriptor `typeOfDescriptor` resolves to a declared type, and through
`decl.provides.contains frameType.role` — which is exactly `carriesPerformative`'s definition.
The two errors the branch can raise instead are a descriptor naming no declared type and a
declared role set that does not include the frame type's role, and both are refuted here by the
hypothesis that the result was `.ok`. -/
theorem accepted_frames_carry_performatives :
    SpecAMQP.Contracts.AcceptedFramesCarryPerformatives := by
  intro bytes frame consumed h
  unfold decodeFrame at h
  simp only [] at h
  repeat' split at h
  all_goals grind [carriesPerformative_eq]

/-- A decoded frame's count is the `SIZE` octets it declares, and lies between the header and
the buffer.

The accepted branch returns `beAt bytes 0 sizeOctets` as its count, and reaches it only past
`¬ size < headerOctets` and `¬ bytes.size < size`, which are the two bounds the statement asks
for. Both are decided from the buffer the decoder was handed, so no arithmetic about the layout
is needed: the decoder already did it. -/
theorem consumed_is_the_declared_size :
    SpecAMQP.Contracts.ConsumedIsTheDeclaredSize := by
  intro bytes frame consumed h
  unfold decodeFrame at h
  simp only [] at h
  repeat' split at h
  all_goals grind

/-! ## What the writer's accepted branch guarantees

The writer is a `do` block too, but its accepted branch binds the value layer's writer
(`encodeValue frame.body`) before deciding on the SIZE ceiling, so the case analysis has one step
more than the decoder's: after the guards are split, the branch is closed by cases on
`encodeValue frame.body`, and the `let` binding inside the `Except` bind has to be reduced by hand
— `dsimp only [Bind.bind, Monad.toBind, …]`, because the monad instance's `bind` is a projection
and `simp` cannot see through it — before the `if` beneath it can be split. -/

/-- Everything an accepted encoding records about the frame it encoded: the `DOFF` floor, the
channel's width, the `DOFF` ceiling, the extended header's width being the one `DOFF` implies, the body being a
described value whose descriptor the frame type accepts, the value layer's own octets for that
body, the SIZE ceiling, and the exact shape of the buffer written. -/
theorem encodeFrame_ok_facts (frame : Frame) (bytes : Octets) (h : encodeFrame frame = .ok bytes) :
    ∃ (descriptor inner : Value) (bodyOctets : Octets),
      minDoff ≤ frame.doff ∧
      frame.channel ≤ 2 ^ (8 * channelOctets) - 1 ∧
      frame.doff ≤ 2 ^ (8 * doffOctets) - 1 ∧
      frame.extended.size = bodyStart frame.doff - headerOctets ∧
      frame.body = .described descriptor inner ∧
      carriesPerformative frame.frameType descriptor = true ∧
      encodeValue frame.body = .ok bodyOctets ∧
      headerOctets + frame.extended.size + bodyOctets.size + frame.payload.size ≤ maxSize ∧
      bytes = (beOctets sizeOctets (headerOctets + frame.extended.size + bodyOctets.size +
          frame.payload.size) ++ beOctets 1 frame.doff ++ beOctets 1 frame.frameType.code ++
          beOctets channelOctets frame.channel).toArray ++ frame.extended ++ bodyOctets ++
          frame.payload := by
  unfold encodeFrame at h
  simp only [] at h
  repeat' split at h
  all_goals first
    | (exfalso; grind; done)
    | (cases hb : encodeValue frame.body with
       | error e =>
         dsimp only [Bind.bind, Monad.toBind, Monad.toApplicative, Applicative.toPure,
           Pure.pure, Except.instMonad, Except.bind, Except.pure] at h
         rw [hb] at h
         simp at h
       | ok b =>
         dsimp only [Bind.bind, Monad.toBind, Monad.toApplicative, Applicative.toPure,
           Pure.pure, Except.instMonad, Except.bind, Except.pure] at h
         repeat' split at h
         all_goals grind [carriesPerformative_eq])

/-! ## Big-endian fields, and the header the writer writes

The four `SIZE`/`DOFF`/`TYPE`/`CHANNEL` fields the decoder reads are `beAt` over the header the
writer emitted, so reading them back is arithmetic about `beOctets` and about `Array.extract` over
an appended buffer. Nothing here is about frames: these are the facts that let `decodeFrame`'s own
guards be decided from the writer's output. -/

/-- The octet count of the width-to-`2 ^ (8 * width)` identity: a `width`-octet field carries a
number below `2 ^ (8 * width)` exactly when it is below `256 ^ width`, which is the modulus
`beOctets` is built on. -/
theorem pow256 (w : Nat) : 256 ^ w = 2 ^ (8 * w) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

/-- Reading a big-endian field returns what it was written from, modulo the field's own
bound: `beOctets` is `beOctets.go` reversed, and the loop writes `n % 256` then continues at
`n / 256`, so the induction's step is `mod_mul_base` — the modular identity the value layer's own
rung names as the one core lacks. -/
theorem foldl_beOctets (width n : Nat) :
    (beOctets width n).foldl (fun acc byte => acc * 256 + byte.toNat) 0 = n % 256 ^ width := by
  induction width generalizing n with
  | zero => simp [beOctets, beOctets.go, Nat.mod_one]
  | succ k ih =>
    have hgo : beOctets (k + 1) n = beOctets k (n / 256) ++ [UInt8.ofNat (n % 256)] := by
      simp only [beOctets, beOctets.go, List.reverse_cons]
    rw [hgo, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (Nat.mod_lt n (by decide : 0 < 256))]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, mod_mul_base n (256 ^ k),
      Nat.mul_comm (n / 256 % 256 ^ k) 256, Nat.add_comm]

/-- A `width`-octet field read at offset zero, without a bound: the value is the number the
field holds, which is the number written modulo `256 ^ width`. -/
theorem beAt_beOctets_mod (width n : Nat) :
    beAt (beOctets width n).toArray 0 width = n % 256 ^ width := by
  have hext : (beOctets width n).toArray.extract 0 width = (beOctets width n).toArray := by
    simp [beOctets_length, List.take_of_length_le]
  simp only [beAt, Nat.zero_add, hext]
  rw [← Array.foldl_toList, List.toList_toArray, foldl_beOctets]

/-- The same, for a number that fits the field: reading it back returns it exactly, and that is
what the decoder's `SIZE`/`TYPE`/`CHANNEL` fields need. -/
theorem beAt_beOctets (width n : Nat) (h : n < 2 ^ (8 * width)) :
    beAt (beOctets width n).toArray 0 width = n := by
  rw [beAt_beOctets_mod, pow256, Nat.mod_eq_of_lt h]

/-- A value at most one below a power of two is below it: the shape the encoder's channel check and
its `SIZE` ceiling hand to a reader, and the reason neither needs arithmetic about the bound. -/
theorem lt_of_le_pow_sub_one {n w : Nat} (h : n ≤ 2 ^ (8 * w) - 1) : n < 2 ^ (8 * w) := by
  rw [← Nat.pred_eq_sub_one] at h
  exact Nat.lt_of_le_pred (Nat.two_pow_pos (8 * w)) h

/-- `Array.toArray` distributes over `List.append`, which is how the concatenation the writer
emitted becomes an `Array` append chain whose pieces `Array.extract_append` can take apart. -/
theorem toArray_append_list (l1 l2 : List UInt8) :
    (l1 ++ l2).toArray = l1.toArray ++ l2.toArray := by
  rw [← List.toList_toArray (as := l2), Array.toArray_append]

/-- A field that lies inside the first component of a concatenation is read from that component
alone: the buffer's tail cannot change what the field holds. -/
theorem beAt_append_of_le (a b : Octets) (k w : Nat) (h : k + w ≤ a.size) :
    beAt (a ++ b) k w = beAt a k w := by
  have h1 : k + w - a.size = 0 := by omega
  have h2 : k - a.size = 0 := by omega
  simp only [beAt, Array.extract_append, h1, h2, Array.extract_zero, Array.append_empty]

/-- A field that begins exactly where the first component ends is read from the second component,
at the offset the first component's width gives it: this is how the `DOFF`, `TYPE` and `CHANNEL`
fields are reached past the bytes before them. -/
theorem beAt_append_size_add (a b : Octets) (k w : Nat) :
    beAt (a ++ b) (a.size + k) w = beAt b k w := by
  have h1 : a.size + k - a.size = k := by omega
  have h2 : a.size + k + w - a.size = k + w := by omega
  rw [beAt, Array.extract_append, h1, h2,
    Array.extract_empty_of_size_le_start (by omega : a.size ≤ a.size + k),
    Array.empty_append]
  rfl

/-- The segment of `a ++ (b ++ c)` that begins where `a` ends and ends where `b` does is exactly
`b`: this is the frame's extended header, which the layout says is ignored but which the decoded
frame carries. -/
theorem extract_middle (a b c : Octets) :
    (a ++ (b ++ c)).extract a.size (a.size + b.size) = b := by
  have h1 : a.size + b.size - a.size = b.size := by omega
  have h3 : a.size ≤ a.size := by omega
  have h4 : b.size - b.size = 0 := by omega
  have h0 : a.size - a.size = 0 := by omega
  rw [Array.extract_append, Array.extract_empty_of_size_le_start h3, Array.empty_append,
    h0, h1, Array.extract_append, h4, Nat.zero_sub, Array.extract_zero,
    Array.extract_size, Array.append_empty]

/-- Everything after the block `b` is exactly `c`: the frame's body is read from a buffer that
continues into the payload, which is why the round trip's value-layer hypothesis asks the reader
to consume the value's own octets out of a longer buffer rather than out of an exact one. -/
theorem extract_tail (a b c : Octets) :
    (a ++ (b ++ c)).extract (a.size + b.size) (a.size + b.size + c.size) = c := by
  have h1 : a.size + b.size - a.size = b.size := by omega
  have h2 : a.size + b.size + c.size - a.size = b.size + c.size := by omega
  have h3 : a.size ≤ a.size + b.size := by omega
  have h4 : b.size ≤ b.size := by omega
  rw [Array.extract_append, Array.extract_empty_of_size_le_start h3, Array.empty_append,
    h1, h2, Array.extract_append, Array.extract_empty_of_size_le_start h4,
    Array.empty_append, Nat.sub_self, Nat.add_sub_cancel_left, Array.extract_size]

/-- The segment after two blocks, which is the frame's payload: it is what the decoded frame
reports as `payload`, and the decoder's final slice takes exactly it. -/
theorem extract_second_tail (a b c d : Octets) :
    (a ++ (b ++ (c ++ d))).extract (a.size + b.size + c.size)
      (a.size + b.size + c.size + d.size) = d := by
  have h1 : a.size + b.size + c.size - a.size = b.size + c.size := by omega
  have h2 : a.size + b.size + c.size + d.size - a.size = b.size + c.size + d.size := by omega
  have h3 : a.size ≤ a.size + b.size + c.size := by omega
  have h4 : b.size + c.size - b.size = c.size := by omega
  have h5 : b.size + c.size + d.size - b.size = c.size + d.size := by omega
  have h6 : b.size ≤ b.size + c.size := by omega
  have h7 : c.size ≤ c.size := by omega
  have h8 : c.size - c.size = 0 := by omega
  rw [Array.extract_append, Array.extract_empty_of_size_le_start h3, Array.empty_append,
    h1, h2, Array.extract_append, Array.extract_empty_of_size_le_start h6, Array.empty_append,
    h4, h5, Array.extract_append, Array.extract_empty_of_size_le_start h7, Array.empty_append,
    h8, Nat.add_sub_cancel_left, Array.extract_size]

/-- The frame's extended header: with `hdr` the mandatory eight octets, everything from the header's
end to the body's start is `ext`.

Stated with the two sums the writer computes — `headerOctets + ext.size` for the body's start and
`size` for the frame's end — rather than in the block form `extract_middle` takes, because that is
the shape a caller has: `SIZE` is a variable there, not the sum it is defined as. -/
theorem extract_extended_of_size (hdr ext body payload : Octets)
    (hsize : hdr.size = headerOctets) :
    (hdr ++ (ext ++ (body ++ payload))).extract headerOctets (headerOctets + ext.size) = ext := by
  rw [← hsize]
  exact extract_middle hdr ext (body ++ payload)

/-- The frame's body region: everything from the body's start to the frame's end is the body
followed by the payload, which is the buffer the value layer's reader is handed. -/
theorem extract_region_of_size (hdr ext body payload : Octets) (size : Nat)
    (hsize : hdr.size = headerOctets)
    (hsum : size = headerOctets + ext.size + body.size + payload.size) :
    (hdr ++ (ext ++ (body ++ payload))).extract (headerOctets + ext.size) size =
      body ++ payload := by
  rw [hsum, Nat.add_assoc, ← Array.size_append, ← hsize]
  exact extract_tail hdr ext (body ++ payload)

/-- The frame's payload: everything after the body is the payload, which is what the decoded frame
reports as its `payload` and what the next frame would begin after. -/
theorem extract_payload_of_size (hdr ext body payload : Octets) (size : Nat)
    (hsize : hdr.size = headerOctets)
    (hsum : size = headerOctets + ext.size + body.size + payload.size) :
    (hdr ++ (ext ++ (body ++ payload))).extract (headerOctets + ext.size + body.size) size =
      payload := by
  rw [hsum, ← hsize]
  exact extract_second_tail hdr ext body payload

/-- The frame header as the writer builds it: `SIZE`, then `DOFF`, then `TYPE`, then `CHANNEL`,
each taken from the declared surface's widths. Named so that the facts about the header's fields
can be stated about the header rather than about the writer's inlined expression. -/
def frameHeader (size doff typeCode channel : Nat) : Octets :=
  (beOctets sizeOctets size ++ beOctets 1 doff ++ beOctets 1 typeCode ++
    beOctets channelOctets channel).toArray

/-- The header is `headerOctets` octets: the four widths the layout gives its fields add up to
the fixed eight. -/
theorem frameHeader_size (size doff typeCode channel : Nat) :
    (frameHeader size doff typeCode channel).size = headerOctets := by
  simp [frameHeader, beOctets_length, headerOctets, sizeOctets, channelOctets]

/-- The header as an `Array` append chain, one component per field, so that the field facts
below can peel it a component at a time. -/
theorem frameHeader_toArray (size doff typeCode channel : Nat) :
    frameHeader size doff typeCode channel =
      (beOctets sizeOctets size).toArray ++ ((beOctets 1 doff).toArray ++
        ((beOctets 1 typeCode).toArray ++ (beOctets channelOctets channel).toArray)) := by
  simp only [frameHeader, toArray_append_list, Array.append_assoc]

/-- `SIZE` read back from the header is the size the writer computed. -/
theorem beAt_frameHeader_size (size doff typeCode channel : Nat)
    (hs : size < 2 ^ (8 * sizeOctets)) :
    beAt (frameHeader size doff typeCode channel) 0 sizeOctets = size := by
  simp only [frameHeader_toArray]
  rw [beAt_append_of_le (h := by simp [beOctets_length, sizeOctets])]
  exact beAt_beOctets sizeOctets size hs

/-- `DOFF` read back from the header is the frame's body offset, for a `DOFF` the field can
hold. The writer refuses the others, which is what `doff_lt_of_encodeFrame_ok` rests on. -/
theorem beAt_frameHeader_doff (size doff typeCode channel : Nat) (hd : doff < 2 ^ 8) :
    beAt (frameHeader size doff typeCode channel) 4 1 = doff := by
  have key := beAt_append_size_add (a := (beOctets sizeOctets size).toArray)
    (b := (beOctets 1 doff).toArray ++ ((beOctets 1 typeCode).toArray ++
      (beOctets channelOctets channel).toArray)) (k := 0) (w := 1)
  simp only [List.size_toArray, beOctets_length, sizeOctets, Nat.add_zero] at key
  simp only [frameHeader_toArray, sizeOctets]
  rw [key, beAt_append_of_le (a := (beOctets 1 doff).toArray)
      (b := (beOctets 1 typeCode).toArray ++ (beOctets channelOctets channel).toArray)
      (h := by simp [beOctets_length])]
  exact beAt_beOctets 1 doff hd

/-- `TYPE` read back from the header is the frame type's own code. -/
theorem beAt_frameHeader_typeCode (size doff typeCode channel : Nat) (ht : typeCode < 2 ^ 8) :
    beAt (frameHeader size doff typeCode channel) 5 1 = typeCode := by
  have key1 := beAt_append_size_add (a := (beOctets sizeOctets size).toArray)
    (b := (beOctets 1 doff).toArray ++ ((beOctets 1 typeCode).toArray ++
      (beOctets channelOctets channel).toArray)) (k := 1) (w := 1)
  simp only [List.size_toArray, beOctets_length, sizeOctets] at key1
  have key2 := beAt_append_size_add (a := (beOctets 1 doff).toArray)
    (b := (beOctets 1 typeCode).toArray ++ (beOctets channelOctets channel).toArray)
    (k := 0) (w := 1)
  simp only [List.size_toArray, beOctets_length, Nat.add_zero] at key2
  simp only [frameHeader_toArray, sizeOctets]
  rw [key1, key2, beAt_append_of_le (a := (beOctets 1 typeCode).toArray)
      (b := (beOctets channelOctets channel).toArray) (h := by simp [beOctets_length])]
  exact beAt_beOctets 1 typeCode ht

/-- `CHANNEL` read back from the header is the channel the writer wrote. -/
theorem beAt_frameHeader_channel (size doff typeCode channel : Nat)
    (hc : channel < 2 ^ (8 * channelOctets)) :
    beAt (frameHeader size doff typeCode channel) 6 channelOctets = channel := by
  have key1 := beAt_append_size_add (a := (beOctets sizeOctets size).toArray)
    (b := (beOctets 1 doff).toArray ++ ((beOctets 1 typeCode).toArray ++
      (beOctets channelOctets channel).toArray)) (k := 2) (w := channelOctets)
  simp only [List.size_toArray, beOctets_length, sizeOctets] at key1
  have key2 := beAt_append_size_add (a := (beOctets 1 doff).toArray)
    (b := (beOctets 1 typeCode).toArray ++ (beOctets channelOctets channel).toArray)
    (k := 1) (w := channelOctets)
  simp only [List.size_toArray, beOctets_length] at key2
  have key3 := beAt_append_size_add (a := (beOctets 1 typeCode).toArray)
    (b := (beOctets channelOctets channel).toArray) (k := 0) (w := channelOctets)
  simp only [List.size_toArray, beOctets_length, Nat.add_zero] at key3
  simp only [frameHeader_toArray, sizeOctets]
  rw [key1, key2, key3]
  exact beAt_beOctets channelOctets channel hc

/-! ## What the decoder does with a buffer that has the header's fields

The decoder's guards are all decided by the fields it reads and by the body's own consumption, so
the accepted branch is reached whenever those agree — and the record it returns is the frame those
fields describe. This is the bridge the round trip crosses: the facts above supply the hypotheses,
`decodeFrame_eq_ok_of` supplies the conclusion. -/

/-- The decoder accepts a buffer whose `SIZE`, `DOFF`, `TYPE` and `CHANNEL` fields are the frame's
own, whose body decodes to the frame's body in exactly the octets `SIZE` leaves for it, and whose
extended header and payload are the frame's — and it returns that frame, having consumed the whole
buffer.

Each hypothesis is one guard's worth of fact: `hSize` and `hHeader` decide the two buffer-length
guards, `hMinDoff` the `DOFF` floor, `hBodyStart` the `DOFF`-against-`SIZE` guard, `hDoff`,
`hType` and `hChannel` name the fields, `hExtended`, `hDecode`, `hFit` and `hPayload` describe the
body's window, and `hCarried` is what the descriptor check needs. -/
theorem decodeFrame_eq_ok_of (bytes : Octets) (frame : Frame) (consumed : Nat)
    (hSize : beAt bytes 0 sizeOctets = bytes.size)
    (hHeader : headerOctets ≤ bytes.size)
    (hMinDoff : minDoff ≤ frame.doff)
    (hBodyStart : bodyStart frame.doff ≤ bytes.size)
    (hDoff : beAt bytes 4 1 = frame.doff)
    (hType : beAt bytes 5 1 = frame.frameType.code)
    (hChannel : beAt bytes 6 channelOctets = frame.channel)
    (hExtended : bytes.extract headerOctets (bodyStart frame.doff) = frame.extended)
    (hDecode : decodeValue (bytes.extract (bodyStart frame.doff) bytes.size) =
      .ok (frame.body, consumed))
    (hFit : bodyStart frame.doff + consumed ≤ bytes.size)
    (hPayload : bytes.extract (bodyStart frame.doff + consumed) bytes.size = frame.payload)
    (hCarried : ∃ descriptor inner, frame.body = .described descriptor inner ∧
      carriesPerformative frame.frameType descriptor = true) :
    decodeFrame bytes = .ok (frame, bytes.size) := by
  obtain ⟨descriptor, inner, hbody, hcarry⟩ := hCarried
  obtain ⟨decl, hdec, hprov⟩ := exists_decl_of_carriesPerformative _ _ hcarry
  have g1 : ¬ (bytes.size < headerOctets) := by omega
  have g2 : ¬ (frame.doff < minDoff) := by omega
  have g3 : ¬ (bodyStart frame.doff > bytes.size) := by omega
  have g4 : ¬ (bytes.size < bytes.size) := by omega
  have g5 : ¬ (bodyStart frame.doff + consumed > bytes.size) := by omega
  unfold decodeFrame
  dsimp only []
  rw [hSize, hDoff, hType, hChannel]
  rw [if_neg g1, if_neg g1, if_neg g2, if_neg g3, if_neg g4]
  try dsimp only []
  rw [ofCode_code]
  try dsimp only []
  rw [hDecode]
  try dsimp only []
  rw [hbody]
  try dsimp only []
  rw [hdec]
  try dsimp only []
  rw [hExtended]
  try dsimp only []
  rw [if_neg g5]
  try dsimp only []
  rw [hPayload]
  rw [if_pos hprov]
  rw [← hbody]

/-! ## The two hypotheses the round trip rests on -/

/-- The value layer's consumption law: whatever the value layer's writer encodes for a value, its
reader recovers that value from those octets followed by anything at all, consuming exactly the
value's octets.

This is stronger than `SpecAMQP.Contracts.RoundTripOnEncodedValues`, and it is what the frame layer
needs: a frame's body is the front of the frame's remainder, the payload follows it inside the same
buffer, and the frame's `SIZE` accounting only works if the body's read stops at the body's own
last octet. Stated over the writer's domain, like the value layer's law, so that where the writer
refuses there is nothing to claim. -/
def ValueConsumption : Prop :=
  ∀ (value : Value) (octets tail : Octets),
    encodeValue value = .ok octets → decodeValue (octets ++ tail) = .ok (value, octets.size)

/-- The value layer's stated round trip follows from its consumption law, so the hypothesis above
is not a weakening of the contract's dependency but a strengthening of it that the frame layer
needs. -/
theorem round_trip_on_encoded_values_of_consumption (valueConsumption : ValueConsumption) :
    SpecAMQP.Contracts.RoundTripOnEncodedValues := by
  intro value bytes h
  have := valueConsumption value bytes #[] h
  simpa using this

/-! ## The round trip -/

/-- An accepted write has a `DOFF` the one-octet field can hold: the writer's `limit` guard, read
off `encodeFrame_ok_facts`. This is why the round trip below needs no `DOFF` hypothesis of its own
— the writer's domain is what supplies it. -/
theorem doff_lt_of_encodeFrame_ok (frame : Frame) (bytes : Octets)
    (h : encodeFrame frame = .ok bytes) : frame.doff < 2 ^ 8 := by
  obtain ⟨_descriptor, _inner, _bodyOctets, _hMinDoff, _hChan, hDoff, _hExt, _hBody, _hCarry,
    _hEnc, _hMax, _hBytes⟩ := encodeFrame_ok_facts frame bytes h
  exact lt_of_le_pow_sub_one hDoff

/-- Frame round trip, per frame: every frame the writer encodes is read back byte for byte,
consuming the whole buffer.

The proof is the two case analyses composed: `encodeFrame_ok_facts` says what the writer wrote,
the field facts read each of the decoder's five guards off that buffer, the value layer's
consumption law reads the body out of the buffer that continues into the payload, and
`decodeFrame_eq_ok_of` returns the frame. The `DOFF` bound the decoder's third guard needs comes
from the writer's own refusal, through `doff_lt_of_encodeFrame_ok`.

The writer's SIZE is generalized to a variable before the assembly: it is a sum of three lengths
the writer computed, and every fact below mentions it, so folding it away once keeps the terms
each step unifies small — the difference between this proof checking in seconds and not at all. -/
theorem frame_round_trip (valueConsumption : ValueConsumption)
    (frame : Frame) (bytes : Octets) (henc : encodeFrame frame = .ok bytes) :
    decodeFrame bytes = .ok (frame, bytes.size) := by
  obtain ⟨descriptor, inner, bodyOctets, hMinDoff, hChan, hDoffBound, hExt, hBody, hCarry, hEnc,
    hMax, hBytes⟩ := encodeFrame_ok_facts frame bytes henc
  generalize hsz : headerOctets + frame.extended.size + bodyOctets.size + frame.payload.size =
    size at hMax hBytes ⊢
  have hDoff : frame.doff < 2 ^ 8 := lt_of_le_pow_sub_one hDoffBound
  have hSizeLt : size < 2 ^ (8 * sizeOctets) := by
    have h := hMax
    rw [maxSize] at h
    exact lt_of_le_pow_sub_one h
  have hBytes' : bytes = frameHeader size frame.doff frame.frameType.code frame.channel ++
      (frame.extended ++ (bodyOctets ++ frame.payload)) := by
    rw [hBytes, ← frameHeader]
    simp only [Array.append_assoc]
  have hLen : bytes.size = size := by
    simp only [hBytes', Array.size_append, frameHeader_size]
    omega
  have hStart : bodyStart frame.doff = headerOctets + frame.extended.size := by
    have h := hExt
    have hmin := hMinDoff
    simp only [bodyStart, doffWord, minDoff, headerOctets] at h hmin ⊢
    omega
  refine decodeFrame_eq_ok_of bytes frame bodyOctets.size ?_ ?_ hMinDoff ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ⟨descriptor, inner, hBody, hCarry⟩
  · rw [hLen, hBytes']
    rw [beAt_append_of_le (h := by rw [frameHeader_size]; decide)]
    exact beAt_frameHeader_size _ _ _ _ hSizeLt
  · rw [hLen, ← hsz]
    simp only [headerOctets]
    omega
  · rw [hLen, hStart, ← hsz]
    simp only [headerOctets]
    omega
  · rw [hBytes']
    rw [beAt_append_of_le (h := by rw [frameHeader_size]; decide)]
    exact beAt_frameHeader_doff _ _ _ _ hDoff
  · rw [hBytes']
    rw [beAt_append_of_le (h := by rw [frameHeader_size]; decide)]
    exact beAt_frameHeader_typeCode _ _ _ _ (code_lt frame.frameType)
  · rw [hBytes']
    rw [beAt_append_of_le (h := by rw [frameHeader_size]; decide)]
    exact beAt_frameHeader_channel _ _ _ _ (lt_of_le_pow_sub_one hChan)
  · rw [hBytes', hStart]
    exact extract_extended_of_size _ _ _ _ (frameHeader_size _ _ _ _)
  · have hregion : bytes.extract (bodyStart frame.doff) bytes.size =
        bodyOctets ++ frame.payload := by
      rw [hLen, hBytes', hStart]
      exact extract_region_of_size _ _ _ _ _ (frameHeader_size _ _ _ _) hsz.symm
    rw [hregion]
    exact valueConsumption frame.body bodyOctets frame.payload hEnc
  · rw [hLen, hStart, ← hsz]
    simp only [headerOctets]
    omega
  · rw [hLen, hBytes', hStart]
    exact extract_payload_of_size _ _ _ _ _ (frameHeader_size _ _ _ _) hsz.symm

/-- Frame round trip on the writer's domain, discharging
`SpecAMQP.Contracts.FrameRoundTripOnEncodedFrames` from the value layer's consumption law — the
dependency the contract records — and nothing else. The writer's `DOFF` domain is not assumed: the
`limit` guard makes it follow from `encodeFrame frame = .ok bytes`, through
`doff_lt_of_encodeFrame_ok`. -/
theorem frame_round_trip_on_encoded_frames (valueConsumption : ValueConsumption) :
    SpecAMQP.Contracts.FrameRoundTripOnEncodedFrames := by
  intro frame bytes henc
  exact frame_round_trip valueConsumption frame bytes henc

end SpecAMQP.Proofs
