/-
# The byte-stream front end (R2, `PLAN.md` §23.1)

The transport's view of the core. `Impl.Core.step` is the frozen interface's machine, and its `Input.frame`
is *one buffer offered to the connection layer* — a protocol header, or one frame — because that is the
reading `Conforms` (`PLAN.md` §10) can be discharged against. A socket is not that: it delivers an ordered
byte stream, in reads of whatever size the kernel and the peer happen to produce, with a frame's octets
split across reads and several frames arriving in one. This module is where that difference is absorbed,
and it is the whole of the core's own protocol-facing decision.

## The two halves of the difference, and which one the core owns

* **Which octets the layer is handed.** The layer is handed **the octets that have arrived** — the
  accumulated buffer — and not a slice of it. That is not a convenience: `Spec.Frame.readFrame` is
  *written* to be handed a buffer that may hold a following frame ("Read one frame from the front of a
  buffer, reporting the octets it consumed as the SIZE it declares, so a buffer may hold a following
  frame"), and its body region runs to the end of the buffer on purpose so that a performative which
  overruns its own `SIZE` is a `sizeMismatch` rather than a `truncated`. Slicing first would replace the
  layer's reading of the octets with our idea of what it should see, and every refusal whose class turns
  on how many octets were in the buffer would become ours to justify.
* **How far to advance.** This is the core's decision, and it is unavoidable: `Spec.Connection.step`'s
  `.arriving` arm reads a frame with `readFrame`, which *does* report the octets it consumed, but the
  layer passes that count to `stepAmqpFrame` as a size and the `Outcome` it returns does not carry it.
  The loop therefore cannot learn how far to advance from the layer, and **asks the layout instead**:
  `Spec.Frame.frameExtent`, in the module that owns the layout, where the arithmetic is stated once
  (`declaredSize`, `declaredDoff`, `declarationConsistent`) and `declarationConsistent_eq_true_iff` and
  `readFrame_ok_declarationConsistent` tie it to the reader's own checks. Nothing here re-spells it; the
  one comparison this module adds is the waiting rule, which is a question about the buffer.

`nextUnitLength`'s rules: the first column is the connection layer's question, the last is the
specification's arithmetic, and the only thing this module decides is whether the buffer yet holds what
the arithmetic asks for.

| when | the unit | why |
|---|---|---|
| a header is due (`State.receiveClass`) | `headerOctets` (8), or wait | a protocol header *is* eight octets, and `decodeHeader` reads nothing beyond them |
| a frame is due and fewer than 8 octets have arrived | wait | nothing can be named from less than a frame header, and the layer's answer there (`truncated`) is a statement about the buffer's length rather than a decision about a frame |
| a frame is due and the buffer begins with the header magic | `headerOctets` | the layer refuses this shape *before* reading any frame — "a protocol header is not a frame of this layer" — so a frame window must not be computed from octets that are not a frame |
| `SIZE` below the header, `DOFF` below its minimum, or the body start past `SIZE` | `Spec.Frame.frameExtent` = `headerOctets` | the declaration contradicts itself, and all three contradictions are decided by the header alone (`declarationConsistent`) — so its declared extent cannot be trusted and the octets that carried the declaration are what the unit is |
| otherwise | `Spec.Frame.frameExtent` = `SIZE`, or wait until `SIZE` octets have arrived | this is the frame's extent as the layout states it ("SIZE ... MUST contain the total frame size of the frame header, extended header, and frame body"), and on exactly those octets the layer reads the frame or names a defect inside it |

`nextUnitLength_ge_header` below is what makes the middle rows safe and the loop terminate: a unit is
never shorter than a header, so the loop never advances by zero and never re-decides octets it has
already decided about. In the frame branch that law is `Spec.Frame.headerOctets_le_frameExtent` — the
specification's fact, not this module's.

## What this module proves, and what it leaves

The laws here are about the *front end*: that a unit is at least the header and at most the buffer (so
the loop consumes octets and invents none), that the loop stops with nothing complete left, that its
remainder is a suffix of what arrived (nothing dropped from the middle, nothing duplicated), that the
framer's decision does not depend on octets that have not arrived, and that the loop's per-unit inputs are
exactly `Impl.Core.step`'s inputs (`run_some`). Two things are deliberately **not** claimed here:

* **That the sequence of per-unit answers is a sequence the specification admits.** That is not this
  module's to say: the per-unit answer *is* `Impl.Core.step`'s answer by construction, and that it
  conforms is R3's instance; the composition of the loop's iteration with that instance is R3's corollary.
* **That feeding a stream in one read equals feeding it in two.** It is true exactly when the layer's
  answer to a buffer is its answer to the unit at that buffer's front — a property of
  `Spec.Connection.step` and of `Spec.Frame.readFrame`'s reader (does a decoder that accepts a frame
  accept the same frame when more octets follow it?), *not* a property of this loop. The framer's own half
  is proved here (`nextUnitLength_prefix`), and the layer's half is reported as an obligation with its
  exact statement rather than assumed: nothing in the tree proves the reader's suffix-independence today,
  and assuming it here would be assuming the conclusion for that half of the claim.
-/

import Impl.Core

namespace SpecAMQP.Impl.Stream

open SpecAMQP.Contracts (Output)
open SpecAMQP.Harness (Octets)
open SpecAMQP.Impl.Core (State Conn arriving toOctets)

/-- The layer's own `State`, named to keep the two state types apart at a use site. -/
abbrev LayerState := SpecAMQP.Spec.Connection.State

/-- The frame layout's header width, as this module's arithmetic uses it. -/
def headerOctets : Nat := SpecAMQP.Spec.Frame.headerOctets

/-- The protocol header magic's width: the prefix a buffer that is headed by a protocol header begins
with. -/
def magicOctets : Nat := 4

/-! ## Reading the layout's own fields -/

/-- The octets of a field are the same octets in a longer buffer: a prefix read of a buffer is a read of
the same octets. This is what makes every rule below independent of how much else is in the buffer. -/
theorem extract_prefix (inbox extra : Octets) (start width : Nat)
    (h : start + width ≤ inbox.size) :
    (inbox ++ extra).extract start (start + width) = inbox.extract start (start + width) := by
  rw [Array.extract_append]
  have hstart : start - inbox.size = 0 :=
    Nat.sub_eq_zero_of_le (Nat.le_trans (Nat.le_add_right start width) h)
  have hstop : start + width - inbox.size = 0 := Nat.sub_eq_zero_of_le h
  rw [hstart, hstop]
  simp

/-- A big-endian field read at an offset the buffer already covers does not change when more octets
follow it. Both `SIZE` and `DOFF` are read through this. -/
theorem beAt_append (inbox extra : Octets) (start width : Nat)
    (h : start + width ≤ inbox.size) :
    SpecAMQP.Spec.Frame.beAt (inbox ++ extra) start width =
      SpecAMQP.Spec.Frame.beAt inbox start width := by
  unfold SpecAMQP.Spec.Frame.beAt
  rw [extract_prefix inbox extra start width h]

/-- A buffer that begins with the magic still begins with it when more octets follow: the discriminator
the connection layer refuses a frame-shaped buffer by is a property of the first four octets. -/
theorem headerShaped_append (inbox extra : Octets) (h : magicOctets ≤ inbox.size) :
    SpecAMQP.Spec.Connection.headerShaped (inbox ++ extra) =
      SpecAMQP.Spec.Connection.headerShaped inbox := by
  have hm : 4 ≤ inbox.size := by simpa [magicOctets] using h
  have hge : 4 ≤ Array.size inbox + Array.size extra := by omega
  have hprefix : (inbox ++ extra).extract 0 4 = inbox.extract 0 4 :=
    extract_prefix inbox extra 0 4 (by omega)
  unfold SpecAMQP.Spec.Connection.headerShaped
  rw [Array.size_append, hprefix]
  simp [hm, hge]

/-! ## The unit: the layer's questions, and the specification's arithmetic

A unit is the buffer the connection layer is handed next. Two things decide it, and they belong to
different owners:

* **whether a header or a frame is due** — `State.receiveClass`, the layer's own read of picture 24's
  "Legal Receives" column — and whether a buffer that is *not* a frame has arrived where a frame belongs,
  which is the layer's own discriminator again (`Spec.Connection.headerShaped`, tested before it reads any
  frame). Both are asked here, not re-decided.
* **how far a frame extends** — the layout's arithmetic, which is `Spec.Frame.frameExtent`: the declared
  `SIZE` where the declaration is self-consistent and the header where it is not. Nothing here re-spells
  it. The one comparison this module adds is the *waiting* rule — does the buffer hold that many octets
  yet — which is a question about the buffer rather than about the frame, and is therefore the caller's.
-/

/--
**The extent of the next wire unit**, or `none` where the buffer does not yet hold one.

`none` is "wait for more octets" and never "nothing is here": every caller in this module treats it as
"the buffer is incomplete", which is why the loop below stops rather than discarding.
-/
def nextUnitLength (state : LayerState) (inbox : Octets) : Option Nat :=
  if state.receiveClass = .header then
    if inbox.size < headerOctets then none else some headerOctets
  else if inbox.size < headerOctets then none
  else if SpecAMQP.Spec.Connection.headerShaped inbox then some headerOctets
  else
    let extent := SpecAMQP.Spec.Frame.frameExtent inbox
    if inbox.size < extent then none else some extent

/-- **A frame's extent does not move when the octets after the header do.** `Spec.Frame.frameExtent` reads
the declaration's two fields and nothing else, and both live inside the header, so a buffer that has a
header has the frame's extent whatever follows it. This is the framer's half of stream safety; the layer's
half — that its *answer* is prefix-determined too — is unproved in this tree and is named in R2's report. -/
theorem frameExtent_append {inbox extra : Octets} (h : headerOctets ≤ inbox.size) :
    SpecAMQP.Spec.Frame.frameExtent (inbox ++ extra) = SpecAMQP.Spec.Frame.frameExtent inbox := by
  have hsize4 : (0 + SpecAMQP.Spec.Frame.sizeOctets) ≤ inbox.size := by
    simp only [SpecAMQP.Spec.Frame.sizeOctets, headerOctets, SpecAMQP.Spec.Frame.headerOctets] at h ⊢
    omega
  have hdoff5 : (4 + SpecAMQP.Spec.Frame.doffOctets) ≤ inbox.size := by
    simp only [SpecAMQP.Spec.Frame.doffOctets, headerOctets, SpecAMQP.Spec.Frame.headerOctets] at h ⊢
    omega
  have h0 := beAt_append inbox extra 0 SpecAMQP.Spec.Frame.sizeOctets hsize4
  have h4 := beAt_append inbox extra 4 SpecAMQP.Spec.Frame.doffOctets hdoff5
  simp only [SpecAMQP.Spec.Frame.frameExtent, SpecAMQP.Spec.Frame.declarationConsistent,
    SpecAMQP.Spec.Frame.declaredSize, SpecAMQP.Spec.Frame.declaredDoff, h0, h4]
  rfl

-- The bounds below are what the loop's termination and its conservation law rest on. Both branches are
-- proved for their own shape, and the frame branch's lower bound is the specification's own law.

/-- The header branch's extent: eight octets of a buffer that has eight, and nothing otherwise. -/
theorem headerBranch_ge {inbox : Octets} {n : Nat}
    (h : (if inbox.size < headerOctets then (none : Option Nat) else some headerOctets) = some n) :
    headerOctets ≤ n := by
  split at h <;> simp_all

/-- The header branch's extent is within the buffer, on the same terms. -/
theorem headerBranch_le {inbox : Octets} {n : Nat}
    (h : (if inbox.size < headerOctets then (none : Option Nat) else some headerOctets) = some n) :
    n ≤ inbox.size := by
  split at h <;> simp_all

/-- **A unit is at least a frame header.** The law the loop's termination rests on — an advance is never
zero, so the buffer it recurses on is genuinely smaller — and the law that makes the loop well-founded in
the other sense too: octets already decided about are never re-decided. In the frame branch it is
`Spec.Frame.headerOctets_le_frameExtent`, so a frame's extent being non-empty is the specification's fact
rather than this module's. -/
theorem nextUnitLength_ge_header {state : LayerState} {inbox : Octets} {n : Nat}
    (h : nextUnitLength state inbox = some n) : headerOctets ≤ n := by
  unfold nextUnitLength at h
  by_cases hh : state.receiveClass = .header
  · rw [if_pos hh] at h
    exact headerBranch_ge h
  · rw [if_neg hh] at h
    by_cases h8 : inbox.size < headerOctets
    · rw [if_pos h8] at h; simp at h
    · rw [if_neg h8] at h
      by_cases hs : SpecAMQP.Spec.Connection.headerShaped inbox
      · rw [if_pos hs] at h
        simp only [Option.some.injEq] at h
        omega
      · rw [if_neg hs] at h
        by_cases hw : inbox.size < SpecAMQP.Spec.Frame.frameExtent inbox
        · rw [if_pos hw] at h; simp at h
        · rw [if_neg hw] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact SpecAMQP.Spec.Frame.headerOctets_le_frameExtent inbox

/-- **A unit is at most the buffer.** A unit is never invented beyond the octets that have arrived: the
advance is a slice of what is in the buffer, never more. -/
theorem nextUnitLength_le_size {state : LayerState} {inbox : Octets} {n : Nat}
    (h : nextUnitLength state inbox = some n) : n ≤ inbox.size := by
  unfold nextUnitLength at h
  by_cases hh : state.receiveClass = .header
  · rw [if_pos hh] at h
    exact headerBranch_le h
  · rw [if_neg hh] at h
    by_cases h8 : inbox.size < headerOctets
    · rw [if_pos h8] at h; simp at h
    · rw [if_neg h8] at h
      by_cases hs : SpecAMQP.Spec.Connection.headerShaped inbox
      · rw [if_pos hs] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        exact Nat.le_of_not_lt h8
      · rw [if_neg hs] at h
        by_cases hw : inbox.size < SpecAMQP.Spec.Frame.frameExtent inbox
        · rw [if_pos hw] at h; simp at h
        · rw [if_neg hw] at h
          simp only [Option.some.injEq] at h
          rw [← h]
          exact Nat.le_of_not_lt hw

/--
**The framer's own half of stream safety**: a unit that is complete in a prefix of a buffer is complete
in the longer buffer, with the same extent. Reading the octets that arrived must not depend on octets that
have not arrived yet, and this is that property for the decision this module owns — the layer's
header-or-frame question and the specification's extent. The layer's half of the same property (that its
*answer* is prefix-determined) is named in R2's report as an obligation with its exact statement.
-/
theorem nextUnitLength_prefix {state : LayerState} {inbox : Octets} {n : Nat}
    (h : nextUnitLength state inbox = some n) :
    ∀ extra : Octets, nextUnitLength state (inbox ++ extra) = some n := by
  intro extra
  unfold nextUnitLength at h ⊢
  by_cases hh : state.receiveClass = .header
  · rw [if_pos hh] at h ⊢
    split at h
    · simp at h
    · have : ¬ (inbox ++ extra).size < headerOctets := by rw [Array.size_append]; omega
      rw [if_neg this]
      exact h
  · rw [if_neg hh] at h ⊢
    by_cases h8 : inbox.size < headerOctets
    · rw [if_pos h8] at h; simp at h
    · rw [if_neg h8] at h
      have hge : headerOctets ≤ inbox.size := Nat.le_of_not_lt h8
      have hbig : ¬ (inbox ++ extra).size < headerOctets := by rw [Array.size_append]; omega
      rw [if_neg hbig]
      have hshape := headerShaped_append inbox extra (by
        simp only [magicOctets, headerOctets, SpecAMQP.Spec.Frame.headerOctets] at hge ⊢
        omega)
      by_cases hs : SpecAMQP.Spec.Connection.headerShaped inbox
      · rw [if_pos hs] at h
        rw [if_pos (by rw [hshape]; exact hs)]
        exact h
      · rw [if_neg hs] at h
        rw [if_neg (by rw [hshape]; exact hs)]
        have hext := frameExtent_append (inbox := inbox) (extra := extra) hge
        by_cases hw : inbox.size < SpecAMQP.Spec.Frame.frameExtent inbox
        · rw [if_pos hw] at h; simp at h
        · rw [if_neg hw] at h
          simp only [hext]
          rw [if_neg (by rw [Array.size_append]; omega)]
          exact h

/-! ## The loop -/

-- The equation name the `match` below introduces is used by `decreasing_by`, which the linter does not
-- see; the option is scoped to this definition rather than to the module.
set_option linter.unusedVariables false in
/--
**The loop**: hand the layer what has arrived, advance by the unit the framer names, repeat while the
buffer holds one, and stop with the remainder.

The connection layer's state is threaded, and so are the octets — the buffer handed to the layer is the
whole remainder and not a slice of it, which is the reading `Spec.Frame.readFrame` documents — and the
outputs are appended in the order the steps produced them.

Termination is by measure: each advance is at least a header (`nextUnitLength_ge_header`) and at most the
buffer (`nextUnitLength_le_size`), so the buffer strictly shrinks. There is no `partial` here — the
integrity gate forbids one — and those two bounds are what discharge the obligation.
-/
def run (conn : Conn) (inbox : Octets) : Conn × Octets × List Output :=
  match h : nextUnitLength conn.state inbox with
  | none => (conn, inbox, [])
  | some n =>
    let answer := arriving conn inbox
    let (conn', inbox', outs') := run answer.1 (inbox.extract n inbox.size)
    (conn', inbox', answer.2 ++ outs')
termination_by inbox.size
decreasing_by
  have hge : headerOctets ≤ n := nextUnitLength_ge_header h
  have hle : n ≤ inbox.size := nextUnitLength_le_size h
  simp only [headerOctets, SpecAMQP.Spec.Frame.headerOctets] at hge
  rw [Array.size_extract, Nat.min_self]
  omega

/-- Running the loop on a buffer that holds no complete unit answers nothing and changes nothing: a
partial read is kept, not decided about. -/
theorem run_none {conn : Conn} {inbox : Octets} (h : nextUnitLength conn.state inbox = none) :
    run conn inbox = (conn, inbox, []) := by
  rw [run.eq_1]
  split
  · rfl
  · rename_i m hm
    rw [h] at hm
    simp at hm

/-- Running the loop on a buffer that holds a unit: the layer answers the octets that arrived, the loop
advances by the framer's unit, and the rest is the loop's answer to the remainder.

This is the fold identity in the form a proof uses it, and it is also the composition R3 needs: the
per-unit answer here **is** `Impl.Core.step`'s answer to `Input.frame` of those octets and the state it
leaves, so a sequence of these iterations is a sequence of steps of the instance. -/
theorem run_some {conn : Conn} {inbox : Octets} {n : Nat}
    (h : nextUnitLength conn.state inbox = some n) :
    run conn inbox =
      let answer := arriving conn inbox
      let (conn', inbox', outs') := run answer.1 (inbox.extract n inbox.size)
      (conn', inbox', answer.2 ++ outs') := by
  conv_lhs => rw [run.eq_def]
  split
  · rename_i hnone
    rw [h] at hnone
    simp at hnone
  · rename_i m hm
    rw [h] at hm
    simp only [Option.some.injEq] at hm
    rw [← hm]

/-- **The loop stops with nothing complete left**: whatever the buffer holds when the loop returns, the
framer finds no unit in it. Nothing that could have been stepped is left unstepped. -/
theorem run_rest_stops : ∀ (conn : Conn) (inbox : Octets),
    nextUnitLength (run conn inbox).1.state (run conn inbox).2.1 = none := by
  intro conn inbox
  induction conn, inbox using run.induct with
  | case1 conn inbox h => rw [run_none h]; exact h
  | case2 conn inbox n h _ conn' inbox' outs' hcall ih =>
    have hrec : run (arriving conn inbox).1 (inbox.extract n inbox.size) =
        (conn', inbox', outs') := hcall
    rw [hrec] at ih
    rw [run_some h]
    simp only [hrec]
    exact ih

/-- **The remainder is a suffix**: the octets the loop leaves are the tail of the octets that arrived —
nothing dropped from the middle, nothing duplicated, nothing invented. The loop advances by whole units
and its rest is exactly what it did not decide about. -/
theorem run_rest_suffix : ∀ (conn : Conn) (inbox : Octets),
    ∃ k, (run conn inbox).2.1 = inbox.extract k inbox.size := by
  intro conn inbox
  induction conn, inbox using run.induct with
  | case1 conn inbox h =>
    refine ⟨0, ?_⟩
    rw [run_none h]
    rw [Array.extract_size]
  | case2 conn inbox n h _ conn' inbox' outs' hcall ih =>
    have hrec : run (arriving conn inbox).1 (inbox.extract n inbox.size) =
        (conn', inbox', outs') := hcall
    obtain ⟨k, hk⟩ := ih
    rw [hrec] at hk
    have hk' : inbox' = (inbox.extract n inbox.size).extract k
        (inbox.extract n inbox.size).size := hk
    have hle : n ≤ inbox.size := nextUnitLength_le_size h
    have hidx : min (n + (inbox.extract n inbox.size).size) inbox.size = inbox.size := by
      rw [Array.size_extract, Nat.min_self]
      omega
    refine ⟨n + k, ?_⟩
    rw [run_some h]
    simp only [hrec]
    rw [hk', Array.extract_extract, hidx]

/-- **The remainder of the loop holds no unit, and is a suffix of what arrived.** -/
theorem run_rest (conn : Conn) (inbox : Octets) :
    nextUnitLength (run conn inbox).1.state (run conn inbox).2.1 = none ∧
      ∃ k, (run conn inbox).2.1 = inbox.extract k inbox.size :=
  ⟨run_rest_stops conn inbox, run_rest_suffix conn inbox⟩

/-! ## The shell's two calls -/

/--
**Drain**: the same loop, over the endpoint's own state. Named separately from `run` because the shell's
entry point is `feed`, and because the inbox the loop threads back is what a partial read leaves behind.
-/
def drain (state : State) : State × List Output :=
  let (conn, inbox, outs) := run state.conn state.inbox
  ({ conn := conn, inbox := inbox }, outs)

/--
**Feed the endpoint the octets a read returned**, and take back what it answers.

This is the whole of the shell's read path: append what arrived to what was pending, hand the layer
everything that has arrived, advance by each complete unit the framer names, and keep the tail. A read
that completed no unit answers nothing and keeps its octets, which is what a partial read *is*, and a read
that completed several units answers each of them in order, which is what pipelining is.

The outputs are the interface's own — the octets the layer wrote, and the answer the corpus reads (the
state's name, or a refusal's condition and class) — in the order the steps produced them.
-/
def feed (state : State) (bytes : ByteArray) : State × List Output :=
  drain { conn := state.conn, inbox := state.inbox ++ toOctets bytes }

/-- Feeding nothing drains what is already pending: the loop's own answer, not a special case here. (A
zero-length read does not happen through `Impl.Transport` — it *is* the peer's orderly close, for which
see `closed` — and a caller that passes an empty buffer gets the pending buffer's answer.) -/
theorem feed_empty (state : State) : feed state ByteArray.empty = drain state := by
  unfold feed
  simp [toOctets]

/-- Feeding is draining what has arrived: the append is the whole of the difference. -/
theorem feed_eq (state : State) (bytes : ByteArray) :
    feed state bytes = drain { conn := state.conn, inbox := state.inbox ++ toOctets bytes } := rfl

/-- What the loop leaves, a partial read keeps: feeding octets that complete no unit answers nothing and
keeps every octet. -/
theorem feed_none {state : State} {bytes : ByteArray}
    (h : nextUnitLength state.conn.state (state.inbox ++ toOctets bytes) = none) :
    feed state bytes = ({ state with inbox := state.inbox ++ toOctets bytes }, []) := by
  unfold feed drain
  rw [run_none h]

/-- And a read that completes units answers each of them and keeps the tail: the shell's read path is the
loop, with nothing added. -/
theorem feed_some {state : State} {bytes : ByteArray} {n : Nat}
    (h : nextUnitLength state.conn.state (state.inbox ++ toOctets bytes) = some n) :
    feed state bytes =
      let buffer := state.inbox ++ toOctets bytes
      let answer := arriving state.conn buffer
      let (state', outs') := drain { conn := answer.1, inbox := buffer.extract n buffer.size }
      (state', answer.2 ++ outs') := by
  unfold feed drain
  rw [run_some h]

/-- **What a read leaves behind holds no complete unit.** The shell can call `feed` again with whatever
the next read returns and the two will compose: no octets are decided about twice. -/
theorem feed_rest_stops (state : State) (bytes : ByteArray) :
    nextUnitLength (feed state bytes).1.conn.state (feed state bytes).1.inbox = none := by
  unfold feed drain
  exact run_rest_stops _ _

/-- **And it is a tail of everything that has arrived**, with the same reading as the loop's: the shell's
buffer is a suffix of what it has been fed, so nothing is dropped from the middle and nothing is
duplicated. -/
theorem feed_rest_suffix (state : State) (bytes : ByteArray) :
    ∃ k, (feed state bytes).1.inbox = (state.inbox ++ toOctets bytes).extract k
      (state.inbox ++ toOctets bytes).size := by
  unfold feed drain
  exact run_rest_suffix _ _

/-! ## An orderly close -/

/--
**An orderly close.** The peer has closed the byte stream: drop the pending octets, which can never be
completed, and leave the protocol state exactly where it is.

The protocol state is *deliberately* untouched. The artifact names TCP Close as a connection action the
state table mandates — the third column's "TCP Close for Write" on CLOSE_PIPE and CLOSE_SENT, "TCP Close"
on END — and nowhere as an event a peer receives, so what an endpoint's *protocol* state becomes when the
stream ends is not a question the standard answers. That is why this is a function of its own rather than
an `Input`: §10's alphabet has `frame`, `api` and `tick`, and a fourth constructor would make us the author
of the answer. (A `tick` is an environment event too — but its *semantics* are the specification's: what a
timer is and what is due at it is the layer's business, while the meaning of the stream ending would be
ours.) The consequence — closing the descriptor, reporting the transport end — belongs to the shell, and
this function is outside every conformance claim rather than dressed as handled.
-/
def closed (state : State) : State :=
  { state with inbox := #[] }

/-- Dropping what cannot be completed is all an orderly close does to the core's state. -/
theorem closed_eq (state : State) : closed state = { state with inbox := #[] } := rfl

/-- An orderly close does not move the connection layer: the endpoint the interface compares is the same
before and after, which is why this function cannot be an `Input`: a step that changed nothing observable
would be a step the specification has no answer for. -/
theorem closed_conn (state : State) : (closed state).conn = state.conn := rfl

/-- An orderly close leaves nothing pending. -/
theorem closed_inbox (state : State) : (closed state).inbox = #[] := rfl

end SpecAMQP.Impl.Stream
