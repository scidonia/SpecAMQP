import Spec.Session
import Proofs.HandleUniqueness

/-!
# The recorded first-transfer identity does not outlive its delivery

`delivery-id.u1`, `delivery-tag.u1` and `message-format.u1` each make it an error for a
continuation transfer to differ from the first transfer of its delivery. The session implements
that by *recording* what the first transfer carried: `Session.deliveryTag` and
`Session.deliveryFormat` hold the two fields the held delivery does not, and the held delivery's
own `id` is the third. A recording that outlived its delivery would be compared against the wrong
one — the same family of defect as the three clauses themselves — so the invariant is that the
recording is absent whenever the delivery is:

    DeliveryIdentity session :=
      session.delivery = none → session.deliveryTag = none ∧ session.deliveryFormat = none

## Why the ties belong over the operations rather than over the sites

A lemma per clearing site documents the sites that exist today; it does not stop a sixth being
added, because a site lemma is a true statement about a record that nothing obliges the code to
build. What makes "cleared at every site" a *check* rather than a count is `attachLink`,
`detachLink`, `dispositionLink` and `transferLink` stated as theorems over themselves, each
inverting its own guards: then a branch added later that sets `delivery := none` without clearing
the recording breaks a build instead of waiting for the next reader to count transitions. **The
site lemmas below are records of today's sites; the ties are the half that would make them a
check, and they are not proved — see the last section, which states the residual goal verbatim
rather than dressing it up.**

## What is here

* `initial_delivery_identity` — the base case: a session that has not begun holds no delivery and
  has recorded nothing.
* `DeliveryIdentity.of_eq` — the *frame* lemma, in `Proofs/SessionCredit.lean`'s sense: an
  operation that leaves all three fields where they were preserves the invariant. It is the shape
  every operation this module does not mention is discharged with once a tie exists to discharge —
  `stepBegin`, `Session.afterEnd`, `flowLink`, the two transaction carriers and the connection
  layer all leave `delivery`, `deliveryTag` and `deliveryFormat` alone, which is a reading of
  those definitions rather than a proved statement here.
* one lemma per site that *clears* the delivery: `attachLink`'s two establish branches,
  `detachLink`'s two branches, and `dispositionLink`'s settle release; and `transferLink`'s two
  returns, where the recording is kept exactly when the successor holds a delivery and dropped
  exactly when it does not.

The guard-chain lemmas a `do`-block's `refuseUnless` sequences are inverted with — and the two
shapes a reduction reaches — are imported from `Proofs/HandleUniqueness` rather than restated:
they are the shape the session layer's operations elaborate to, and a second copy would drift the
first time one of them was corrected. The dependency runs that way round on purpose, this module
resting on the handle machinery's lemmas rather than the reverse.
-/

namespace SpecAMQP.Proofs.DeliveryIdentity

open SpecAMQP.Spec.Session
open SpecAMQP.Harness (Octets)
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Spec.Connection (fieldValue valueNat valueOctets)
open SpecAMQP.Proofs.HandleUniqueness
  (guard_last guard_chain1 guard_chain2 guard_chain2_tail bind_ok_iff if_ok_right)

/-! ## The invariant -/

/-- **The recording is about a delivery, and takes its leave with one.** `delivery-id.u1`,
`delivery-tag.u1` and `message-format.u1` compare a continuation transfer against "the first
transfer of a delivery", so a recording that outlived its delivery would be compared against the
wrong one; this is the property that says it cannot. -/
def DeliveryIdentity (session : Session) : Prop :=
  session.delivery = none → session.deliveryTag = none ∧ session.deliveryFormat = none

/-- **The starting state.** A session that has not begun holds no delivery and has recorded
nothing, so the implication's premise holds and its conclusion does too. -/
theorem initial_delivery_identity : DeliveryIdentity Session.initial := by
  simp [DeliveryIdentity, Session.initial]

/-- **The frame lemma.** An operation that leaves `delivery`, `deliveryTag` and `deliveryFormat`
where they were preserves the invariant, which is the shape the operations this module does not
mention would be discharged with. -/
theorem DeliveryIdentity.of_eq {s s' : Session} (h : DeliveryIdentity s)
    (hdelivery : s'.delivery = s.delivery) (htag : s'.deliveryTag = s.deliveryTag)
    (hformat : s'.deliveryFormat = s.deliveryFormat) : DeliveryIdentity s' := by
  intro hnone
  rw [hdelivery] at hnone
  obtain ⟨h1, h2⟩ := h hnone
  exact ⟨by rw [htag, h1], by rw [hformat, h2]⟩

/-! ## The sites that clear the delivery

One lemma per record the layer builds when a delivery ends or a link is released. Each is stated
over the record the operation actually builds, so the statement is the site rather than a
paraphrase of it — but note the section above: these document today's sites, and it is the
operation-level ties that would make a sixth site fail a build.
-/

/-- A record that clears the delivery and both recordings satisfies the identity, whatever else it
changes: the five clearing sites' common content. The delivery is named even though the
conclusion does not read it, because clearing it is what the site *is*. -/
theorem DeliveryIdentity.of_cleared {s' : Session} (_hdelivery : s'.delivery = none)
    (htag : s'.deliveryTag = none) (hformat : s'.deliveryFormat = none) :
    DeliveryIdentity s' := by
  intro _
  exact ⟨htag, hformat⟩

/-- `attachLink`'s establish branch for this endpoint: a link that is being established has
agreed nothing, so the delivery in progress and its recording both go. -/
theorem attachLink_cleared_this_end {s s' : Session} (handle : Nat) (role : LinkRole)
    (position : Option Position) (senderSettle : Bool)
    (hstep : (Except.ok ({ s with
                            handle := some handle, handles := handle :: s.handles,
                            role := some role, position, peerCount := 0, peerCredit := 0,
                            delivery := none, deliveryTag := none, deliveryFormat := none,
                            senderSettleMode :=
                              if role == LinkRole.sender then senderSettle
                              else s.senderSettleMode } : Session) : Except Refusal Session)
              = .ok s') :
    DeliveryIdentity s' := by
  cases hstep
  simp [DeliveryIdentity]

/-- `attachLink`'s establish branch for the partner: the same, on the peer's handle. -/
theorem attachLink_cleared_the_peer {s s' : Session} (handle initialCount : Nat) (role : LinkRole)
    (position : Option Position) (senderSettle : Bool)
    (hstep : (Except.ok ({ s with
                            peerRole := some role, peerHandle := some handle,
                            peerHandles := handle :: s.peerHandles, peerCount := initialCount,
                            position, senderSettleMode :=
                              if role == LinkRole.sender then senderSettle
                              else s.senderSettleMode,
                            delivery := none, deliveryTag := none,
                            deliveryFormat := none } : Session) : Except Refusal Session)
              = .ok s') :
    DeliveryIdentity s' := by
  cases hstep
  simp [DeliveryIdentity]

/-- `detachLink`'s release of this endpoint's link: a released link takes its delivery with it. -/
theorem detachLink_cleared_outbound {s s' : Session}
    (hstep : (Except.ok (Session.afterLinkRelease
      { s with handle := none, role := none, position := none,
               peerCount := 0, peerCredit := 0, delivery := none,
               deliveryTag := none, deliveryFormat := none } : Session) : Except Refusal Session)
              = .ok s') :
    DeliveryIdentity s' := by
  cases hstep
  simp [DeliveryIdentity, Session.afterLinkRelease]

/-- `detachLink`'s release of the partner's link: the same, on the peer's handle. -/
theorem detachLink_cleared_inbound {s s' : Session}
    (hstep : (Except.ok (Session.afterLinkRelease
      { s with peerHandle := none, peerRole := none,
               peerCount := 0, peerCredit := 0, delivery := none,
               deliveryTag := none, deliveryFormat := none } : Session) : Except Refusal Session)
              = .ok s') :
    DeliveryIdentity s' := by
  cases hstep
  simp [DeliveryIdentity, Session.afterLinkRelease]

/-- `dispositionLink`'s settle release: a disposition that settles the delivery this endpoint is
holding releases it, and the recording with it. -/
theorem dispositionLink_cleared {s s' : Session}
    (hstep : (Except.ok ({ s with delivery := none, deliveryTag := none,
                                   deliveryFormat := none } : Session) : Except Refusal Session)
              = .ok s') :
    DeliveryIdentity s' := by
  cases hstep
  simp [DeliveryIdentity]

/-- `transferLink`'s two returns. The recording it computes is kept exactly when the successor
holds a delivery and is `none` exactly when it does not, so both returns satisfy the identity
whichever branch of the position match built them. -/
theorem transferLink_recorded {s s' : Session} (position : Option Position)
    (delivery : Option Delivery) (carriedTag : Option Octets) (carriedFormat : Option Nat)
    (hstep : (Except.ok ({ s with
                            position, delivery,
                            deliveryTag :=
                              if delivery.isSome then
                                (if s.delivery.isSome then s.deliveryTag else carriedTag)
                              else none,
                            deliveryFormat :=
                              if delivery.isSome then
                                (if s.delivery.isSome then s.deliveryFormat else carriedFormat)
                              else none } : Session) : Except Refusal Session) = .ok s') :
    DeliveryIdentity s' := by
  cases hstep
  cases delivery <;> simp [DeliveryIdentity]

/-! ## What is not proved, and what it would take

**The operation-level ties are not here.** `attachLink_delivery_identity`,
`detachLink_delivery_identity`, `dispositionLink_delivery_identity` and
`transferLink_delivery_identity` — each `(h : DeliveryIdentity s) → op s … = .ok s' →
DeliveryIdentity s'`, stated over the operation so that its guards are inverted rather than
assumed — are what would turn the site lemmas above into a check. They are not proved, and the
rest of this section is the residual rather than an approximation of it.

**What was tried.** `Proofs/HandleUniqueness`'s own recipe, in this order, against each of the
four operations over the real definitions:

    unfold <op> refuseUnless at hstep
    repeat (first | split at hstep | simp at hstep)
    all_goals (try (rw [bind_ok_iff] at hstep))        -- for the one opaque call, in transferLink
    all_goals (try (obtain ⟨_, _, hstep⟩ := hstep))
    repeat (first | split at hstep | simp at hstep)
    all_goals (try (cases hm : (fieldValue "transfer" "delivery-id" body).bind valueNat))
    all_goals (try (cases hd : s.delivery)) (try (cases hp : s.position)) (try (cases ho : outbound))
    all_goals (try (rw [Except.ok.injEq] at hstep))
    all_goals (try (subst s')) (try assumption) (try (simp [DeliveryIdentity]))

**What happens.** The reduction *does* reach the branch records — that is where the site lemmas'
records come from, and each one it reaches is closed by `subst s'` and `simp [DeliveryIdentity]`,
which is why `attachLink_cleared_this_end` and its siblings are stated over exactly those records.
What resists is the goals it does *not* reach: a run over the four operations leaves 81 goals
across `attachLink`, `detachLink` and `dispositionLink` — 27 each — with `s'` still abstract and
`hstep` still holding an unreduced `do` chain. `transferLink`'s dump names the mechanism:

    if continued = true then do
        if (carriedTag.isNone || carriedTag == s.deliveryTag) = true then Except.ok ()
          else Except.error (refusal …)
        let y ← if (carriedFormat.isNone || carriedFormat == s.deliveryFormat) = true
                 then Except.ok () else Except.error (refusal …)
        __do_jp y
      else do
        let y ← pure PUnit.unit
        __do_jp y
    ⊢ s'.delivery = none → s'.deliveryTag = none ∧ s'.deliveryFormat = none

Those are do-notation **join points**: a nested `if … then do … else do …` elaborates to a
`let y ← …; __do_jp y`, and `split at hstep` cannot case a bind the elaborator introduced, so the
`if` beneath it is never reached and the chain stops there. That `attachLink`, `detachLink` and
`dispositionLink` stop too, with no nested `do` of their own, is the part this module does not
explain: it is a reducer limitation one level down rather than a question about the rule, and what
was observed is stated rather than the cause that was not confirmed. `transferLink` carries one
goal of a second kind as well, because its chain also contains the call whose bind is opaque:

    hstep : (do linkHandleOf s outbound "transfer" body
                 Except.ok { … delivery := none, deliveryTag := none, deliveryFormat := none … })
            = Except.ok s'
    ⊢ s'.delivery = none → s'.deliveryTag = none ∧ s'.deliveryFormat = none

which is one `bind_ok_iff` round away from the record, as the site lemma `transferLink_recorded`
states — and `transferLink`'s remaining goals are the join points above, not this one.

**What it would take.** Either a reducer for the join points — rewriting the chain statement by
statement with `Except.bind_ok_iff`-shaped lemmas (`Proofs/ExceptMap` holds two of them) instead
of asking `split` to case it — or the route `Proofs/SessionCredit.lean` took for `attachLink` and
this module's sibling took for its one tied operation: state one named-successor lemma per branch
*without* reducing to it, then prove the operation theorem as a case split applying them. Both are
proof engineering in this layer's `do`-blocks. Neither changes what the two artefacts do, and the
rule itself is pinned by `vectors/flow-negative.ndjson` independently of this module.
-/

end SpecAMQP.Proofs.DeliveryIdentity
