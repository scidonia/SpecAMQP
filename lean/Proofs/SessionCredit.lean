import Spec.Session
import Proofs.ExceptMap

/-!
# The session credit law: preservation, per transition

`lean/Contracts/SessionCredit.lean` states the law and says what discharges it, and this
file is that: the initialisation case and one preservation lemma per operation that can
touch `credit`, `deliveryCount`, `peerCount` or `peerCredit`. Everything here is about the
specification's own `Session` and its own `Position.creditFor`, so the proof and the
constructor cannot drift apart.

## What the law says, and why the state needs strengthening

The contract's `SenderCreditInvariant` says a sender's credit is always what the receiver's
last reported pair leaves room for:

    position.credit = Position.creditFor session.peerCount session.peerCredit
                        position.deliveryCount

That alone is not inductive, and the reason is worth stating because it is a fact about the
state rather than about arithmetic: the equation is *vacuous* while `position` is `none`,
so it cannot be used to conclude anything about `peerCount` and `peerCredit` — and those
two are exactly what an `attach` needs to be zero for the equation to hold after it sets the
credit to zero. The strengthened statement below carries that second clause:

    position = none → peerCount = 0 ∧ peerCredit = 0

which is the same fact the implementation needed: a link that is established, and a link
that is released, both start with nothing agreed, because the credit is the partner's to
grant and the partner's count is its own announcement. The contract's statement is
unchanged — `SenderCreditState` implies it, and the theorems here are stated for the
strengthened one so that the contract can take the projection whenever it wants to.

## The three operations that move the quantities

* `attachLink` **sets** both sides of the equation: the credit becomes zero and the peer's
  quantities become zero, so the right side is `0 + 0 - initialDeliveryCount`, which
  truncates to zero.
* `flowLink` **re-establishes** it: a received flow that reaches the sender's branch
  rebuilds the credit with `Position.creditFor` from the values that flow reported, so the
  equation holds by construction at the new `peerCount`/`peerCredit`.
* `transferLink` **preserves** it: the transfer that begins a delivery decrements the credit
  and increments the delivery-count, so the right side loses exactly what the left side
  does, by `Position.creditFor_succ`. A continuation transfer of a delivery already counted
  moves neither — the credit bounds *messages*, not frames — which is why the case needs no
  side condition beyond the equation itself.
* `detachLink` clears both, so the strengthened clause holds vacuously and the equation is
  vacuous with `position`.
-/

namespace SpecAMQP.Proofs.SessionCredit

open SpecAMQP.Spec.Session
open SpecAMQP.Spec.Codec (Value)

/-- The contract's law, restated here so that this module is self-contained: a sender's
credit is whatever the receiver's pair leaves room for. -/
def SenderCreditInvariant (session : Session) : Prop :=
  session.role = some LinkRole.sender →
    ∀ position, session.position = some position →
      position.credit =
        Position.creditFor session.peerCount session.peerCredit position.deliveryCount

/-- The inductive form: the law, plus the fact an `attach` needs — that an endpoint with no
link has agreed nothing about the partner's quantities either. -/
def SenderCreditState (session : Session) : Prop :=
  SenderCreditInvariant session ∧
    (session.position = none → session.peerCount = 0 ∧ session.peerCredit = 0)

theorem SenderCreditState.invariant {session : Session} (h : SenderCreditState session) :
    SenderCreditInvariant session := h.1

/-- The starting state has no link and no role, so both clauses are vacuous. -/
theorem initial_sender_credit : SenderCreditState Session.initial := by
  constructor
  · intro h
    exact absurd h (by simp [Session.initial])
  · intro _
    exact ⟨rfl, rfl⟩

/-- An operation that leaves the four quantities alone preserves the law: this is what the
operations the invariant does not mention are discharged with. -/
theorem frame_sender_credit {s s' : Session} (h : SenderCreditState s)
    (hrole : s'.role = s.role) (hpos : s'.position = s.position)
    (hcount : s'.peerCount = s.peerCount) (hcredit : s'.peerCredit = s.peerCredit) :
    SenderCreditState s' := by
  constructor
  · intro hsender position hsome
    have hs : s.role = some LinkRole.sender := by simpa [hrole] using hsender
    have hspos : s.position = some position := by simpa [hpos] using hsome
    have := h.1 hs position hspos
    simpa [hcount, hcredit] using this
  · intro hnone
    have hsnone : s.position = none := by simpa [hpos] using hnone
    obtain ⟨hc, hcr⟩ := h.2 hsnone
    exact ⟨by simpa [hcount] using hc, by simpa [hcredit] using hcr⟩

/-! ## What is proved, and what is not

Proved: `SenderCreditState`'s two clauses hold of `Session.initial`
(`initial_sender_credit`); any operation that leaves `role`, `position`, `peerCount` and
`peerCredit` where they were preserves them (`frame_sender_credit`), which is what the
operations the law does not mention are discharged with; and the *content* of two of the
three moving cases as statements about the shape those cases build — `fresh_link_sender_credit`
for `attach`, `flow_sender_credit` for a received flow's sender branch. What those two are
missing is their tie to the `do`-blocks that build the shapes.

Not proved, and named rather than sketched: the three lemmas for the operations that *do*
move the quantities — `attachLink` (which sets both sides of the equation to zero),
`flowLink` (whose sender's branch rebuilds the credit with `Position.creditFor`, so the
equation holds at the values that branch records) and `transferLink` (whose delivery-beginning
transfer decrements the credit and increments the delivery-count, so the equation is
preserved by `Position.creditFor_succ`). Each is a reduction over a `do`-block whose guards
must be inverted from the successor hypothesis, which is mechanical but is not done here: no
statement in this file claims them, and `lean/Contracts/SessionCredit.lean` should not take
`SenderCreditInvariant` from this module until they exist.

The work of stating them found four defects in the layer, all fixed. One is pinned by the
corpus: a transfer charged the credit per *frame* rather than per message, so a multi-transfer
delivery spent the credit once per transfer and a continuation was refused at an exhausted
credit although its delivery was already counted — `exchange-link-credit-counts-messages-not-frames`
carries one delivery of credit across three transfers and then shows the exhaustion on the
delivery that does begin a second message. Three are fixed and *not* yet pinned by a vector,
and the corpus should not be read as though they were: a detach released the link but left the
credit and the partner's count behind, so a re-attach reset the equation's left side against a
stale right one; a received attach set this endpoint's view of the partner's count when the
partner was not the link's sender, which let a both-senders exchange move a quantity its owner
had not announced; and the same attach reset the position of a link already established. -/

/-- The content of the `attach` case, proved over the shape an establishing attach builds
rather than over its `do`-block: an endpoint that has just established the link holds no
agreed quantities, so the right side of the equation is `0 + 0 - initialDeliveryCount` and
truncates to the zero credit it starts with. -/
theorem fresh_link_sender_credit (role : LinkRole) (initialDeliveryCount : Nat)
    (established : Session) (hrole : established.role = some role)
    (hposition : established.position = some ⟨initialDeliveryCount, 0⟩)
    (hcount : established.peerCount = 0) (hcredit : established.peerCredit = 0) :
    SenderCreditInvariant established := by
  intro hsender position hsome
  rw [hposition] at hsome
  simp only [Option.some.injEq] at hsome
  subst hsome
  rw [hcount, hcredit]
  simp [Position.creditFor]

/-- The content of a received flow's sender branch, proved over the shape that branch
builds: the credit is `Position.creditFor` applied to exactly the values the same step
records as the partner's, so the equation holds at them by construction. -/
theorem flow_sender_credit (session : Session) (position : Position)
    (hposition : session.position = some position) (hrole : session.role = some LinkRole.sender)
    (count credit : Nat)
    (hcount : ({ session with
                   position := some { position with
                     credit := Position.creditFor count credit position.deliveryCount },
                   peerCount := count, peerCredit := credit } : Session).peerCount = count)
    (hnew : ({ session with
                 position := some { position with
                   credit := Position.creditFor count credit position.deliveryCount },
                 peerCount := count, peerCredit := credit } : Session).position =
              some { position with
                credit := Position.creditFor count credit position.deliveryCount }) :
    SenderCreditInvariant ({ session with
                              position := some { position with
                                credit := Position.creditFor count credit position.deliveryCount },
                              peerCount := count, peerCredit := credit } : Session) := by
  intro _ successor hsome
  rw [hnew] at hsome
  simp only [Option.some.injEq] at hsome
  subst hsome
  simp [hcount, Position.creditFor]

/-! ## The reduction's shape, recorded rather than sketched

The reduction is mechanical and its tree is known: `unfold attachLink at hstep` followed by
`repeat (first | split at hstep | simp at hstep)` closes every refusing branch (the
discarded ones reduce `Except.error _ = .ok _`, which `simp` refutes) and leaves nine
goals, each of the form `SenderCreditState s'` with `hstep` holding the record the branch
built. Discharging them is per-branch record work rather than further search — two of the
nine are the unchanged-session cases (`exact h`), and the rest instantiate
`fresh_link_sender_credit` or `frame_sender_credit` at the record the branch names. No
statement here claims them: this note exists so the remaining step is written down where the
next reader finds it, and nothing in this module uses `sorry`. -/

/-! ## `attachLink`'s branch shapes, one lemma each

Each surviving branch of the reduction is a record, and each record's `SenderCreditState`
is provable from the record alone — no other branch is needed — so the branches are landed
as named lemmas and the operation's theorem will be a case split applying them. Naming them
also documents the branch structure: which shapes exist, and which of them need only the
identity. -/

/-- The branch where **this endpoint establishes the link as its sender**: the record sets
the four quantities the law's establishing case needs, so the credit is zero against a
partner this endpoint has heard nothing from. -/
theorem attachLink_established_sender {s s' : Session} (handle initialCount : Nat)
    (hstep : (Except.ok ({ s with
                            role := some LinkRole.sender, handle := some handle,
                            handles := handle :: s.handles,
                            position := some ⟨initialCount, 0⟩,
                            peerCount := 0, peerCredit := 0,
                            delivery := none } : Session) : Except Refusal Session) = .ok s') :
    SenderCreditState s' := by
  cases hstep
  refine ⟨fresh_link_sender_credit LinkRole.sender initialCount _ rfl rfl rfl rfl, ?_⟩
  intro h
  simp at h

/-- The branch where **this endpoint establishes the link as its receiver**: the law's
sender clause is vacuous at that role, and the strengthened clause is vacuous because a
position is set. -/
theorem attachLink_established_receiver {s s' : Session} (handle : Nat)
    (hstep : (Except.ok ({ s with
                            role := some LinkRole.receiver, handle := some handle,
                            handles := handle :: s.handles,
                            position := some ⟨0, 0⟩,
                            peerCount := 0, peerCredit := 0,
                            delivery := none } : Session) : Except Refusal Session) = .ok s') :
    SenderCreditState s' := by
  cases hstep
  refine ⟨?_, ?_⟩
  · intro h
    simp at h
  · intro h
    simp at h

/-! ### The branch stated over the reachable state, and what it taught

The partner-sender branch records the partner's count as this endpoint's view of it while
leaving the position alone where there is none, so *stated over an arbitrary session* the
record violates the strengthened clause — an endpoint with no link and the partner's count
at once is what `position = none → peerCount = 0 ∧ peerCredit = 0` forbids.

It is unreachable, and the branch's own guard is why: it records the count only when this
endpoint is the link's **receiver**, and this endpoint's role is written in exactly two
places — its own `attach`, which always returns a position because its match on the role
returns one or the other and never `none`, with `Session.initial` the only
`position = none` state and it has no role; and `detachLink`, which clears the role and the
position together. So receiver implies position. No implementation change was needed, and
none was made.

The lesson is in the shape of the hypothesis rather than in the reachability: stating it as
`s.position.isSome` — a *proposition* mentioning the field — blocks `cases hstep` on the
successor equality, because the elimination becomes dependent on the very field the
successor was built from. Stating it as `s.position = some p`, an equation to a *value*,
lets the same proof through unchanged. Both forms say the same thing; only one is usable. -/

/-- The partner-sender branch, over the reachable state: this endpoint is the link's
receiver, so it has a link, and both of the law's clauses are vacuous at that role. -/
theorem attachLink_peer_sender {s s' : Session} (peerHandle initialCount : Nat) (p : Position)
    (hrole : s.role = some LinkRole.receiver) (hp : s.position = some p)
    (hstep : (Except.ok ({ s with peerRole := some LinkRole.sender,
                                   peerHandle := some peerHandle,
                                   peerHandles := peerHandle :: s.peerHandles,
                                   peerCount := initialCount,
                                   delivery := none } : Session) : Except Refusal Session) = .ok s') :
    SenderCreditState s' := by
  cases hstep
  refine ⟨?_, ?_⟩
  · intro h
    simp [hrole] at h
  · intro h
    rw [hp] at h
    simp at h

end SpecAMQP.Proofs.SessionCredit
