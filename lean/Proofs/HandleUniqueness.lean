import Spec.Session
import Proofs.ExceptMap

/-!
# Handle uniqueness: no two links share a handle

`attach/field:handle.1` is one sentence — *"The handle MUST NOT be used for other open links"* —
and `attach/field:handle.2` gives it teeth: an attach reusing a handle is answered with an
immediate close carrying the `handle-in-use` session error. The clause is about the wire, and what
makes it true of this specification is a property of the session's own state: the registry of
handles an endpoint has claimed is duplicate-free, and the handle its live link holds is one of
them.

This module proves that property as a **preserved invariant**, in the idiom
`Proofs/SessionCredit.lean` established: the initial state, a generic step for every operation
that leaves the four fields alone, and one theorem per operation that moves them. Where the credit
module's three moving cases are stated over the branch records and *not* tied to their `do`-blocks,
this one is tied: `attachLink_handle_uniqueness` is stated over `attachLink` itself and discharges
the guards the function runs, which is what makes "allocation is fresh against the live handle set"
a theorem about the operation rather than about a shape somebody transcribed.

## What the invariant is, and why the registry suffices

    HandleUniqueness session :=
      session.handles.Nodup
      ∧ session.peerHandles.Nodup
      ∧ (∀ handle, session.handle = some handle → handle ∈ session.handles)
      ∧ (∀ handle, session.peerHandle = some handle → handle ∈ session.peerHandles)

The registry is a list rather than a set because the specification's own guard is a membership
test against it — `refuseUnless (!claimed.contains handle)` — and the invariant has to be the fact
that guard needs. Two consequences of the model's shape are worth stating rather than hiding:

* **The two registries are separate.** The handles one endpoint claims and the handles its partner
  claims are different id spaces; `links/doc:link-handles.1` says so ("The two endpoints are not
  REQUIRED to use the same handle"), so the invariant constrains them separately and the theorem
  says nothing about a handle colliding *across* the two.
* **The registry is cumulative, not live.** `detachLink` clears the live handle and leaves the
  registry, so a released handle cannot be re-used by this endpoint. `handle.1` requires only that
  an *open* link not reuse a handle, so the model is stricter than the clause — deliberately, since
  it is the property `handle.2`'s mandated close is a response to, and the corpus's
  `exchange-link-handle-in-use` pins exactly that refusal.

## Why the proof needs guard lemmas

`attachLink` is a `do`-block whose guards are `refuseUnless (condition) (refusal …)`, and Lean
elaborates each into an `if` whose condition is `decide condition = true` and whose branches build
a `Unit` or a refusal. A `split` cannot case such an `if` when it sits inside the block's `>>=`
chain, which is where all four live, so the module states the chain shapes as lemmas —
`guard_last`, `guard_chain1`, `guard_chain2` and `guard_chain2_tail` — and rewrites the hypothesis
with them. The conditions are `Prop`-valued in the lemmas, so each applies to a call site's
`decide`-formed condition; nothing in them mentions this layer.
-/

namespace SpecAMQP.Proofs.HandleUniqueness

open SpecAMQP.Spec.Session
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Spec.Connection (fieldValue valueNat)

/-! ## The guard-chain lemmas

Each is the monadic fact a `do`-block of guards takes: if such a chain *succeeded*, then every
guard passed and the value it built is the one the equality reports. They are stated once here
because four operations in this layer share the shape, and their proofs are the case analysis the
`if` would have had if `split` could reach it. -/

/-- A final guarded value: the chain succeeded exactly when its guard did not fire and the value
it built is the one the equality reports. -/
theorem guard_last {ε α : Type _} (c : Prop) [Decidable c] (r : ε) (rec a : α) :
    ((if c then .error r else (Except.ok rec : Except ε α)) = .ok a) ↔ ¬c ∧ rec = a := by
  by_cases h : c <;> simp_all

/-- One `refuseUnless` guard followed by any computation. -/
theorem guard_chain1 {ε α : Type _} (c1 : Prop) [Decidable c1] (r1 : ε) (k : Except ε α)
    (a : α) :
    (((if c1 then (Except.ok () : Except ε Unit) else .error r1) >>= fun _ => k) = .ok a) ↔
      c1 ∧ k = .ok a := by
  by_cases h1 : c1 <;> simp_all

/-- Two guards followed by a value the block builds. -/
theorem guard_chain2 {ε α : Type _} (c1 c2 : Prop) [Decidable c1] [Decidable c2]
    (r1 r2 : ε) (rec a : α) :
    (((if c1 then (Except.ok () : Except ε Unit) else .error r1) >>= fun _ =>
      (if c2 then .error r2 else (Except.ok () : Except ε Unit)) >>= fun _ =>
      (Except.ok rec : Except ε α)) = .ok a) ↔ c1 ∧ ¬c2 ∧ rec = a := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp_all

/-- Two guards followed by any computation: the same facts, for the chains a later `match`
continues. -/
theorem guard_chain2_tail {ε α : Type _} (c1 c2 : Prop) [Decidable c1] [Decidable c2]
    (r1 r2 : ε) (k : Except ε α) (a : α) :
    (((if c1 then (Except.ok () : Except ε Unit) else .error r1) >>= fun _ =>
      (if c2 then .error r2 else (Except.ok () : Except ε Unit)) >>= fun _ =>
      k) = .ok a) ↔ c1 ∧ ¬c2 ∧ k = .ok a := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp_all

/-- A `>>=` that succeeded came from a success: the step a `do`-block's opaque calls —
`linkHandleOf` is one — need inverting, since no guard lemma matches them. -/
theorem bind_ok_iff {ε α β : Type _} (x : Except ε α) (f : α → Except ε β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

/-- An `if` whose *both* branches succeed: which branch it took is the only thing that decides
the value, and a `detach` and a `flow` both end in exactly that shape — one branch builds the
successor, the other returns the session untouched. -/
theorem if_ok_right {ε α : Type _} (c : Prop) [Decidable c] (a b x : α) :
    ((if c then (Except.ok a : Except ε α) else .ok b) = .ok x) ↔
      (c ∧ a = x) ∨ (¬c ∧ b = x) := by
  by_cases h : c <;> simp_all

/-! ## The invariant -/

/-- **No two links share a handle.** The handles this endpoint has claimed are all distinct, the
handles its partner has claimed are all distinct, and each endpoint's live handle is one of its
own registry's — which is what `attach/field:handle.1`'s guard reads and what the corpus's
`exchange-link-handle-in-use` observes at the wire. -/
def HandleUniqueness (session : Session) : Prop :=
  session.handles.Nodup ∧
    session.peerHandles.Nodup ∧
    (∀ handle, session.handle = some handle → handle ∈ session.handles) ∧
    (∀ handle, session.peerHandle = some handle → handle ∈ session.peerHandles)

/-- The registry and both live handles are what the invariant is about, so one operation's
evidence can be transfered to another's by four equalities. This is the `frame_…` lemma the credit
module discharges its untouched operations with. -/
theorem HandleUniqueness.of_option_le {s s' : Session} (h : HandleUniqueness s)
    (hhandles : s'.handles = s.handles) (hpeerHandles : s'.peerHandles = s.peerHandles)
    (hmine : ∀ x, s'.handle = some x → s.handle = some x)
    (hpeer : ∀ x, s'.peerHandle = some x → s.peerHandle = some x) : HandleUniqueness s' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hhandles]; exact h.1
  · rw [hpeerHandles]; exact h.2.1
  · intro x hx; rw [hhandles]; exact h.2.2.1 x (hmine x hx)
  · intro x hx; rw [hpeerHandles]; exact h.2.2.2 x (hpeer x hx)

/-- **The starting state.** A session that has not begun has claimed nothing and attached nothing,
so both registries are empty and both live handles are absent. -/
theorem initial_handle_uniqueness : HandleUniqueness Session.initial := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Session.initial]

/-- **An operation that leaves the four fields alone preserves the invariant**: the frame step for
`begin`, `end`, the flow's session-state path and every other site that does not touch a handle. -/
theorem HandleUniqueness.frame {s s' : Session} (h : HandleUniqueness s)
    (hhandles : s'.handles = s.handles) (hpeerHandles : s'.peerHandles = s.peerHandles)
    (hhandle : s'.handle = s.handle) (hpeerHandle : s'.peerHandle = s.peerHandle) :
    HandleUniqueness s' :=
  h.of_option_le hhandles hpeerHandles (by intro x hx; rwa [hhandle] at hx)
    (by intro x hx; rwa [hpeerHandle] at hx)

/-! ## `attachLink`: allocation is fresh against the live handle set

The one operation that *adds* a handle, and the reason the invariant is not vacuous. The theorem is
stated over the function, so the guard that makes it true — `refuseUnless (!claimed.contains
handle)` — is discharged rather than assumed. -/

set_option maxHeartbeats 800000 in
/-- **An attach preserves handle uniqueness.** The commit is the fresh handle appended to its
endpoint's registry; the guard is inverted, so this is `handle.1`'s rule read as a property of the
state rather than as a branch somebody wrote. -/
theorem attachLink_handle_uniqueness {s s' : Session} (outbound : Bool) (body : Value)
    (h : HandleUniqueness s) (hstep : attachLink s outbound body = .ok s') :
    HandleUniqueness s' := by
  -- The `do`-block's guards are `if decide c = true` chains, which `split` cannot case from
  -- inside the `>>=`, and its three lookups are `Option.bind` applications, which `split` cannot
  -- case either. The lookups are named first, then the guards rewritten by the chain lemmas.
  unfold attachLink refuseUnless at hstep
  repeat (first | split at hstep | simp at hstep)
  all_goals (try (cases hv : (fieldValue "attach" "role" body).bind LinkRole.ofValue))
  all_goals (try (cases hw : (fieldValue "attach" "handle" body).bind valueNat))
  all_goals (try (simp only [guard_chain2, guard_chain2_tail, guard_chain1, guard_last] at hstep))
  all_goals (try (cases hv2 : (fieldValue "attach" "role" body).bind LinkRole.ofValue
    <;> simp_all))
  all_goals (try (cases hw2 : (fieldValue "attach" "handle" body).bind valueNat <;> simp_all))
  all_goals (try (cases hcount : (fieldValue "attach" "initial-delivery-count" body).bind valueNat
    <;> simp_all))
  all_goals (try (simp only [guard_chain2, guard_chain2_tail, guard_chain1, guard_last] at hstep))
  all_goals (try (rw [Except.ok.injEq] at hstep))
  all_goals (first
    | (obtain ⟨_, _, hrec⟩ := hstep)
    | (obtain ⟨_, hrec⟩ := hstep))
  all_goals (try (obtain ⟨_, hrec⟩ := hrec))
  all_goals (try (cases hrec))
  all_goals (try (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [HandleUniqueness, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, Option.some.injEq]))
  all_goals (try (simp_all [HandleUniqueness]))

/-! ## Releasing a link, and the two operations that move a delivery

`detachLink`, `flowLink` and `transferLink` preserve the invariant, and their ties to their
`do`-blocks are **not** discharged here. They are named with the residual goal each leaves rather than dressed up as
statements over a record shape, because a shape lemma is a second copy of the function and the tie
is the part that makes the claim about the code. What each needs is stated exactly:

* **`detachLink`.** After `unfold detachLink` and the guard loop the surviving goal is

      (if (fieldValue "detach" "handle" body).bind valueNat = s.peerHandle then
         Except.ok { s with peerRole := none, peerHandle := none, peerCount := 0, peerCredit := 0,
                            delivery := none,
                            transactions := Option.map Spec.Transactions.Layer.retireAll
                                              s.transactions }
       else Except.ok s) = Except.ok s'

  — an `if` whose *both* branches succeed, which is why neither `guard_last` (whose then-branch is a
  refusal) nor the chain lemmas match it. `if_ok_right` above is that shape and was checked against
  a minimal instance of it; here `simp only [if_ok_right] at hstep` reports the lemma unused, so
  the mismatch is in how this site's condition elaborates rather than in the lemma's statement. What
  it needs is either the condition's elaborated form named (`by_cases` on
  `(fieldValue "detach" "handle" body).bind valueNat = s.peerHandle` closes one direction in
  isolation) or a `split` that reaches an `if` head inside this `do`-block; the record's four fields
  are then `rfl`/vacuous for `HandleUniqueness.of_option_le`, and `Session.afterLinkRelease` needs
  unfolding for its `transactions` update.

* **`flowLink`.** After the two `bind_ok_iff` rounds the surviving goal is the same `if` shape one
  level deeper, over the five field-rule conjuncts a handle-less flow must not carry, so it needs
  the same treatment. Its successor is a record update over `position`, `peerCount` and `peerCredit`,
  where `HandleUniqueness.frame`'s four equalities hold by `rfl`.

* **`transferLink`.** The same reduction leaves the residual goals a level further in, where the
  delivery-id and first-transfer-field lookups are: `case h_1.isTrue.isTrue.isFalse` and the `h_2`
  cases, each of the form `<a do-block of a guard and a lookup> = Except.ok s'`. Its successor is a
  record update over `position` and `delivery`, where `HandleUniqueness.frame`'s four equalities hold
  by `rfl`, so the closing is not the difficulty — reaching the guard heads is.

Nothing in this module claims `detachLink`, `flowLink` or `transferLink` until those goals are
discharged.
-/

end SpecAMQP.Proofs.HandleUniqueness
