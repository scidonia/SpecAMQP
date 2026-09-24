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
this one is tied: `attachLink_handle_uniqueness`, `detachLink_handle_uniqueness`,
`flowLink_handle_uniqueness` and `transferLink_handle_uniqueness` are each stated over their own
operation and discharge the guards it runs, which is what makes "allocation is fresh against the
live handle set" — and its preservation by the three operations that share the state — a theorem
about the code rather than about a shape somebody transcribed.

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

## Why `attachLink`'s proof uses guard lemmas

`attachLink` is a `do`-block whose guards are `refuseUnless (condition) (refusal …)`, and Lean
elaborates each into an `if` whose condition is `decide condition = true` and whose branches build
a `Unit` or a refusal. Such an `if` sits inside the block's `>>=` chain, where the `let`-bindings
the elaborator introduces as join points stand between `split` and it, so this proof states the
chain shapes as lemmas — `guard_last`, `guard_chain1`, `guard_chain2` and `guard_chain2_tail` —
and rewrites the hypothesis with them. The conditions are `Prop`-valued in the lemmas, so each
applies to a call site's `decide`-formed condition; nothing in them mentions this layer. The three
ties at the end of this module take the other route over the same obstacle — `dsimp only` reduces
those bindings and `split` then cases the `if` — and the section there records what that turned on.
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

`detachLink`, `flowLink` and `transferLink` preserve the invariant, and each is tied here to its
own `do`-block: the successor hypothesis is inverted, so the guards the function runs are
discharged rather than assumed, and each tie is a theorem about the operation rather than about a
record shape somebody transcribed from it.

## The join points, and the one step that exposes them

The elaborator rewrites a `do`-block's early `return` and its `let x ← e` bindings into *join
points* — a `let`-bound lambda that the step's value is applied to — and an `if` beneath one is
invisible to `split`: `findSplit?` refuses an `ite` whose condition has loose bound variables, and
a condition written in terms of a join point's binding is exactly that. Every reduction below
therefore begins with `dsimp only at hstep`, which zeta-reduces those bindings and hands `split` an
`if` it will case. This is the reducer limitation `Proofs/DeliveryIdentity` records; it is real,
and it is one `dsimp` away from being out of the way.

It also corrects what this module first recorded about `if_ok_right` at `detachLink`'s site. The
*condition* is not the obstacle — `dsimp only` leaves a plain `ite` on `(!releasable) = true`, and
`split at hstep` cases it on the first try. The lemma is stated for branches that are `Except.ok a`
and `Except.ok b`, and neither branch at that site is one: the then-branch is `pure s`, the
else-branch is the join point's application, and a detach's two directions are a second `if`
inside it. `split` asks the *condition*, and is therefore not blocked by what the branches are
built from.

## What each tie needed

* **`detachLink`** — `unfold`, `dsimp only`, two `split` rounds (the release condition, then the
  direction the detach travels) and `cases` on the successor equality. It closes with
  `HandleUniqueness.of_option_le`, which was already here: a detach releases the handle of its own
  direction only, leaving both registries and the other direction's handle alone, and a detach
  naming a handle this endpoint has not attached returns the session itself. No `by_cases`, no new
  helper, no rearrangement of the block.
* **`flowLink`** — `unfold flowLink linkHandleOf refuseUnless`, `dsimp only`, then
  `repeat' (first | split at hstep | simp only [pure_bind] at hstep)`: the five field-rule
  conjuncts a handle-less flow must not carry, `linkHandleOf`'s match on the handle field, the
  delivery-count guard and the two credit lookups. Then `cases` and `HandleUniqueness.frame`, whose
  four equalities are `rfl` because no branch of a flow writes a handle or a registry — the most a
  flow sets is `position`, `peerCount` and `peerCredit`. No `by_cases`, no new helper, no
  rearrangement.
* **`transferLink`** — the same reduction over a longer block, with `cases hstep` in the loop as
  well: a branch a guard refuses reduces to `Except.error … = .ok s'`, which `cases` discharges the
  moment it is reached, and carrying those branches to the end of the reduction is what makes this
  one the expensive case. Then `cases` and `HandleUniqueness.frame` again, over `position`,
  `delivery`, `deliveryTag` and `deliveryFormat`. No `by_cases`, no new helper, no rearrangement.

No `by_cases` on a named condition, and no helper lemma, was needed by any of the three: with the
join points reduced the conditionals are reached by `split`, and each successor's four facts are
`rfl` for a record update over fields its operation never writes. Nothing here changed how the
invariant is stated — the same four conjuncts, both registries duplicate-free with each live handle
present in its own registry. -/

/-- **A detach preserves handle uniqueness.** The successor is either the session itself — a detach
naming a handle this endpoint has not attached is admitted, "other than a detach" — or the record a
release builds, which clears the live handle of the direction the detach travelled and leaves both
registries and the other direction's handle where they were. `of_option_le` is the shape that
needs: each of its two implications is vacuous in the cleared direction and the identity in the
other. -/
theorem detachLink_handle_uniqueness {s s' : Session} (outbound : Bool) (body : Value)
    (h : HandleUniqueness s) (hstep : detachLink s outbound body = .ok s') :
    HandleUniqueness s' := by
  unfold detachLink at hstep
  dsimp only at hstep
  split at hstep <;> try split at hstep
  all_goals (cases hstep)
  all_goals (first
    | exact h
    | (apply h.of_option_le
       · rfl
       · rfl
       · intro x hx
         first | exact hx | cases hx
       · intro x hx
         first | exact hx | cases hx))

set_option maxHeartbeats 800000 in
/-- **A flow preserves handle uniqueness.** The successor is the session itself, or a record update
over `position`, `peerCount` and `peerCredit`; no branch of the exchange writes a handle or a
registry, so the frame lemma's four equalities are `rfl` and the invariant is carried across the
step unchanged. -/
theorem flowLink_handle_uniqueness {s s' : Session} (outbound : Bool) (body : Value)
    (h : HandleUniqueness s) (hstep : flowLink s outbound body = .ok s') :
    HandleUniqueness s' := by
  unfold flowLink linkHandleOf refuseUnless at hstep
  dsimp only at hstep
  repeat' (first | split at hstep | simp only [pure_bind] at hstep)
  all_goals (try cases hstep)
  all_goals (first | exact h | exact HandleUniqueness.frame h rfl rfl rfl rfl)

set_option maxHeartbeats 1600000 in
/-- **A transfer preserves handle uniqueness.** The successor is a record update over `position`,
`delivery`, `deliveryTag` and `deliveryFormat`; like a flow, no branch of the exchange writes a
handle or a registry, so the frame lemma's four equalities are `rfl`. This is the reduction that
needs `cases` inside the loop rather than after it: the guards a transfer refuses on are what makes
its `do`-block the largest of the four, and a refused branch closes against the successor equality
as soon as `split` reaches it. -/
theorem transferLink_handle_uniqueness {s s' : Session} (outbound : Bool) (body : Value)
    (h : HandleUniqueness s) (hstep : transferLink s outbound body = .ok s') :
    HandleUniqueness s' := by
  unfold transferLink linkHandleOf refuseUnless at hstep
  dsimp only at hstep
  simp only [pure_bind] at hstep
  repeat' (first
    | cases hstep
    | split at hstep
    | simp only [pure_bind] at hstep
    | simp only [Except.ok.injEq] at hstep)
  all_goals (try exact h)
  all_goals (try exact HandleUniqueness.frame h rfl rfl rfl rfl)

end SpecAMQP.Proofs.HandleUniqueness
