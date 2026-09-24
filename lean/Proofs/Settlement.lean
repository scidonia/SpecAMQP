import Spec.Session
import Contracts.Settlement
import Proofs.HandleUniqueness

/-!
# The settle-mode selection is the choice the clause selects

`transfer/field:settled.4` states its condition through a cross-reference that selects a
*choice* — `<xref name="sender-settle-mode" choice="settled"/>` — of `attach`'s
`snd-settle-mode` field, and `.6` selects the other one. The element `sender-settle-mode`
names the field's declared *type*, whose choices are `unsettled`, `settled` and `mixed`, so a
model that reads the element's name where each sentence selects a choice applies each
obligation under the other's negotiation: `.4`'s "MUST be true on at least one transfer frame"
would govern the `unsettled` negotiation and never the `settled` one, which is neither
sentence.

`Contracts/Settlement.lean`'s `SenderSettleModeIsTheChoiceTheClauseSelects` states the
selection as an equality, and this module proves it — the whole of what the contract asks, at
the one operation that records the selection.

## Why the shape of the selection is part of the contract

The contract's right-hand side reads the choice's number through `Spec.Connection.choiceValue?`,
because a literal number may not appear in `Spec/` or `Contracts/` — the generated tables are
the authority on values. Turning the artifact's *text* into that number is `String.toNat?`,
which **the kernel cannot reduce**: `String.toNat? s = s.toSlice.toNat?`, and `Slice.isNat` /
`Slice.foldl` bottom out in ByteArray primitives that do not unfold, so `String.toNat? "1" =
some 1` is neither `rfl` nor `decide` — only `native_decide`, which
`tests/contracts/s1_proof_integrity.sh` bans. The selection is therefore written in the
contract's own shape, the carried field value compared against the choice's value, so that the
field the successor records *is* the contract's right-hand side and this proof argues about
the `do`-block rather than about an opaque parse. Stating a selection as an equality makes the
shape of that selection part of the contract; that is a reason to state such a selection
deliberately rather than a reason to state it differently.

## What is proved, and what it does not claim

The theorem is the contract, under the contract's own name. It does not claim `settled.6` —
that the flag is false or unset on *every* transfer of a delivery negotiated `unsettled` —
which stays the deferred obligation the ledger's dispositions name, and it says nothing about
`rcv-settle-mode`, which the session does not record.

## Failure first

The same statement, against the model as it stood before the selection was corrected — where
the flag was the comparison against the `unsettled` choice — was run and observed failing. The
first of its seven unsolved goals was the whole defect, the code's comparison on the left and
the clause's on the right:

    case h_1.isTrue.isFalse.isTrue.some.some
    ⊢ (valueNat value✝ == some (((choiceValue? "sender-settle-mode" "unsettled").bind String.toNat?).getD 0)) =
        (valueNat value✝ == (choiceValue? "sender-settle-mode" "settled").bind String.toNat?)

With the selection written in the contract's shape the left-hand side *is* the right-hand
side, and what the same script leaves is only the branch the role's own hypothesis makes
impossible: the `do`-block's `if (role == LinkRole.sender)` is cased by `split` as a `Bool`,
which produces a `(LinkRole.sender == LinkRole.sender) = false` branch beside the real one.
`sender_role_beq_self` refutes it, and every goal still open after the reduction is it.

That was the residue while the selection was the last thing `attachLink` did before it built the
record. The session layer has since added the two `attach/source` and `attach/target` guards the
attach now runs first, and they move the boundary: the chain lemmas invert the guards up to the
one that reads a terminus, so the `k` they hand the closing steps is the record's own `do`-block
rather than the record, and the branch in which both guards pass reaches those steps with its
chain un-inverted. The theorem cases each `terminus` lookup by name to reduce it, and both
residues — that branch and the impossible role one — close the way every other branch does. -/

namespace SpecAMQP.Proofs.Settlement

open SpecAMQP.Spec.Session
open SpecAMQP.Spec.Codec (Value)
open SpecAMQP.Spec.Connection (choiceValue? fieldValue valueNat)
open SpecAMQP.Proofs.HandleUniqueness (guard_last guard_chain2_tail)

/-- The scrutinee the `if (role == LinkRole.sender)` a `do`-block's branch elaborates to
reduces to once the hypothesis naming the role has been rewritten in. Its `= false` branch is
one no session can be in, and this equality is what refutes it. -/
theorem sender_role_beq_self : (LinkRole.sender == LinkRole.sender) = true := rfl

set_option maxHeartbeats 1600000 in
/-- **The flag the session records is the comparison against the `settled` choice**: the
equality `Contracts/Settlement.lean` states, in the contract's own name.

The proof is the `do`-block's case analysis. `attachLink`'s guards are `refuseUnless (c) r`,
which Lean elaborates into `if` terms inside the block's `>>=` chain — where `split` cannot
case them from — so the role lookup is rewritten by the hypothesis that names it, the guards
whose chains `Proofs/HandleUniqueness`' lemmas state are inverted by them, and each surviving
branch is the record the function builds. The `attach/source` and `attach/target` guards the
block runs before it records the selection are cased one `terminus` lookup at a time instead:
they stand between the chain those lemmas invert and the record, so the `k` such a lemma hands
over is the record's own `do`-block, a shape no lemma of the family states. Both branches
assign `senderSettleMode` from the same selection, so the two of them close on the same
definitional equality. -/
theorem senderSettleModeIsTheChoiceTheClauseSelects :
    SpecAMQP.Contracts.SenderSettleModeIsTheChoiceTheClauseSelects := by
  intro session session' outbound body hrole hattach
  unfold attachLink refuseUnless at hattach
  rw [hrole] at hattach
  simp only [] at hattach
  repeat (first | split at hattach | simp at hattach)
  all_goals (try (cases hw : (fieldValue "attach" "handle" body).bind valueNat <;> simp_all))
  all_goals (try (simp only [guard_chain2_tail] at hattach))
  all_goals (try (cases hcount : (fieldValue "attach" "initial-delivery-count" body).bind valueNat
    <;> simp_all))
  all_goals (try (simp only [guard_last] at hattach))
  -- The two `attach/source` and `attach/target` guards the block runs before it records the
  -- selection, cased on the `terminus` lookup each one reads. They stand between the chain the
  -- lemmas above invert and the record, so what they leave is a `do`-block no chain lemma states,
  -- and `cases` on the lookup is what reduces it. Each case is stated apart from the reduction
  -- that follows — `cases … <;> simp_all` fails as one tactic where the branch in which the guard
  -- passes survives its `simp_all`. The endpoint is `sender`, which is the branch `rw [hrole]`
  -- leaves the `let sentBy` lookup in.
  all_goals (try (cases hsource :
    (terminusRefusalOf Spec.Message.SendingEndpoint.sender "source" body)))
  all_goals (try (cases htarget :
    (terminusRefusalOf Spec.Message.SendingEndpoint.sender "target" body)))
  all_goals (try (rw [Except.ok.injEq] at hattach))
  all_goals (try (obtain ⟨_, hrec⟩ := hattach))
  all_goals (try (obtain ⟨_, hrec⟩ := hrec))
  all_goals (try (cases hrec))
  all_goals (try (simp_all))
  all_goals (try (simp_all [sender_role_beq_self]))
  -- What the two lookups leave is the record the block builds, so the successor equality the goals
  -- still carry is cased the way every other branch's is, and the field projection then reduces to
  -- the selection — which is the whole of the contract.
  all_goals (try (cases hrec))
  all_goals (try (simp_all))

end SpecAMQP.Proofs.Settlement
