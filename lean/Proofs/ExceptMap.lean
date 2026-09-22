/-!
# `Except` under a class projection: the reductions `simp` was missing

`Except`'s `Functor` and `Monad` instances are *derived*: the functor is `Monad.toFunctor`, so a
call site's `f <$> x` and `x >>= f` are class projections applied to `Except.map` and
`Except.bind`. Their case equations all hold by `rfl` — `Except.map g (.ok a)` is `.ok (g a)`,
`Except.map g (.error e)` is `.error e`, `Except.bind (.ok a) f` is `f a`, `Except.bind (.error e) f`
is `.error e` — and not one of them is a `@[simp]` lemma, while `simp` will not unfold a class
projection to find one. So the constructor stays stuck behind the projection: a proof that wants to
invert a refusal branch — "this computation succeeded, so its refusing half cannot have refused" —
has the fact in hand and cannot apply it.

The four lemmas below are those case equations, stated at the projections a call site actually has,
and handed to `simp`. None of them changes a definition: each is `rfl`, and each is a statement
about `Except`'s own `bind` and `map` with the instance unfolded.

## What consumes them

`except_bind_ok` and `except_bind_error` are what `Proofs/CodecRoundTripNarrowest.lean` needs to
drop the cursor's check from `takeBe_lt` and `takeBytes_advances`: `takeBe` is a `do`-block, so
inverting its refusal branch means reducing `(takeBytes width c) >>= k` at a `takeBytes` that
refused, and `takeBytes`'s own refusal is an `ite` whose branch is available only as a hypothesis.

`except_map_ok` and `except_map_error` are the same fact for the `<$>` form the reader uses to lift
a declaration into an `Option` — `some <$> declInRange …`, in the array constructor's lookup — which
is the shape `Proofs/CodecRoundTripVariable.lean` names as the obstruction between
`lengthPrefixed`'s success and its premise. They are stated here rather than beside that site
because the shape is not that family's: it is what a constructor-headed `Except` computation looks
like under any of the reader's compositions.

`except_pure_ok` completes the `do`-block: the `return` a block's last line desugars to is `pure`,
so a proof that reduces a `do`-block on its *success* branch needs the `ok` case of `>>=` and this
together, the way the two refusal sites need the `error` case alone. Without it `(… >>= fun x =>
pure (f x)) = .ok y` is as stuck as the refusal forms were.
-/
namespace SpecAMQP.Proofs

/-- `Functor.map` on a success is the success of the function: the functor instance derives from the
monad, so this is `Except.map`'s first case with the instance unfolded. -/
@[simp] theorem except_map_ok {ε α β : Type _} (f : α → β) (a : α) :
    Functor.map f (.ok a : Except ε α) = .ok (f a) := rfl

/-- `Functor.map` on a refusal is that refusal: a map reaches no constructor but the one it is
given. -/
@[simp] theorem except_map_error {ε α β : Type _} (f : α → β) (e : ε) :
    Functor.map f (.error e : Except ε α) = .error e := rfl

/-- `>>=` on a success is the continuation applied to the value: the `do`-block's `let ←` case. -/
@[simp] theorem except_bind_ok {ε α β : Type _} (a : α) (f : α → Except ε β) :
    ((.ok a : Except ε α) >>= f) = f a := rfl

/-- `>>=` on a refusal is that refusal, which is what lets a `do`-block's success refute its own
left side's refusal. -/
@[simp] theorem except_bind_error {ε α β : Type _} (e : ε) (f : α → Except ε β) :
    ((.error e : Except ε α) >>= f) = .error e := rfl

/-- `pure` at `Except` is `ok`: the third constructor-headed form a `do`-block's desugaring
produces, and the one `return` in the reader's field reads reduce to. -/
@[simp] theorem except_pure_ok {ε α : Type _} (a : α) : (pure a : Except ε α) = .ok a := rfl

end SpecAMQP.Proofs
