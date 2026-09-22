import Lake
open Lake DSL

/-
The SpecAMQP Lean project.

`Generated/` holds the declared surface derived from the pinned OASIS artifacts by
`scripts/gen-oasis-lean.py` and is never edited by hand. `Spec/` will hold the
handwritten semantics, `Contracts/` the acceptance declarations, and `Proofs/` the
proofs; each library is registered here when its first module lands, because an
empty `lean_lib` would be scaffolding rather than content.

mathlib is required from `./.lake/packages/mathlib`: a path dependency into the
gitignored, writable copy of the pinned closure that the `spec` development shell
provisions from its prewarmed store path. `lake-manifest.json` records exactly that
resolution, so the project builds offline with no network access.
-/

require mathlib from "./.lake/packages/mathlib"

package specamqp

@[default_target]
lean_lib Generated

@[default_target]
lean_lib Spec

@[default_target]
lean_lib Contracts
