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

/-
Each library names the submodules it holds.

Lake's default is a `Glob.one` of the library's own name — `roots` defaults to
`#[name]` and `globs` to `roots.map Glob.one` — which here would select *root
modules* called `Generated`, `Spec`, `Contracts`, `Harness` and `Ref`. No file of
any of those names exists: the content lives beside them, one directory down. A
`Glob.one` yields its name without checking that a source file is there, so each
library's module set would hold that phantom module, fetching its imports would
fail, and the library's `modules` facet would report "some modules have bad
imports" at job computation. Only targets that name a library were affected —
`lake build <some-module>` and `lake build amqp-ref` never touch the module set —
which is why every acceptance command, all of them targeted, was green.

`roots` keeps its default, which is what makes the modules beneath each name
local to its library; only the globs change, from the name alone to the
submodules under it.

`Glob.submodules` is the right glob *because* these libraries have no root module.
`Glob.andSubmodules` would select the bare name too, unconditionally, and that is
precisely the phantom-module case above; so if a root module is ever added — a
`Ref.lean` that imports the rest, say — the glob must be widened to
`Glob.andSubmodules` in that same change, or the new module would be silently
outside its library.
-/

@[default_target]
lean_lib Generated where
  globs := #[.submodules `Generated]

@[default_target]
lean_lib Spec where
  globs := #[.submodules `Spec]

@[default_target]
lean_lib Contracts where
  globs := #[.submodules `Contracts]

@[default_target]
lean_lib Harness where
  globs := #[.submodules `Harness]

@[default_target]
lean_lib Ref where
  globs := #[.submodules `Ref]

/-- The reference implementation as a native executable: `lake exe amqp-ref
<vector-file.ndjson>`. -/
lean_exe «amqp-ref» where
  root := `Ref.Main
  supportInterpreter := true

/-- The specification as an executable over the same corpus: `lake exe amqp-spec
<vector-file.ndjson>`. Both artefacts run through `Harness.Runner`, so their
verdicts are directly comparable. -/
lean_exe «amqp-spec» where
  root := `Spec.Main
  supportInterpreter := true
