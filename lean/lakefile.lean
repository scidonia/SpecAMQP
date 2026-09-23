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

@[default_target]
lean_lib Proofs where
  globs := #[.submodules `Proofs]

/--
## The transport shell (R1, `PLAN.md` §23.1)

`Impl` holds the shipped endpoint's Lean side. Today that is one module,
`Transport.lean`, which declares the six `@[extern]` operations that are the whole
of this implementation's unproved trust; the pure protocol core joins it at R2.
`tests/contracts/s1_proof_integrity.sh` pins the boundary to that one path and
reports the count, so the size of the trust is a number in a gate's output rather
than a claim in prose.
-/
@[default_target]
lean_lib Impl where
  globs := #[.submodules `Impl]

/--
The shim those declarations call, compiled by the shell's C compiler.

A custom `target` rather than `extern_lib`, which Lake's README deprecates in favour
of exactly this pair: the object file is a target, and the executables that need the
symbols name it in `moreLinkObjs`. The include path is a *weak* argument because it
is system-dependent — changing it must not invalidate a correct object file — while
the flags that decide the object's contents are traced, so a flag change rebuilds it.

The compiler is `cc`, the pinned shell's `gcc` wrapper, and *not* the Lean
toolchain's own C compiler, which `buildLeanO` would use. That clang is invoked with
a store-path sysroot and `-nostdinc`; measured, it cannot find even `stddef.h`, let
alone `arpa/inet.h`, because the Lean build ships no libc headers. A shim that talks
to the kernel needs POSIX headers, so it is compiled by the shell's compiler against
Lean's headers, which is what `-I $(lean --print-prefix)/include` gives it.
-/
target «transport-shim» pkg : System.FilePath := do
  let srcJob ← inputTextFile <| (pkg.dir.parent.getD pkg.dir) / "scripts" / "transport_shim.c"
  buildO (pkg.buildDir / "c" / "transport_shim.o") srcJob
    #["-I", (← getLeanIncludeDir).toString]
    #["-O2", "-fPIC", "-std=c11", "-Wall", "-Wextra"]

/--
R1's loopback evidence: a server that echoes one connection and a client that
compares what it receives octet for octet. They live outside `lean/Impl/` so that
"nothing but `Transport.lean` inside the shipped tree is unproved" is a
directory-level fact rather than a reading of two files, and outside the package
directory because they are R1's harness rather than the shipped endpoint.

Their sources are under `scripts/loopback/Loopback/` — the module tree sits one
level down so that `srcDir` can point the library at it and the module names stay
`Loopback.*` rather than claiming top-level names.
-/
@[default_target]
lean_lib Loopback where
  srcDir := "../scripts/loopback"
  globs := #[.submodules `Loopback]

/-- `lake exe amqp-loopback-server <port> <chunk-octets>` — R1's server: accepts one
connection, echoes the announced payload, reports its call counts, exits. -/
lean_exe «amqp-loopback-server» where
  srcDir := "../scripts/loopback"
  root := `Loopback.ServerMain
  moreLinkObjs := #[«transport-shim»]

/-- `lake exe amqp-loopback-client <port> <octets> <chunk-octets>` — R1's client:
sends a known byte string, compares what comes back octet for octet, exits non-zero
on a mismatch. -/
lean_exe «amqp-loopback-client» where
  srcDir := "../scripts/loopback"
  root := `Loopback.ClientMain
  moreLinkObjs := #[«transport-shim»]

/--
R1's shim controls: the same shim file, compiled with wrappers that plant a fault on
demand (`scripts/loopback/mutants/shim_controls.c`, selected by `SPECAMQP_SHIM_CONTROL`).

Separate object file and separate executables, so neither binary under test contains a
line of control code and no control can be switched on in a run that means to be clean.
A harness that has never been made to fail proves nothing; this is what makes it fail
on request, reproducibly, for anyone reviewing the evidence.
-/
target «transport-shim-controls» pkg : System.FilePath := do
  let scriptDir := pkg.dir.parent.getD pkg.dir / "scripts"
  let srcJob ← inputTextFile <| scriptDir / "loopback" / "mutants" / "shim_controls.c"
  buildO (pkg.buildDir / "c" / "transport_shim_controls.o") srcJob
    #["-I", (← getLeanIncludeDir).toString]
    #["-O2", "-fPIC", "-std=c11", "-Wall", "-Wextra"]

/-- `lake exe amqp-loopback-control-server …` — the server linked against the controls
instead of the shim. -/
lean_exe «amqp-loopback-control-server» where
  srcDir := "../scripts/loopback"
  root := `Loopback.ControlServerMain
  moreLinkObjs := #[«transport-shim-controls»]

/-- `lake exe amqp-loopback-control-client …` — the client linked against the controls. -/
lean_exe «amqp-loopback-control-client» where
  srcDir := "../scripts/loopback"
  root := `Loopback.ControlClientMain
  moreLinkObjs := #[«transport-shim-controls»]

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
