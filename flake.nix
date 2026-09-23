{
  description = "SpecAMQP — lock-pinned Lean environment for the AMQP 1.0 specification";

  # Lean and mathlib are pinned to exactly the revisions TemperMint pins
  # (`../TemperMint/toolchain/pins.toml`), so the specification's modules can be
  # required directly by downstream proof work with no version surgery. The
  # values are repeated literally here because Nix only sees files tracked by
  # Git, and `tests/contracts/s0_lean_environment.sh` is what keeps this record
  # and the specification's own record of the downstream pins in agreement.
  #
  # This repository needs no Rust, Charon or Aeneas: it holds the specification,
  # not an implementation.
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/b3d51a0365f6695e7dd5cdf3e180604530ed33b4";

    mathlib = {
      url = "github:leanprover-community/mathlib4/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f";
      flake = false;
    };
    batteries = {
      url = "github:leanprover-community/batteries/fa08db58b30eb033edcdab331bba000827f9f785";
      flake = false;
    };
    quote4 = {
      url = "github:leanprover-community/quote4/f46324995fca5f0483b742e4eb4daec7f4ee50d2";
      flake = false;
    };
    aesop = {
      url = "github:leanprover-community/aesop/e3cb2f741431ce31bf73549fb52316a57368b06f";
      flake = false;
    };
    proofwidgets = {
      url = "github:leanprover-community/ProofWidgets4/24b0d9dc081c5423f8eec7e866c441e5184f29d9";
      flake = false;
    };
    importGraph = {
      url = "github:leanprover-community/import-graph/5c7542ed018c78194f1e2b903eaf6a792b74c03d";
      flake = false;
    };
    leanSearchClient = {
      url = "github:leanprover-community/LeanSearchClient/c5d5b8fe6e5158def25cd28eb94e4141ad97c843";
      flake = false;
    };
    plausible = {
      url = "github:leanprover-community/plausible/63045536fe95024e6c18fc7b48e03f506701c5bc";
      flake = false;
    };
    lean4cli = {
      url = "github:leanprover/lean4-cli/92564e5770e4d09f2d86dfbf8ada1e9c715b384c";
      flake = false;
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      mathlib,
      batteries,
      quote4,
      aesop,
      proofwidgets,
      importGraph,
      leanSearchClient,
      plausible,
      lean4cli,
      ...
    }:
    let
      system = "x86_64-linux";

      pkgs = import nixpkgs { inherit system; };

      # Lean `v4.31.0`, the toolchain the pinned mathlib revision expects. The
      # release tarball is pinned by SHA-256 rather than installed through elan:
      # elan resolves `lean-toolchain` by downloading from the network, which an
      # offline acceptance run may not do.
      leanDistribution = pkgs.stdenv.mkDerivation {
        pname = "lean4";
        version = "4.31.0";

        src = pkgs.fetchurl {
          url = "https://github.com/leanprover/lean4/releases/download/v4.31.0/lean-4.31.0-linux.tar.zst";
          hash = "sha256-B6YzzI2RUcvAiCXqTN2lDUsCosnLhSwBMbEwRvScrX8=";
        };

        nativeBuildInputs = [
          pkgs.autoPatchelfHook
          pkgs.zstd.bin
        ];
        buildInputs = [ pkgs.stdenv.cc.cc.lib ];

        sourceRoot = "lean-4.31.0-linux";
        dontConfigure = true;
        dontBuild = true;

        installPhase = ''
          runHook preInstall
          mkdir -p $out
          cp -r . $out/
          runHook postInstall
        '';
      };

      # The pinned mathlib closure, materialised so that Lake resolves it
      # without network access.
      #
      # Lake refuses a git dependency that is not a Git repository, so each
      # materialised source gets a local repository whose commit ids are
      # deterministic (fixed author, committer and dates); the upstream
      # revision and content hash of every source stay in `flake.lock`. The
      # manifest Lake reads is mathlib's own committed
      # `lake-manifest.json`, retargeted at these copies: mathlib's requires
      # then resolve locally instead of being fetched.
      #
      # The specification's mathlib imports are compiled here so that the store
      # path carries their `.olean` files. Every later build is offline and
      # starts from compiled dependencies rather than recompiling a mathlib
      # cone. `--no-cache` keeps the build from consulting a remote cache.
      leanWorkspace = pkgs.stdenv.mkDerivation {
        pname = "specamqp-lean-workspace";
        version = "1";

        nativeBuildInputs = [
          leanDistribution
          pkgs.git
          pkgs.python3
        ];

        dontUnpack = true;
        # The workspace carries prebuilt `.olean` artifacts; leave them alone.
        dontStrip = true;
        dontFixup = true;

        buildPhase = ''
          runHook preBuild
          export HOME="$TMPDIR"
          mkdir -p workspace/.lake/packages

          materialise_dependency() {
            local name="$1" source="$2" target="workspace/.lake/packages/$1"
            cp -r "$source" "$target"
            chmod -R u+w "$target"
            git -C "$target" init -q -b main
            git -C "$target" add -A
            GIT_AUTHOR_DATE="2000-01-01T00:00:00+0000" \
            GIT_COMMITTER_DATE="2000-01-01T00:00:00+0000" \
              git -C "$target" \
                -c user.name="SpecAMQP pin" \
                -c user.email="pins@specamqp.invalid" \
                commit -q -m "SpecAMQP: pinned dependency source"
          }

          materialise_dependency mathlib ${mathlib}
          materialise_dependency batteries ${batteries}
          materialise_dependency Qq ${quote4}
          materialise_dependency aesop ${aesop}
          materialise_dependency proofwidgets ${proofwidgets}
          materialise_dependency importGraph ${importGraph}
          materialise_dependency LeanSearchClient ${leanSearchClient}
          materialise_dependency plausible ${plausible}
          materialise_dependency Cli ${lean4cli}

          # The specification's own package: mathlib is a path dependency, and
          # every transitive dependency is materialised above.
          cat > workspace/lakefile.lean <<'LAKEFILE'
          import Lake
          open Lake DSL

          require mathlib from "./.lake/packages/mathlib"

          package specamqp

          @[default_target] lean_lib Prewarm
          LAKEFILE

          mkdir -p workspace/Prewarm
          cat > workspace/Prewarm.lean <<'PREWARM'
          /-
          The specification's mathlib surface, compiled into this store path so
          that offline builds start from compiled dependencies. Keep this list to
          what `lean/Spec` actually imports: the point is a small, reviewable
          prewarm, not a mathlib build.
          -/
          import Mathlib.Algebra.BigOperators.Group.List.Basic
          import Mathlib.Algebra.Order.BigOperators.Group.List
          import Mathlib.Data.List.Basic
          PREWARM

          cp ${mathlib}/lake-manifest.json workspace/lake-manifest.json
          chmod -R u+w workspace
          python3 - <<'PY'
          import json, subprocess

          path = "workspace/lake-manifest.json"
          with open(path) as handle:
              manifest = json.load(handle)

          manifest["name"] = "specamqp"
          for entry in manifest["packages"]:
              entry["inherited"] = True
              repo = "workspace/.lake/packages/%s" % entry["name"]
              entry["rev"] = subprocess.check_output(
                  ["git", "-C", repo, "rev-parse", "HEAD"], text=True
              ).strip()
          manifest["packages"].append({
              "type": "path",
              "scope": "",
              "name": "mathlib",
              "manifestFile": "lake-manifest.json",
              "inherited": False,
              "dir": "./.lake/packages/mathlib",
              "configFile": "lakefile.lean",
          })
          with open(path, "w") as handle:
              json.dump(manifest, handle, indent=1)
          PY

          ( cd workspace && lake build --no-cache Prewarm )

          runHook postBuild
        '';

        installPhase = ''
          runHook preInstall
          mkdir -p $out
          cp -r workspace/. $out/
          runHook postInstall
        '';
      };

      # Lake reads the `HEAD` of every materialised dependency through `git`.
      # The prewarmed workspace lives in the read-only store, so git's ownership
      # check reports it as a dubious repository and Lake would try to re-fetch
      # it. Mark exactly those trees as trusted instead of weakening the check
      # globally.
      leanWorkspaceGitSafeDirectory =
        let
          repositories = map (name: "${leanWorkspace}/.lake/packages/${name}") [
            "mathlib"
            "batteries"
            "Qq"
            "aesop"
            "proofwidgets"
            "importGraph"
            "LeanSearchClient"
            "plausible"
            "Cli"
          ];
          entries = pkgs.lib.imap0
            (index: path: [
              {
                name = "GIT_CONFIG_KEY_${toString index}";
                value = "safe.directory";
              }
              {
                name = "GIT_CONFIG_VALUE_${toString index}";
                value = path;
              }
            ])
            repositories;
        in
        pkgs.lib.listToAttrs (pkgs.lib.concatLists entries)
        // {
          GIT_CONFIG_COUNT = toString (builtins.length repositories);
        };

      specShell = pkgs.mkShell {
        name = "spec";

        packages = [
          leanDistribution
          leanWorkspace
          pkgs.git
          pkgs.python3
        ];

        env = leanWorkspaceGitSafeDirectory // {
          SPECAMQP_LEAN_TOOLCHAIN = "leanprover/lean4:v4.31.0";
          SPECAMQP_MATHLIB_REVISION = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f";

          # The prewarmed workspace the shell provisions from: a store path, so
          # nothing is fetched.
          SPECAMQP_LEAN_WORKSPACE = "${leanWorkspace}";
        };

        shellHook = ''
          # The host may have an unrelated elan/lean on PATH; the pinned
          # toolchain must win, otherwise `lake` would resolve `lean-toolchain`
          # through elan and try to download a toolchain during an offline run.
          export PATH="${leanDistribution}/bin''${PATH:+:$PATH}"

          # Lean elaborates with every core it can find, which on a working
          # desktop starves interactive audio and editors for minutes at a time.
          # `lake` and `lean` are therefore wrapped to run under `nice -n 19` by
          # default. The wrapper execs the pinned binary by absolute path, so the
          # tool, its version, arguments, output and exit status are the pinned
          # ones and only the scheduling priority differs; elaboration then
          # consumes genuinely idle CPU and yields to anything interactive.
          #
          # Targets are written from `${leanDistribution}/bin`, never from a
          # `command -v` lookup. A lookup can return an exported shell function's
          # name, or some other host tool of the same name, and a wrapper built
          # from that re-enters itself instead of reaching the pinned binary.
          # Installation is all-or-nothing for the same kind of reason: a shell
          # that announces low-priority Lean and then runs it at normal priority
          # is reporting success for something it did not do.
          #
          # Applied to every command this shell runs, interactive or not. The
          # classification is per repository and rests on that repository's
          # evidence contract: nothing here compares a recorded environment.
          # `s0_lean_environment.sh` reads `lean --version` and the planner-owned
          # manifest rather than executable-path identity, and the wrapper execs
          # the same pinned store binary unchanged, so what a contract observes is
          # unchanged by construction. SPECAMQP_LEAN_NICE=0 is the only opt-out:
          # set it before entering the shell for a diagnostic or evidence shell
          # that must see an unmodified PATH.
          if [ "''${SPECAMQP_LEAN_NICE:-1}" != "0" ]; then
            spec_nice_dir="''${TMPDIR:-/tmp}/specamqp-lean-nice"
            spec_nice_failure=""
            mkdir -p "$spec_nice_dir" || spec_nice_failure="mkdir -p $spec_nice_dir"
            if [ -z "$spec_nice_failure" ]; then
              for spec_tool in lake lean; do
                printf '#!/bin/sh\nexec nice -n 19 %s "$@"\n' "${leanDistribution}/bin/$spec_tool" \
                  >"$spec_nice_dir/$spec_tool" &&
                  chmod +x "$spec_nice_dir/$spec_tool" ||
                  { spec_nice_failure="installing the $spec_tool wrapper in $spec_nice_dir"; break; }
              done
            fi
            if [ -z "$spec_nice_failure" ]; then
              export PATH="$spec_nice_dir:$PATH"
              # The pinned toolchain must win, which the PATH entry above only
              # achieves against executables: in bash a function beats a PATH
              # entry, so an inherited `lake` function would shadow the shim and
              # silently run an unniced, possibly unrelated tool. These
              # definitions close that hole. `export -n` matters: redefining an
              # imported exported function would otherwise inherit its export
              # attribute and hand the function to every child shell, so
              # clearing it is what keeps child processes resolving through the
              # shim.
              lake() { command "${pkgs.coreutils}/bin/nice" -n 19 "${leanDistribution}/bin/lake" "$@"; }
              lean() { command "${pkgs.coreutils}/bin/nice" -n 19 "${leanDistribution}/bin/lean" "$@"; }
              export -nf lake lean
            else
              printf 'spec: the low-priority Lean shim could not be installed: %s\n' "$spec_nice_failure" >&2
              printf 'spec: Lean would run at normal priority, which this shell does not do\n' >&2
              printf 'spec: set SPECAMQP_LEAN_NICE=0 if an unshimmed shell is what you want\n' >&2
              # Louder than the provisioning policy below, which warns in an
              # interactive shell: an unshimmed Lean is not the state this shell
              # promises, and the escape hatch exists to make that deliberate.
              exit 1
            fi
          fi

          # The Lean project resolves its pinned mathlib closure from its
          # gitignored `lean/.lake`, and `lean/lake-manifest.json` records
          # exactly that layout. Lake rewrites artifacts there when it considers
          # a dependency module stale, which the read-only store cannot allow, so
          # those paths are backed by a writable copy of the prewarmed workspace
          # under the gitignored `lean/.lake/workspace`. The copy is reused while
          # its marker names the current workspace, and otherwise refreshed by
          # staging and renaming it into place, so a partial copy is never
          # accepted and iterating on the specification never re-copies from
          # scratch. A path that already exists as a real directory is left
          # alone.
          #
          # Every step below reports its own failure and hands it back to the
          # caller: a half-provisioned `.lake` must never look like success,
          # because the acceptance commands would then run against a partial
          # dependency copy. The hook decides whether that failure is fatal; the
          # marker stays absent after any failure, so the next entry retries.
          provision_step_failed() {
            printf 'spec: provisioning the writable Lean workspace failed: %s\n' "$1" >&2
            printf 'spec: the Lean project would resolve against an incomplete %s/.lake\n' "$PWD/lean" >&2
          }

          provision_lean_project() {
            local project="$PWD/lean" cache marker entry link target
            [ -n "''${SPECAMQP_LEAN_WORKSPACE:-}" ] || return 0
            [ -d "$project" ] || return 0
            cache="$project/.lake/workspace"
            marker="$cache/.specamqp-source"
            # `.lake` has to exist before the staging directory inside it is
            # created, otherwise the copy fails and every later step fails with
            # it.
            mkdir -p "$project/.lake" ||
              { provision_step_failed "mkdir -p $project/.lake"; return 1; }
            if [ "$(cat "$marker" 2>/dev/null)" != "$SPECAMQP_LEAN_WORKSPACE" ]; then
              staging="$project/.lake/.workspace.staging"
              rm -rf "$staging" ||
                { provision_step_failed "rm -rf $staging"; return 1; }
              cp -a "$SPECAMQP_LEAN_WORKSPACE" "$staging" ||
                { provision_step_failed "cp -a $SPECAMQP_LEAN_WORKSPACE $staging"; return 1; }
              chmod -R u+w "$staging" ||
                { provision_step_failed "chmod -R u+w $staging"; return 1; }
              printf '%s\n' "$SPECAMQP_LEAN_WORKSPACE" >"$staging/.specamqp-source" ||
                { provision_step_failed "writing $staging/.specamqp-source"; return 1; }
              rm -rf "$cache" ||
                { provision_step_failed "rm -rf $cache"; return 1; }
              mv "$staging" "$cache" ||
                { provision_step_failed "mv $staging $cache"; return 1; }
            fi
            for entry in packages; do
              case "$entry" in
                packages) target="$cache/.lake/packages" ;;
                *) target="$cache/$entry" ;;
              esac
              link="$project/.lake/$entry"
              if [ -L "$link" ] || [ ! -e "$link" ]; then
                ln -sfn "$target" "$link" ||
                  { provision_step_failed "ln -sfn $target $link"; return 1; }
              fi
            done
          }

          # Automation (including `nix develop --command`) must fail loudly
          # rather than run with an unusable Lean project, so a failed
          # provisioning exits the shell. An interactive shell is only warned:
          # tearing down the user's session would be worse than the diagnostic
          # above, and the next entry retries once the cause is fixed.
          if ! provision_lean_project; then
            case "$-" in
              *i*) printf 'spec: this interactive shell keeps running with an unusable Lean project\n' >&2 ;;
              *) printf 'spec: refusing to run commands against a half-provisioned Lean project\n' >&2
                 exit 1 ;;
            esac
          fi
        '';
      };
    in
    {
      devShells.${system}.spec = specShell;

      packages.${system} = {
        inherit leanDistribution leanWorkspace;
        default = specShell;
      };
    };
}
