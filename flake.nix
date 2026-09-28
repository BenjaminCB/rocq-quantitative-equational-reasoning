{
  description = "Rocq project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # Keep Codex's Rust toolchain current independently of the release tag's
    # nested lock file. Codex 0.145.0 contains dependencies requiring Rust 1.94+.
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    codex = {
      url = "github:openai/codex/rust-v0.145.0";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.rust-overlay.follows = "rust-overlay";
    };
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    rust-overlay,
    codex,
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        /*
        Use one coherent Coq/Rocq package set for the whole project.

        This is important: coqc, coq-lsp, pet, and your Coq libraries
        should all come from the same package set.
        */
        /*
        Use BenjaminCB/analysis (a fork of math-comp/analysis adding
        theories/kantorovich.v, the Kantorovich/Wasserstein-1 lifting of
        finitely-supported probability distributions) in place of upstream
        mathcomp-analysis. That fork's base commit requires
        rocq-mathcomp-algebra >= 2.6.0, so mathcomp is bumped in lockstep via
        overrideScope (not a bare .override) so every other package in the
        scope that references the mathcomp/mathcomp-analysis attrs
        (mathcomp-ssreflect, mathcomp-algebra, mathcomp-order,
        mathcomp-classical, mathcomp-reals, mathcomp-algebra-tactics,
        mathcomp-zify, coq-lsp, ...) recomputes consistently instead of
        colliding with the old 2.5.0/1.16.0 versions in the built environment.
        */
        coqPackages = pkgs.coqPackages.overrideScope (self: super: {
          mathcomp = super.mathcomp.override { version = "2.6.0"; };
          # nixpkgs' mathcomp-finmap defaultVersion only auto-selects a
          # mathcomp-2.6.0-compatible release (2.2.4) when rocq-core is in
          # 9.2-9.3; we're on 9.1.1 (which 2.2.4 also supports per its own
          # comment), so request it explicitly instead of getting "broken".
          mathcomp-finmap = super.mathcomp-finmap.override { version = "2.2.4"; };
          # Neither nixpkgs nor upstream has tagged a mathcomp-2.6.0-
          # compatible release of zify/algebra-tactics yet; zify's master
          # branch has an untagged-in-nixpkgs "1.7.0+2.4+9.0" tag whose
          # opam only requires mathcomp-ssreflect >= 2.4 (no upper bound),
          # and algebra-tactics has no such tag at all, so pin it to its
          # master HEAD (its own opam claims < 2.5, but that's untested
          # metadata staleness, not a real incompatibility, per upstream
          # practice of lagging opam bounds behind actual compatibility).
          mathcomp-zify = super.mathcomp-zify.override {
            mathcomp-boot = self.mathcomp-boot;
            mathcomp-fingroup = self.mathcomp-fingroup;
            mathcomp-algebra = self.mathcomp-algebra;
            version = {
              version = "1.7.0";
              location = {
                owner = "math-comp";
                repo = "mczify";
                rev = "387e262343f7844a8d6d896e153a2a30003fae1c";
                hash = "sha256-2dEIx/c0zLagT9jW1aDE/87ztg51HrY1wP7ioQYpUTQ=";
              };
            };
          };
          mathcomp-algebra-tactics = super.mathcomp-algebra-tactics.override {
            mathcomp-ssreflect = self.mathcomp-ssreflect;
            mathcomp-algebra = self.mathcomp-algebra;
            mathcomp-zify = self.mathcomp-zify;
            version = {
              version = "1.3.0";
              location = {
                owner = "math-comp";
                repo = "algebra-tactics";
                rev = "7da689bc90532e70ecf806110fdb4103ba0383b3";
                hash = "sha256-x7JKp2Qr7lMMVm0qKKyf2cKyvR56oFedxPoH6jCjgnQ=";
              };
            };
          };
          mathcomp-analysis = super.mathcomp-analysis.override {
            mathcomp = self.mathcomp;
            version = {
              # This "version" is a nominal label, not a real upstream
              # release: it must parse as a version newer than "1.7" (and
              # "0.6") because mathcomp-analysis/default.nix's
              # patched-derivation1/2/3 use lib.versions.isLt on it to
              # decide "did the classical/reals split exist yet" and
              # silently turn old (or unparseable, e.g. "kantorovich-fork")
              # versions' builds into no-ops. The fork is a straight fork
              # of math-comp/analysis master past 1.18.0, so any numeric
              # label above those thresholds is safe; the actual source
              # comes from `location` below regardless of this string.
              version = "1.19.0";
              location = {
                owner = "BenjaminCB";
                repo = "analysis";
                rev = "0c8068966857444a5f8cfed89f167062e7ed3f51";
                hash = "sha256-76xsR0MLLGkSTPcBLxWT7wI+yZoNnQvS09pJep0RKyU=";
              };
            };
          };
        });

        /*
        Codex 0.145.0 depends on rusty_v8 149.2.0. The v8 crate normally
        downloads its prebuilt static library during cargo build, but Nix
        builds have no network access. Fetch the platform-specific archive as
        a fixed-output derivation and expose it through RUSTY_V8_ARCHIVE.
        */
        rustyV8Archives = {
          "x86_64-linux" = {
            file = "librusty_v8_release_x86_64-unknown-linux-gnu.a.gz";
            hash = "sha256-iu2YY323533Iv7i7R1nsW95HLQv3lD9Y4OYqNQlFxVk=";
          };
          "aarch64-linux" = {
            file = "librusty_v8_release_aarch64-unknown-linux-gnu.a.gz";
            hash = "sha256-+XdRJ8pk3MSjZi0BpSGizvuluY+DOUOog9hHc7Kv88U=";
          };
          "x86_64-darwin" = {
            file = "librusty_v8_release_x86_64-apple-darwin.a.gz";
            hash = "sha256-eUlAo4o/ZrfvUqXwA8awlPdDrQQKZK+z082frUlADwc=";
          };
          "aarch64-darwin" = {
            file = "librusty_v8_release_aarch64-apple-darwin.a.gz";
            hash = "sha256-+rsuyNO6Wm3qY9uaNalg3FypheujLzQrm6Sqocc0sv4=";
          };
        };

        rustyV8ArchiveInfo = rustyV8Archives.${system};

        rustyV8Archive = pkgs.fetchurl {
          url = "https://github.com/denoland/rusty_v8/releases/download/v149.2.0/${rustyV8ArchiveInfo.file}";
          hash = rustyV8ArchiveInfo.hash;
        };

        /*
        The official Codex flake currently also contains incorrect
        fixed-output hashes for its git-pinned tokio-tungstenite and
        tungstenite dependencies. Recreate only the vendored Cargo dependency
        set with the hashes Nix reports, while retaining the official Codex
        package and build.

        Remove the cargoDeps override after OpenAI fixes those hashes upstream.
        */
        codexPackage = codex.packages.${system}.default.overrideAttrs (_old: {
          RUSTY_V8_ARCHIVE = rustyV8Archive;
          cargoDeps = pkgs.rustPlatform.importCargoLock {
            lockFile = "${codex.outPath}/codex-rs/Cargo.lock";
            outputHashes = {
              "ratatui-0.29.0" = "sha256-HBvT5c8GsiCxMffNjJGLmHnvG77A6cqEL+1ARurBXho=";
              "crossterm-0.28.1" = "sha256-6qCtfSMuXACKFb9ATID39XyFDIEMFDmbx6SSmNe+728=";
              "nucleo-0.5.0" = "sha256-Hm4SxtTSBrcWpXrtSqeO0TACbUxq3gizg1zD/6Yw/sI=";
              "nucleo-matcher-0.3.1" = "sha256-Hm4SxtTSBrcWpXrtSqeO0TACbUxq3gizg1zD/6Yw/sI=";
              "runfiles-0.1.0" = "sha256-uJpVLcQh8wWZA3GPv9D8Nt43EOirajfDJ7eq/FB+tek=";
              "tokio-tungstenite-0.28.0" = "sha256-V1xmnrfRWOcZZogelZEA4vvyMj2awCfHVA5/glQ6KAI=";
              "tungstenite-0.27.0" = "sha256-VVHhk7l9J/sEmG3q/UuV/sQ3f+fGsmq5vumSy8vbMvw=";
            };
          };
        });

        /*
        rocqEnv is the actual Coq/Rocq environment used by your project.

        It contains:
        - coqc
        - coqtop
        - coq-lsp
        - pet
        - your Coq/Rocq libraries
        */
        rocqEnv = coqPackages.rocq-core.withPackages (ps:
          with ps; [
            coq-lsp

            mathcomp
            mathcomp-ssreflect
            mathcomp-algebra
            mathcomp-order
            mathcomp-classical
            mathcomp-reals
            mathcomp-finmap
            mathcomp-analysis

            # Reflexive ring/field/lra/nra tactics for MathComp structures.
            # Provides mathcomp.algebra_tactics.ring and
            # mathcomp.algebra_tactics.lra; mathcomp-zify is its dependency
            # and is listed so the same package set supplies it.
            mathcomp-algebra-tactics
            mathcomp-zify

            # coquelicot and interval (which itself pulls in coquelicot) are
            # dropped: neither is imported anywhere in src/*.v, and
            # coquelicot 3.4.4 (nixpkgs' latest) fails to build against
            # mathcomp-boot 2.6.0 (a real upstream incompatibility, not a
            # packaging gap - no newer coquelicot release exists yet).
            flocq
            equations
            hierarchy-builder
          ]);

        coqLspExtension = pkgs.vscode-utils.buildVscodeMarketplaceExtension {
          mktplcRef = {
            name = "coq-lsp";
            publisher = "ejgallego";
            version = "0.2.4";
            hash = "sha256-s2f2i3sNZ3EdCHDgkYPPiXDp25cViAZy+DpnDxfWaSo=";
          };
        };

        wasmWasiCoreExtension =
          pkgs.vscode-utils.buildVscodeMarketplaceExtension
          {
            mktplcRef = {
              name = "wasm-wasi-core";
              publisher = "ms-vscode";
              version = "1.0.2";
              hash = "sha256-hrzPNPaG8LPNMJq/0uyOS8jfER1Q0CyFlwR42KmTz8g=";
            };
          };

        vscode = pkgs.vscode-with-extensions.override {
          vscode = pkgs.vscode;
          vscodeExtensions = [
            wasmWasiCoreExtension
            coqLspExtension
            pkgs.vscode-extensions.vscodevim.vim
          ];
        };

        settingsJson = builtins.toJSON {
          "coq-lsp.path" = "${rocqEnv}/bin/coq-lsp";
          "coq-lsp.args" = [];
          "coq-lsp.check_only_on_request" = true;
          "coq-lsp.check_on_scroll" = true;
          "coq-lsp.completion.unicode.enabled" = "off";
          "coq-lsp.eager_diagnostics" = true;
          "coq-lsp.goal_after_tactic" = false;
          "coq-lsp.show_coq_info_messages" = false;
          "coq-lsp.show_goals_on" = 3;
          "coq-lsp.trace.server" = "off";
          "files.exclude" = {
            "**/*.vo" = true;
            "**/*.vok" = true;
            "**/*.vos" = true;
            "**/*.glob" = true;
            "**/*.aux" = true;
          };
        };

        rocq-watch = pkgs.writeShellScriptBin "rocq-watch" ''
          set -eu

          if [ ! -d src ]; then
            echo "[rocq-watch] No ./src directory found; nothing to watch."
            exit 0
          fi

          echo "[rocq-watch] Watching ./src for changes..."

          exec ${pkgs.watchexec}/bin/watchexec \
            --watch src \
            --exts v \
            --restart \
            --debounce 250ms \
            -- \
            ${pkgs.bash}/bin/bash -lc '
              set -e

              echo "[rocq-watch] Regenerating CoqMakeFile"

              if command -v rocq >/dev/null 2>&1; then
                rocq makefile -f _CoqProject -o CoqMakeFile
              else
                coq_makefile -f _CoqProject -o CoqMakeFile
              fi

              echo "[rocq-watch] Building"
              make -f CoqMakeFile
            '
        '';

        /*
        MCP server wrapper.

        This makes sure rocq-mcp sees the same coqc, coq-lsp, pet,
        and Coq libraries as the rest of the dev shell.
        */
        rocqMcp = pkgs.writeShellApplication {
          name = "rocq-mcp";

          runtimeInputs = [
            pkgs.uv
            pkgs.git
            pkgs.dune_3
            rocqEnv
          ];

          text = ''
            export ROCQ_WORKSPACE="''${ROCQ_WORKSPACE:-$PWD}"
            unset PYTHONPATH

            exec uvx \
              --from git+https://github.com/LLM4Rocq/rocq-mcp \
              rocq-mcp "$@"
          '';
        };
      in {
        packages.default = pkgs.hello;

        devShells.default = pkgs.mkShell {
          packages = [
            vscode

            rocqEnv
            rocqMcp
            rocq-watch

            pkgs.uv
            pkgs.git
            pkgs.dune_3
            pkgs.ripgrep
            pkgs.jq
            pkgs.watchexec
            pkgs.nodejs_22
            pkgs.codex
            pkgs.claude-code
            pkgs.claude-monitor
            # codexPackage
          ];

          shellHook = ''
                        mkdir -p .vscode

                        cat > .vscode/settings.json <<'JSON'
            ${settingsJson}
            JSON

                        echo "Wrote .vscode/settings.json"
                        echo "Welcome to rocq dev shell"

                        echo "coqc:      $(command -v coqc || true)"
                        echo "coq-lsp:   $(command -v coq-lsp || true)"
                        echo "rocq-lsp:  $(command -v rocq-lsp || true)"
                        echo "pet:       $(command -v pet || true)"
                        echo "rocq-mcp:  $(command -v rocq-mcp || true)"
                        echo "codex:     $(command -v codex || true)"
          '';
        };
      }
    );
}
