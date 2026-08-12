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
        coqPackages = pkgs.coqPackages;

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
        rocqEnv = coqPackages.coq.withPackages (ps:
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

            coquelicot
            flocq
            interval
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

            exec uvx \
              --from git+https://github.com/LLM4Rocq/rocq-mcp \
              rocq-mcp "$@"
          '';
        };
      in {
        packages.default = pkgs.hello;

        devShells.default = pkgs.mkShell {
          packages =
            [
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
            ]
            ++ [
              codexPackage
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
