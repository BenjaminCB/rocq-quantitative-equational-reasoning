{
  description = "Rocq project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    codex.url = "github:openai/codex";
    codex-nix.url = "github:SecBear/codex-nix";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    codex,
    codex-nix,
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

        vscode = pkgs.vscode-with-extensions.override {
          vscode = pkgs.vscode;
          vscodeExtensions = with pkgs.vscode-extensions; [
            rocq-prover.vsrocq
            vscodevim.vim
          ];
        };

        vsrocqtop = "${pkgs.rocqPackages.vsrocq-language-server}/bin/vsrocqtop";

        settingsJson = builtins.toJSON {
          "vsrocq.path" = vsrocqtop;
          "vsrocq.completion.enable" = true;
          "vsrocq.diagnostics.full" = true;
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
            ]
            ++ [
              codex-nix.packages.${system}.default
            ];

          shellHook = ''
                        export VSROCQTOP_PATH="${vsrocqtop}"

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
          '';
        };
      }
    );
}
