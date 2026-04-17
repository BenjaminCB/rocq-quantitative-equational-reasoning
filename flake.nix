{
  description = "Flake utils demo";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        vscode = pkgs.vscode-with-extensions.override {
          vscode = pkgs.vscode;
          vscodeExtensions = with pkgs.vscode-extensions; [
            rocq-prover.vsrocq
            vscodevim.vim
          ];
        };

        settingsJson = builtins.toJSON {
          "vsrocq.path" = "${pkgs.rocqPackages.vsrocq-language-server}/bin/vsrocqtop";
          "vsrocq.completion.enable" = true;
          "vsrocq.diagnostics.full" = true;
        };
        # Batteries-included watcher command
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
              rocq makefile -f _CoqProject -o CoqMakeFile
              echo "[rocq-watch] Building"
              make -f CoqMakeFile
            '
        '';
      in {
        packages = {
          default = pkgs.hello;
        };
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [
            vscode
            rocqPackages.vsrocq-language-server
            rocq-core
            rocqPackages.stdlib
            jq
            rocq-watch
          ];

          shellHook = ''
            export VSROCQTOP_PATH="$(which vsrocqtop)"

            mkdir -p .vscode
            cat > .vscode/settings.json <<'JSON'
            ${settingsJson}
            JSON
            echo "Wrote .vscode/settings.json"

            echo Welcome to rocq dev shell
          '';
        };
      }
    );
}
