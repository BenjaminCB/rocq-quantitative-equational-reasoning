# Important

The development shell uses the `coq-lsp` VS Code extension and language server.
It reads `_CoqProject` for the project load path and checks documents
incrementally.

The Nix shell regenerates `.vscode/settings.json`. Make persistent editor
configuration changes in `settingsJson` in `flake.nix`.

# What is included

- A VS Code installation with `coq-lsp` configured for lazy incremental
  checking. Move the cursor to a proof sentence to display its goal state.
- An optional `rocq-watch` command that recompiles when `.v` files under `src`
  change. Do not run it with Auto Save during interactive proof development,
  since frequent `.vo` rewrites can invalidate language-server state.
- A small example showing how a simple multi file setup with dependencies can be
  made.
