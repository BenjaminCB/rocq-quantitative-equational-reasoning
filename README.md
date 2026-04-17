# Important

The current version of vsrocq does not load _RocqProject. Therefore they are
named using the old Coq, i.e _CoqProject etc.

The .vscode settings also contains the nix generated path to vsrocqtop. Fell
free to make changes to the file, but do not delete it.

# What is included

- A vscode with vsrocq installed and setup with the vsrocq-language-server.
- A file watcher command rocq-watch which recompiles then .v files change in the
  src dir, meaning you only have to run the Rocq reset command within vscode to
  get access to any new definitions proofs etc.
- A small example showing how a simple multi file setup with dependencies can be
  made.
