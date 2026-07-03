Rules for this Rocq development.

- Verify before asserting: check that a lemma exists with `Search`, `Check`, or
  `Print`, and inspect the goal before suggesting a tactic.
- Never introduce `Admitted`, `admit`, `Axiom`, `Parameter`, or `Conjecture`.
- Restart the Rocq MCP session after a file edit; a stale proof state produces
  misleading advice.
