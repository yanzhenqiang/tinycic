# Project conventions

## Keep proofs small and flat

- Split every non-trivial proof into small helper lemmas.
- Each lemma should do one conceptual step only.
- Avoid deeply nested tactic blocks and large `have` chains inside a single theorem.
- Prefer `let ... in ...` for local bindings in expression-style proofs.
- If a proof term is becoming large or slow to check, stop and extract a lemma.

## Modularity for geometry work

- When adding or replacing a family of axioms/theorems, prefer creating a dedicated file under `lib/GeometryCommon/`.
- Split the work into independent helper lemmas with clear geometric meaning, then compose them in the main theorem.
