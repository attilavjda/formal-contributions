# Summary of changes for run 2310d90f-f145-4d0d-8e62-27ebda060190
## The contribution: deduplicating `Mathlib/Algebra/Tropical/Basic.lean`

I searched Mathlib (at the version this project pins) for theorems whose *statements* are literally the same term, and `Mathlib/Algebra/Tropical/Basic.lean` came out as the standout small target: a single 470-line file that states five pairs of identical lemmas.

Two causes:

1. **`⊓`/`⊔` versus `min`/`max`.** On a `LinearOrder` the lattice operations *are* `min`/`max` in current Mathlib, so `Tropical.trop_inf`, `untrop_sup`, `inf_eq_add`, `trop_sup_def` are the very same statements as `trop_min`, `untrop_max`, `min_eq_add`, `trop_max_def`. Three of these are duplicated `@[simp]` lemmas — `simp` carries a second copy of a rule that can never do anything the first cannot.
2. **Two spellings of injectivity.** `injective_trop` / `injective_untrop` duplicate `trop_injective` / `untrop_injective`, proved twice fifty lines apart in the same file.

Proposed change: keep the `min`/`max`-spelled lemmas (matching the rest of the file's API, with the lattice-notation material living in `Tropical/Lattice.lean`) and the `_injective`-spelled ones (Mathlib naming convention), and turn the six removed names into deprecated aliases. **17 lines removed, 8 added, three redundant simp lemmas gone, no API lost.** Only one call site inside Mathlib needed updating; no other Mathlib file mentions any removed name.

## What is in the project

- `CONTRIBUTION.md` — full write-up: what is redundant, why, which name survives each pair, and the verification performed.
- `tropical-dedup.patch` — the ready-to-apply diff against `Mathlib/Algebra/Tropical/Basic.lean`.
- `RequestProject/TropicalDedup.lean` — machine-checked evidence, builds with no `sorry`: for each of the six pairs it proves `@Tropical.trop_inf = @Tropical.trop_min` and analogues by `rfl` (these equations only typecheck because the constants have identical types), and it restates each removed lemma verbatim, proving it from the retained lemma alone, so the deprecated aliases lose nothing.
- `scripts/find_duplicate_statements.lean` — the environment scan that produced the candidate list (`dups.txt`): it groups every non-deprecated Mathlib theorem by its statement with binder names normalized.

I also applied the patch to a local Mathlib checkout and rebuilt `Mathlib.Algebra.Tropical.Basic`, `.Lattice` and `.BigOperators` (the only modules importing this material): they compile with no errors and no deprecation warnings. The checkout was then restored to its original state, so the patch ships as a file rather than as a modification of the dependency.
