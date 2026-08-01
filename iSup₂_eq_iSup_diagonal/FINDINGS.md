# Reuse candidate: `Set.subset_prod_iff`

## Repeated pattern

The same elementwise proof occurs in three current Mathlib declarations:

- `Mathlib/Algebra/Group/Subsemigroup/Operations.lean`, `Subsemigroup.le_prod_iff`
- `Mathlib/Algebra/Group/Submonoid/Operations.lean`, `Submonoid.le_prod_iff`
- `Mathlib/LinearAlgebra/Prod.lean`, `Submodule.le_prod_iff`

Each proof expands membership in the two coordinate maps, extracts the first and
second coordinates of a pair, and reconstructs product membership. The core fact
does not depend on multiplication, identities, addition, scalar multiplication,
or any bundled subobject API.

`Subgroup.le_prod_iff` is not a fourth copy: it already delegates to
`Submonoid.le_prod_iff`. This supports extracting the common argument rather than
adding another structure-specific convenience theorem.

## Weak generic statement

```lean
theorem Set.subset_prod_iff {s : Set (α × β)} {t : Set α} {u : Set β} :
    s ⊆ t ×ˢ u ↔ Prod.fst '' s ⊆ t ∧ Prod.snd '' s ⊆ u
```

The name is predictable beside the existing `Set.prod_subset_iff` and
`Set.subset_prod`. It adds no abstraction or framework.

## Simplified proofs

All three copied proofs reduce to the same one-line proof after coercions:

```lean
by
  convert Set.subset_prod_iff
```

Machine-checked versions for subsemigroups, submonoids, and submodules are in
`RequestProject/Main.lean`. The candidate itself is also proved there.

## Suggested upstream shape

Place `Set.subset_prod_iff` near `Set.subset_prod` in `Mathlib/Data/Set/Prod.lean`,
then replace the three elementwise proofs above. No new imports or supporting API
should be necessary.
