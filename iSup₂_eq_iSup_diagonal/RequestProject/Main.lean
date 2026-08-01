import Mathlib

/-!
# A reusable criterion for containment in a product set

This file records a small candidate lemma found by comparing the local proofs of
`Subsemigroup.le_prod_iff`, `Submonoid.le_prod_iff`, and `Submodule.le_prod_iff`.
The generic statement belongs at the `Set` level and lets each structured proof
reduce to coercion/map bookkeeping.
-/

namespace Set

/-- A set of pairs is contained in a product exactly when each of its coordinate
projections is contained in the corresponding factor. -/
theorem subset_prod_iff {α β : Type*} {s : Set (α × β)} {t : Set α} {u : Set β} :
    s ⊆ t ×ˢ u ↔ Prod.fst '' s ⊆ t ∧ Prod.snd '' s ⊆ u := by
  grind

end Set

namespace ReuseExamples

section Subsemigroup

variable {M N : Type*} [Mul M] [Mul N]

/-- Replacement proof for `Subsemigroup.le_prod_iff`. -/
theorem subsemigroup_le_prod_iff_example
    {s : Subsemigroup M} {t : Subsemigroup N} {u : Subsemigroup (M × N)} :
    u ≤ s.prod t ↔ u.map (MulHom.fst M N) ≤ s ∧ u.map (MulHom.snd M N) ≤ t := by
  convert Set.subset_prod_iff

end Subsemigroup

section Submonoid

variable {M N : Type*} [MulOneClass M] [MulOneClass N]

/-- Replacement proof for `Submonoid.le_prod_iff`. -/
theorem submonoid_le_prod_iff_example
    {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    u ≤ s.prod t ↔ u.map (MonoidHom.fst M N) ≤ s ∧ u.map (MonoidHom.snd M N) ≤ t := by
  convert Set.subset_prod_iff

end Submonoid

section Submodule

variable {R M N : Type*} [Semiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- Replacement proof for `Submodule.le_prod_iff`. -/
theorem submodule_le_prod_iff_example
    {s : Submodule R M} {t : Submodule R N} {u : Submodule R (M × N)} :
    u ≤ s.prod t ↔
      u.map (LinearMap.fst R M N) ≤ s ∧ u.map (LinearMap.snd R M N) ≤ t := by
  convert Set.subset_prod_iff

end Submodule

end ReuseExamples
