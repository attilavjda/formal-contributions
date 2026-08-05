import Mathlib

/-!
# PR 1, modularised: cofinal collapse of iterated suprema

This file machine-checks the modularised form of PR 1 proposed in review, and one refinement of it.

* `AsProposed` — the proposal exactly as written: two `IsCofinalFor` utility lemmas, the
  `CompleteLattice` collapse lemmas (mutual cofinality, cofinal family, diagonal) with their duals
  written out by hand through `αᵒᵈ`, the three replacement call-site proofs together with `rfl`
  checks against the current Mathlib statements, and two multiplicative statements Mathlib lacks.
  Everything in it compiles unchanged.

* `Refined` — the same modular chain stated over `CompleteSemilatticeSup` instead of
  `CompleteLattice`, with the duals produced by `@[to_dual]` instead of by hand. This is strictly
  more general and halves the number of declarations that have to be written; the call sites are
  unaffected (`ℝ≥0∞`, `ℕ∞` are complete lattices).

The generality difference is forced by the API used in the proofs: `iSup_mono'`, `iSup₂_le`,
`le_iSup₂` and `iSup_le` all carry `[CompleteLattice α]`, whereas `sSup_le`/`le_sSup` only need
`[CompleteSemilatticeSup α]`.
-/

open Set

set_option autoImplicit false

namespace PR1Modular

/-! ## The proposal, exactly as written -/

namespace AsProposed

/-! ### Part (a): `Mathlib/Order/Bounds/Basic.lean` -/

section Bounds
variable {α : Type*} {ι κ : Sort*} [Preorder α]

/-- Cofinality of ranges, spelled with families. -/
@[simp]
theorem isCofinalFor_range_iff {f : ι → α} {g : κ → α} :
    IsCofinalFor (range f) (range g) ↔ ∀ i, ∃ j, f i ≤ g j := by
  simp [IsCofinalFor]

/-- If `s` is cofinal in `t` and `t` is bounded above, then so is `s`. -/
theorem IsCofinalFor.bddAbove {s t : Set α} (h : IsCofinalFor s t) (ht : BddAbove t) :
    BddAbove s :=
  ht.imp fun _ hc => upperBounds_mono_of_isCofinalFor h hc

/-- If `s` is coinitial in `t` and `t` is bounded below, then so is `s`. -/
theorem IsCoinitialFor.bddBelow {s t : Set α} (h : IsCoinitialFor s t) (ht : BddBelow t) :
    BddBelow s :=
  IsCofinalFor.bddAbove (α := αᵒᵈ) h ht

end Bounds

/-! ### Part (b): `Mathlib/Order/CompleteLattice/Basic.lean` -/

section CompleteLattice
variable {α : Type*} {ι κ ν : Sort*} [CompleteLattice α]

/-- Mutually cofinal families have the same supremum. -/
theorem iSup_eq_iSup_of_forall_exists_le {f : ι → α} {g : κ → α} (hfg : ∀ i, ∃ j, f i ≤ g j)
    (hgf : ∀ j, ∃ i, g j ≤ f i) : ⨆ i, f i = ⨆ j, g j :=
  le_antisymm (iSup_mono' hfg) (iSup_mono' hgf)

/-- Mutually coinitial families have the same infimum. -/
theorem iInf_eq_iInf_of_forall_exists_le {f : ι → α} {g : κ → α} (hfg : ∀ i, ∃ j, g j ≤ f i)
    (hgf : ∀ j, ∃ i, f i ≤ g j) : ⨅ i, f i = ⨅ j, g j :=
  iSup_eq_iSup_of_forall_exists_le (α := αᵒᵈ) hfg hgf

/-- A doubly indexed supremum collapses onto any family that is cofinal in it. -/
theorem iSup₂_eq_iSup_of_forall_exists_le (F : ι → κ → α) (G : ν → α)
    (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k :=
  le_antisymm (iSup₂_le fun i j => (hle i j).elim fun k hk => hk.trans (le_iSup G k))
    (iSup_le fun k => (hge k).elim fun i hi => hi.elim fun j hj =>
      hj.trans (le_iSup₂ (f := F) i j))

/-- A doubly indexed infimum collapses onto any family that is coinitial in it. -/
theorem iInf₂_eq_iInf_of_forall_exists_le (F : ι → κ → α) (G : ν → α)
    (hge : ∀ i j, ∃ k, G k ≤ F i j) (hle : ∀ k, ∃ i j, F i j ≤ G k) :
    ⨅ i, ⨅ j, F i j = ⨅ k, G k :=
  iSup₂_eq_iSup_of_forall_exists_le (α := αᵒᵈ) F G hge hle

/-- If every entry of a square family is dominated by a diagonal entry, then the iterated
supremum collapses onto the diagonal. -/
theorem iSup₂_eq_iSup_diagonal (F : ι → ι → α) (h : ∀ i j, ∃ k, F i j ≤ F k k) :
    ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  iSup₂_eq_iSup_of_forall_exists_le F _ h fun k => ⟨k, k, le_rfl⟩

/-- If every entry of a square family dominates a diagonal entry, then the iterated
infimum collapses onto the diagonal. -/
theorem iInf₂_eq_iInf_diagonal (F : ι → ι → α) (h : ∀ i j, ∃ k, F k k ≤ F i j) :
    ⨅ i, ⨅ j, F i j = ⨅ k, F k k :=
  iInf₂_eq_iInf_of_forall_exists_le F _ h fun k => ⟨k, k, le_rfl⟩

end CompleteLattice

/-! ### Part (c): the three call sites

Each replacement is followed by a `rfl` check against the existing declaration, which succeeds only
if the statement was not changed. The residual `cases isEmpty_or_nonempty ι` is unavoidable: the
distributivity lemmas (`ENNReal.iSup_add`, `ENat.add_iSup`, …) need `[Nonempty ι]`. -/

section CallSites
open scoped ENNReal

/-- Replacement proof for `ENNReal.iSup_add_iSup`. -/
theorem ennreal_iSup_add_iSup {ι : Sort*} {f g : ι → ℝ≥0∞}
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENNReal.iSup_add, ENNReal.add_iSup]
    exact iSup₂_eq_iSup_diagonal _ h

example : @ennreal_iSup_add_iSup = @ENNReal.iSup_add_iSup := rfl

/-- Replacement proof for `ENNReal.iInf_add_iInf`. -/
theorem ennreal_iInf_add_iInf {ι : Sort*} {f g : ι → ℝ≥0∞}
    (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a := by
  simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
  exact iInf₂_eq_iInf_diagonal _ h

example : @ennreal_iInf_add_iInf = @ENNReal.iInf_add_iInf := rfl

/-- Replacement proof for `ENat.iSup_add_iSup`. -/
theorem enat_iSup_add_iSup {ι : Sort*} {f g : ι → ℕ∞}
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENat.iSup_add, ENat.add_iSup]
    exact iSup₂_eq_iSup_diagonal _ h

example : @enat_iSup_add_iSup = @ENat.iSup_add_iSup := rfl

/-- New: the multiplicative analogue of `ENNReal.iSup_add_iSup`. -/
theorem ennreal_iSup_mul_iSup {ι : Sort*} [Nonempty ι] {f g : ι → ℝ≥0∞}
    (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) : iSup f * iSup g = ⨆ i, f i * g i := by
  simp_rw [ENNReal.iSup_mul, ENNReal.mul_iSup]
  exact iSup₂_eq_iSup_diagonal _ h

/-- New: the multiplicative analogue of `ENat.iSup_add_iSup`. -/
theorem enat_iSup_mul_iSup {ι : Sort*} [Nonempty ι] {f g : ι → ℕ∞}
    (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) : iSup f * iSup g = ⨆ i, f i * g i := by
  simp_rw [ENat.iSup_mul, ENat.mul_iSup]
  exact iSup₂_eq_iSup_diagonal _ h

end CallSites

end AsProposed

/-! ## The same chain, one typeclass weaker, with the duals generated

Two changes only:

* the order lemmas move from `CompleteLattice` to `CompleteSemilatticeSup`, which forces the
  `sSup_le`/`le_sSup` API in the proofs;
* every dual is produced by `@[to_dual]` rather than written out through `αᵒᵈ`, so six
  declarations become three. (`to_dual` also picks the dual names automatically here; the explicit
  names below are given only for readability and the linter accepts either.) -/

namespace Refined

section Bounds
variable {α : Type*} {ι κ : Sort*} [Preorder α]

/-- Cofinality of ranges, spelled with families. -/
@[to_dual, simp]
theorem isCofinalFor_range_iff {f : ι → α} {g : κ → α} :
    IsCofinalFor (range f) (range g) ↔ ∀ i, ∃ j, f i ≤ g j := by
  simp [IsCofinalFor]

/-- If `s` is cofinal in `t` and `t` is bounded above, then so is `s`. -/
@[to_dual IsCoinitialFor.bddBelow]
theorem IsCofinalFor.bddAbove {s t : Set α} (h : IsCofinalFor s t) (ht : BddAbove t) :
    BddAbove s :=
  ht.imp fun _ hc => upperBounds_mono_of_isCofinalFor h hc

end Bounds

section CompleteSemilattice
variable {α : Type*} {ι κ ν : Sort*} [CompleteSemilatticeSup α]

/-- Mutually cofinal families have the same supremum. -/
@[to_dual]
theorem iSup_eq_iSup_of_forall_exists_le {f : ι → α} {g : κ → α} (hfg : ∀ i, ∃ j, f i ≤ g j)
    (hgf : ∀ j, ∃ i, g j ≤ f i) : ⨆ i, f i = ⨆ j, g j := by
  refine le_antisymm (sSup_le ?_) (sSup_le ?_) <;> rintro _ ⟨i, rfl⟩
  · obtain ⟨j, hj⟩ := hfg i
    exact hj.trans (le_sSup ⟨j, rfl⟩)
  · obtain ⟨j, hj⟩ := hgf i
    exact hj.trans (le_sSup ⟨j, rfl⟩)

/-- A doubly indexed supremum collapses onto any family that is cofinal in it. -/
@[to_dual iInf₂_eq_iInf_of_forall_exists_le]
theorem iSup₂_eq_iSup_of_forall_exists_le (F : ι → κ → α) (G : ν → α)
    (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k := by
  refine le_antisymm (sSup_le ?_) (sSup_le ?_) <;> rintro _ ⟨i, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hle i j
    exact hk.trans (le_sSup ⟨k, rfl⟩)
  · obtain ⟨a, b, hab⟩ := hge i
    exact hab.trans ((le_sSup (s := range (F a)) ⟨b, rfl⟩).trans (le_sSup ⟨a, rfl⟩))

/-- If every entry of a square family is dominated by a diagonal entry, then the iterated
supremum collapses onto the diagonal. -/
@[to_dual iInf₂_eq_iInf_diagonal]
theorem iSup₂_eq_iSup_diagonal (F : ι → ι → α) (h : ∀ i j, ∃ k, F i j ≤ F k k) :
    ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  iSup₂_eq_iSup_of_forall_exists_le F _ h fun k => ⟨k, k, le_rfl⟩

end CompleteSemilattice

/-! The generated duals really are the infimum statements, at `CompleteSemilatticeInf`. -/
example {α : Type*} {ι : Sort*} [CompleteSemilatticeInf α] (F : ι → ι → α)
    (h : ∀ i j, ∃ k, F k k ≤ F i j) : ⨅ i, ⨅ j, F i j = ⨅ k, F k k :=
  iInf₂_eq_iInf_diagonal F h

/-! The call sites are unchanged: `ℝ≥0∞` and `ℕ∞` are complete lattices, hence in particular
complete sup-semilattices. -/

section CallSites
open scoped ENNReal

theorem ennreal_iSup_add_iSup {ι : Sort*} {f g : ι → ℝ≥0∞}
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENNReal.iSup_add, ENNReal.add_iSup]
    exact iSup₂_eq_iSup_diagonal _ h

example : @ennreal_iSup_add_iSup = @ENNReal.iSup_add_iSup := rfl

theorem ennreal_iInf_add_iInf {ι : Sort*} {f g : ι → ℝ≥0∞}
    (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a := by
  simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
  exact iInf₂_eq_iInf_diagonal _ h

example : @ennreal_iInf_add_iInf = @ENNReal.iInf_add_iInf := rfl

theorem enat_iSup_add_iSup {ι : Sort*} {f g : ι → ℕ∞}
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENat.iSup_add, ENat.add_iSup]
    exact iSup₂_eq_iSup_diagonal _ h

example : @enat_iSup_add_iSup = @ENat.iSup_add_iSup := rfl

/-! The two multiplicative statements do not need `[Nonempty ι]` either: for empty `ι` both sides
are `0`, so the same `cases isEmpty_or_nonempty ι` opening that the additive proofs use also
covers them. -/

/-- The multiplicative analogue of `ENNReal.iSup_add_iSup`, without a `Nonempty` hypothesis. -/
theorem ennreal_iSup_mul_iSup {ι : Sort*} {f g : ι → ℝ≥0∞}
    (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) : iSup f * iSup g = ⨆ i, f i * g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENNReal.iSup_mul, ENNReal.mul_iSup]
    exact iSup₂_eq_iSup_diagonal _ h

/-- The multiplicative analogue of `ENat.iSup_add_iSup`, without a `Nonempty` hypothesis. -/
theorem enat_iSup_mul_iSup {ι : Sort*} {f g : ι → ℕ∞}
    (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) : iSup f * iSup g = ⨆ i, f i * g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENat.iSup_mul, ENat.mul_iSup]
    exact iSup₂_eq_iSup_diagonal _ h

end CallSites

end Refined

/-! ## Where part (a) has a caller

`IsCofinalFor.bddAbove` is unused by parts (b) and (c), but it does discharge the inner
boundedness side condition of the conditionally complete diagonal lemma: each row of the family is
cofinal in the diagonal, so it inherits the diagonal's upper bound. The outer condition
`BddAbove (range fun i ↦ ⨆ j, f i j)` is not an instance of it, since a row supremum need not lie
below any single diagonal entry. -/

example {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α] (f : ι → ι → α)
    (hf : BddAbove (Set.range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) (i : ι) :
    BddAbove (Set.range (f i)) :=
  Refined.IsCofinalFor.bddAbove
    (by rintro _ ⟨j, rfl⟩; obtain ⟨k, hk⟩ := h i j; exact ⟨f k k, ⟨k, rfl⟩, hk⟩) hf

end PR1Modular
