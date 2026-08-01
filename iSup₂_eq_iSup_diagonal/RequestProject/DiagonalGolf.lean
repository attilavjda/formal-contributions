import Mathlib

/-!
# Checked golfing alternatives for diagonal indexed suprema

This file compares a compact proof of the generic diagonal lemma with shorter
versions of its three motivating ENat/ENNReal call sites.
-/

open Function Set

namespace DiagonalGolf

variable {α : Type*} {ι : Sort*}

/-- A compressed proof that preserves the weak `CompleteSemilatticeSup` assumption
and still generates the infimum dual automatically. -/
@[to_dual iInf₂_eq_iInf_diagonal_compact]
theorem iSup₂_eq_iSup_diagonal_compact [CompleteSemilatticeSup α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · apply sSup_le
    intro _ hx
    obtain ⟨i, rfl⟩ := hx
    apply sSup_le
    intro _ hx
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨k, hk⟩ := h i j
    exact hk.trans <| le_sSup (mem_range_self k)
  · apply sSup_le
    intro _ hx
    obtain ⟨k, rfl⟩ := hx
    exact (le_sSup (show f k k ∈ range (f k) from mem_range_self k)).trans <|
      le_sSup (show sSup (range (f k)) ∈ range (fun i ↦ sSup (range (f i))) from
        mem_range_self k)

/-- If one strengthens the assumption to `CompleteLattice`, the high-level indexed-supremum
API makes the proof very short. This is useful as a comparison, but is not the preferred
upstream statement because it needlessly strengthens the hypothesis. -/
theorem iSup₂_eq_iSup_diagonal_complete [CompleteLattice α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  exact le_antisymm
    (iSup₂_le fun i j ↦ (h i j).elim fun k hk ↦ le_iSup_of_le k hk)
    (iSup_le fun k ↦ le_iSup_of_le k <| le_iSup (f k) k)

/-- `simpa using` can combine both distribution rewrites with diagonal collapse.
The arguments are transposed to match the orientation produced by simplification. -/
theorem enat_iSup_add_iSup_simpa {ι : Type*} (f g : ι → ℕ∞)
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simpa only [ENat.iSup_add, ENat.add_iSup] using
      iSup₂_eq_iSup_diagonal_compact (fun i j ↦ f j + g i) fun i j ↦ h j i

/-- The same compact `simpa using` form for `ENNReal.iSup_add_iSup`. -/
theorem ennreal_iSup_add_iSup_simpa {ι : Type*} (f g : ι → ENNReal)
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simpa only [ENNReal.iSup_add, ENNReal.add_iSup] using
      iSup₂_eq_iSup_diagonal_compact (fun i j ↦ f j + g i) fun i j ↦ h j i

/-- The infimum call site needs no empty-index split, so it becomes one `simpa using`. -/
theorem ennreal_iInf_add_iInf_simpa {ι : Type*} (f g : ι → ENNReal)
    (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) :
    iInf f + iInf g = ⨅ i, f i + g i := by
  simpa only [ENNReal.iInf_add, ENNReal.add_iInf] using
    iInf₂_eq_iInf_diagonal_compact (fun i j ↦ f j + g i) fun i j ↦ h j i

end DiagonalGolf
