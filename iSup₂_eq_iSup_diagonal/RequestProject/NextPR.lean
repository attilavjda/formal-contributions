import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.SetTheory.Cardinal.Arithmetic

open Set

set_option autoImplicit false

/-!
# Proposed next PR: conditionally complete diagonal suprema

This file contains only the two reviewer-requested diagonal lemmas and one concrete `Cardinal`
caller. It deliberately does not include the complete-lattice mutual-cofinality lemmas.

The pinned Mathlib version used by this project predates the names
`ciSup_mono_of_forall_exists` and `ciSup_mono_of_forall_exists'`. The two private compatibility
lemmas immediately below have the intended signatures and let the proposed proofs use those names
verbatim. They are not part of the proposed upstream addition.
-/

private theorem ciSup_mono_of_forall_exists {α : Type*} {ι κ : Sort*}
    [ConditionallyCompleteLattice α] [Nonempty ι] {f : ι → α} {g : κ → α}
    (hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k) :
    ⨆ i, f i ≤ ⨆ k, g k := by
  refine ciSup_le fun i ↦ ?_
  obtain ⟨k, hk⟩ := h i
  exact hk.trans (le_ciSup hg k)

private theorem ciSup_mono_of_forall_exists' {α : Type*} {ι κ : Sort*}
    [ConditionallyCompleteLinearOrderBot α] {f : ι → α} {g : κ → α}
    (hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k) :
    ⨆ i, f i ≤ ⨆ k, g k := by
  refine ciSup_le' fun i ↦ ?_
  obtain ⟨k, hk⟩ := h i
  exact hk.trans (le_ciSup hg k)

/-- A doubly indexed conditionally complete supremum equals the supremum along its diagonal when
that diagonal is cofinal. Boundedness of the diagonal bounds the entire double family. -/
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*}
    [ConditionallyCompleteLattice α] [Nonempty ι]
    (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k)
    (hb : BddAbove (Set.range fun k ↦ f k k)) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  let b := Classical.choose hb
  have hb' := Classical.choose_spec hb
  have hf : ∀ i, BddAbove (range (f i)) := fun i ↦
    ⟨b, by
      rintro _ ⟨j, rfl⟩
      obtain ⟨k, hik⟩ := h i j
      exact hik.trans (hb' ⟨k, rfl⟩)⟩
  have hfi : BddAbove (range fun i ↦ ⨆ j, f i j) :=
    ⟨b, by
      rintro _ ⟨i, rfl⟩
      exact ciSup_le fun j ↦ by
        obtain ⟨k, hik⟩ := h i j
        exact hik.trans (hb' ⟨k, rfl⟩)⟩
  apply le_antisymm
  · exact ciSup_le fun i ↦ ciSup_mono_of_forall_exists hb (h i)
  · exact ciSup_mono_of_forall_exists hfi fun k ↦
      ⟨k, le_ciSup (hf k) k⟩

/-- The bottomed linear-order version of `ciSup₂_eq_ciSup_diagonal`. No `Nonempty ι` assumption is
needed because an empty indexed supremum is `⊥`. -/
theorem ciSup₂_eq_ciSup_diagonal' {α : Type*} {ι : Sort*}
    [ConditionallyCompleteLinearOrderBot α]
    (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k)
    (hb : BddAbove (Set.range fun k ↦ f k k)) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  let b := Classical.choose hb
  have hb' := Classical.choose_spec hb
  have hf : ∀ i, BddAbove (range (f i)) := fun i ↦
    ⟨b, by
      rintro _ ⟨j, rfl⟩
      obtain ⟨k, hik⟩ := h i j
      exact hik.trans (hb' ⟨k, rfl⟩)⟩
  have hfi : BddAbove (range fun i ↦ ⨆ j, f i j) :=
    ⟨b, by
      rintro _ ⟨i, rfl⟩
      exact ciSup_le' fun j ↦ by
        obtain ⟨k, hik⟩ := h i j
        exact hik.trans (hb' ⟨k, rfl⟩)⟩
  apply le_antisymm
  · exact ciSup_le' fun i ↦ ciSup_mono_of_forall_exists' hb (h i)
  · exact ciSup_mono_of_forall_exists' hfi fun k ↦
      ⟨k, le_ciSup (hf k) k⟩

namespace Cardinal

/-- A diagonal strengthening of `Cardinal.ciSup_add_ciSup`: if the diagonal sums are cofinal among
all pairwise sums, its double supremum collapses to the diagonal. -/
protected theorem ciSup_add_ciSup_diagonal {ι : Type*} [Nonempty ι]
    (f g : ι → Cardinal)
    (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  rw [Cardinal.ciSup_add_ciSup f hf g hg]
  apply ciSup₂_eq_ciSup_diagonal' (fun i j ↦ f i + g j) h
  obtain ⟨bf, hbf⟩ := hf
  obtain ⟨bg, hbg⟩ := hg
  exact ⟨bf + bg, by
    rintro _ ⟨k, rfl⟩
    exact add_le_add (hbf ⟨k, rfl⟩) (hbg ⟨k, rfl⟩)⟩

end Cardinal
