import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.SetTheory.Cardinal.Arithmetic

open Set

set_option autoImplicit false

/-!
# Proposed next PR: conditionally complete diagonal suprema (golfed)

This file contains the reviewer-requested diagonal lemma and one concrete `Cardinal` caller.

Golfing notes (see `GOLF.md`):

* The two proposed lemmas `ciSup₂_eq_ciSup_diagonal` (for `ConditionallyCompleteLattice` with
  `[Nonempty ι]`) and `ciSup₂_eq_ciSup_diagonal'` (for `ConditionallyCompleteLinearOrderBot`)
  were duplicates: dropping `[Nonempty ι]` in favour of an `isEmpty_or_nonempty` case split
  makes the first lemma strictly more general, and the second one becomes literally the same
  statement (`ConditionallyCompleteLinearOrderBot` extends `ConditionallyCompleteLattice`).
  Only one lemma is kept; `ciSup₂_eq_ciSup_diagonal'` below is a one-liner kept purely to record
  that fact.
* Consequently only the unprimed API (`ciSup_le`, `ciSup_mono_of_forall_exists`) is used; the
  primed `ciSup_le'` / `ciSup_mono_of_forall_exists'` copies of the proof disappear.
* Inside the proof the two `BddAbove` side goals both come from the single fact
  `∀ i j, f i j ≤ ⨆ k, f k k` ("every entry is below the diagonal supremum"), proved once as `hle`.
  Taking the diagonal supremum itself as the bound avoids destructuring `hb` for some anonymous
  upper bound `b`.
* One half of the antisymmetry is exactly the neighbouring Mathlib lemma
  `ciSup_mono_of_forall_exists`, so it is reused rather than re-proved. The pinned Mathlib of this
  project predates that name, hence the single private shim below (not part of the proposal).
-/

private theorem ciSup_mono_of_forall_exists {α : Type*} {ι κ : Sort*}
    [ConditionallyCompleteLattice α] [Nonempty ι] {f : ι → α} {g : κ → α}
    (hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k) : ⨆ i, f i ≤ ⨆ k, g k := by
  refine ciSup_le fun i ↦ ?_
  obtain ⟨k, hk⟩ := h i
  exact hk.trans (le_ciSup hg k)

/-- A doubly indexed conditionally complete supremum equals the supremum along its diagonal when
that diagonal is cofinal. Boundedness of the diagonal bounds the whole double family. -/
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) (hb : BddAbove (range fun k ↦ f k k)) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
      let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hb k)
    have hrow : ∀ i, BddAbove (range (f i)) := fun i ↦ ⟨_, forall_mem_range.2 (hle i)⟩
    have hcol : BddAbove (range fun i ↦ ⨆ j, f i j) :=
      ⟨_, forall_mem_range.2 fun i ↦ ciSup_le (hle i)⟩
    exact le_antisymm (ciSup_le fun i ↦ ciSup_mono_of_forall_exists hb (h i))
      (ciSup_le fun k ↦ le_ciSup_of_le hcol k (le_ciSup (hrow k) k))

/-- The `ConditionallyCompleteLinearOrderBot` version of `ciSup₂_eq_ciSup_diagonal` is not a
separate lemma: it is the very same statement, since such an order is in particular a
conditionally complete lattice and the lemma above needs no `Nonempty` hypothesis. -/
theorem ciSup₂_eq_ciSup_diagonal' {α : Type*} {ι : Sort*}
    [ConditionallyCompleteLinearOrderBot α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) (hb : BddAbove (range fun k ↦ f k k)) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  ciSup₂_eq_ciSup_diagonal f h hb

namespace Cardinal

/-- A diagonal strengthening of `Cardinal.ciSup_add_ciSup`: if the diagonal sums are cofinal among
all pairwise sums, its double supremum collapses to the diagonal. -/
protected theorem ciSup_add_ciSup_diagonal {ι : Type*} [Nonempty ι] (f g : ι → Cardinal)
    (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  obtain ⟨bf, hbf⟩ := id hf
  obtain ⟨bg, hbg⟩ := id hg
  rw [Cardinal.ciSup_add_ciSup f hf g hg]
  exact ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j) h
    ⟨bf + bg, by rintro _ ⟨k, rfl⟩; exact add_le_add (hbf ⟨k, rfl⟩) (hbg ⟨k, rfl⟩)⟩

end Cardinal
