import Mathlib

open scoped ENNReal
open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- Two indexed suprema agree when their index families are mutually cofinal: every value of one
family is dominated by some value of the other, and vice versa. This is the genuinely reusable
core behind the diagonal collapse below (it is `iSup_mono'` applied in both directions, packaged as
an equality). -/
@[to_dual]
theorem iSup_eq_iSup_of_forall_exists_le {α : Type*} {ι ι' : Sort*} [CompleteSemilatticeSup α]
    {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i' := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨i, rfl⟩
    obtain ⟨i', hi'⟩ := h₁ i
    exact hi'.trans (le_sSup ⟨i', rfl⟩)
  · apply sSup_le
    rintro _ ⟨i', rfl⟩
    obtain ⟨i, hi⟩ := h₂ i'
    exact hi.trans (le_sSup ⟨i, rfl⟩)

/-- The diagonal collapse is the special case of `iSup_eq_iSup_of_forall_exists_le` where the second
family is the diagonal `k ↦ f k k` (which is trivially cofinal in itself). Shown here over `Type*`,
where `iSup_prod'` is available; the direct proof below works for `ι : Sort*`. -/
example {α : Type*} {ι : Type*} [CompleteLattice α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  rw [iSup_prod' (f := fun i j => f i j)]
  exact iSup_eq_iSup_of_forall_exists_le
    (fun p => h p.1 p.2) (fun k => ⟨(k, k), le_rfl⟩)

/-- A doubly indexed supremum equals the supremum along its diagonal when the diagonal is
cofinal. -/
@[to_dual iInf₂_eq_diagonal]
theorem iSup₂_eq_diagonal {α : Type*} {ι : Sort*} [CompleteSemilatticeSup α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨i, rfl⟩
    apply sSup_le
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j
    exact hk.trans (le_sSup ⟨k, rfl⟩)
  · apply sSup_le
    rintro _ ⟨k, rfl⟩
    exact (le_sSup (s := range (f k)) ⟨k, rfl⟩).trans
      (le_sSup (s := range fun i ↦ ⨆ j, f i j) ⟨k, rfl⟩)

/-- A conditionally complete lattice version of `iSup₂_eq_diagonal`: a doubly indexed
supremum equals the supremum along its diagonal when the diagonal is cofinal and bounded above. -/
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (hf : BddAbove (Set.range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · obtain ⟨b, hb⟩ := id hf
    have hbound : ∀ i j, f i j ≤ b := by
      intro i j
      obtain ⟨k, hk⟩ := h i j
      exact hk.trans (hb ⟨k, rfl⟩)
    apply le_antisymm
    · apply ciSup_le
      intro i
      apply ciSup_le
      intro j
      obtain ⟨k, hk⟩ := h i j
      exact hk.trans (le_ciSup hf k)
    · apply ciSup_le
      intro k
      refine le_ciSup_of_le ?_ k ?_
      · exact ⟨b, by rintro _ ⟨i, rfl⟩; exact ciSup_le (fun j => hbound i j)⟩
      · exact le_ciSup ⟨b, by rintro _ ⟨j, rfl⟩; exact hbound k j⟩ k

/-- A conditionally complete linear order with a bottom element version of
`iSup₂_eq_diagonal`. Here the `Nonempty` assumption on the index is unnecessary, since the
empty supremum is `⊥`. -/
theorem ciSup₂_eq_ciSup_diagonal' {α : Type*} {ι : Sort*} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → ι → α) (hf : BddAbove (Set.range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  obtain ⟨b, hb⟩ := id hf
  have hbound : ∀ i j, f i j ≤ b := by
    intro i j
    obtain ⟨k, hk⟩ := h i j
    exact hk.trans (hb ⟨k, rfl⟩)
  apply le_antisymm
  · apply ciSup_le'
    intro i
    apply ciSup_le'
    intro j
    obtain ⟨k, hk⟩ := h i j
    exact hk.trans (le_ciSup hf k)
  · apply ciSup_le'
    intro k
    refine le_ciSup_of_le ?_ k ?_
    · exact ⟨b, by rintro _ ⟨i, rfl⟩; exact ciSup_le' (fun j => hbound i j)⟩
    · exact le_ciSup ⟨b, by rintro _ ⟨j, rfl⟩; exact hbound k j⟩ k

/-- The existing `ENat.iSup_add_iSup` proof reduced to the generic diagonal lemma. -/
theorem enat_iSup_add_iSup_via_diagonal {ι : Type*} {f g : ι → ENat}
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENat.iSup_add, ENat.add_iSup]
    exact iSup₂_eq_diagonal (fun i j ↦ f i + g j) h

/-- The existing `ENNReal.iSup_add_iSup` proof reduced to the same generic lemma. -/
theorem ennreal_iSup_add_iSup_via_diagonal {ι : Type*} {f g : ι → ENNReal}
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENNReal.iSup_add, ENNReal.add_iSup]
    exact iSup₂_eq_diagonal (fun i j ↦ f i + g j) h

/-- A concrete new caller enabled by the conditionally complete diagonal lemma: a diagonal version
of `Cardinal.ciSup_add_ciSup`, collapsing the double supremum to the diagonal under a cofinality
hypothesis. `Cardinal` is a `ConditionallyCompleteLinearOrderBot`, not a `CompleteLattice`, so the
complete-lattice lemma does not apply here. -/
theorem cardinal_ciSup_add_ciSup_via_diagonal {ι : Type*} [Nonempty ι] (f g : ι → Cardinal)
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ i, f i + g i := by
  rw [Cardinal.ciSup_add_ciSup f hf g hg]
  refine ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j) ?_ h
  obtain ⟨bf, hbf⟩ := hf
  obtain ⟨bg, hbg⟩ := hg
  exact ⟨bf + bg, by rintro _ ⟨k, rfl⟩; exact add_le_add (hbf ⟨k, rfl⟩) (hbg ⟨k, rfl⟩)⟩

/-! ## Follow-up exploration (second review round)

The additions below answer the question "are the two callers exhaustive, and is there a more
structural home for this pattern?". Two concrete conclusions, both machine-checked here:

1. **The two callers are not exhaustive.** The infimum dual `ENNReal.iInf_add_iInf`
   (`Mathlib/Data/ENNReal/Operations.lean`, line 564) is a *third* duplicate of the same argument
   and is simplified by the already-generated dual lemma `iInf₂_eq_diagonal`. (There is no
   `ENat.iInf_add_iInf`, so this dual caller is ENNReal-only.)

2. **The most structural home already exists in Mathlib.** The `IsCofinalFor` predicate
   (`Mathlib/Order/Bounds/Defs.lean`) already carries the cofinality notion, with a full API
   (`.of_subset`, `.rfl`, `.trans`, and the `to_dual` dual `IsCoinitialFor`). Mathlib already has
   the *inequality* half `sSup_le_sSup_of_isCofinalFor` (and dual
   `sInf_le_sInf_of_isCoinitialFor`); only the mutual-cofinality **equality** is missing. Adding it
   is therefore not new framework — it is the natural equality companion of an existing lemma, and
   the indexed lemma `iSup_eq_iSup_of_forall_exists_le` above becomes a one-line corollary of it. -/

/-- Mutually cofinal sets have equal `sSup`. This is the set-level, predicate-based form of
`iSup_eq_iSup_of_forall_exists_le`, and the natural equality companion of the existing
`sSup_le_sSup_of_isCofinalFor`. -/
theorem sSup_eq_sSup_of_isCofinalFor {α : Type*} [CompleteSemilatticeSup α] {s t : Set α}
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) : sSup s = sSup t :=
  le_antisymm (sSup_le_sSup_of_isCofinalFor hst) (sSup_le_sSup_of_isCofinalFor hts)

/-- If `s ⊆ t` and `s` is cofinal in `t`, then `s` and `t` have the same supremum.
This is an immediate convenience corollary of mutual cofinality. -/
theorem sSup_eq_sSup_of_subset_of_isCofinalFor {α : Type*} [CompleteSemilatticeSup α]
    {s t : Set α} (hst : s ⊆ t) (hcf : IsCofinalFor t s) : sSup s = sSup t :=
  sSup_eq_sSup_of_isCofinalFor hst.isCofinalFor hcf

/-- Dual of `sSup_eq_sSup_of_isCofinalFor`. (Stated manually rather than via `@[to_dual]`, since the
`≤`-half lemmas `sSup_le_sSup_of_isCofinalFor` / `sInf_le_sInf_of_isCoinitialFor` are themselves not
`to_dual`-linked in Mathlib.) -/
theorem sInf_eq_sInf_of_isCoinitialFor {α : Type*} [CompleteSemilatticeInf α] {s t : Set α}
    (hst : IsCoinitialFor s t) (hts : IsCoinitialFor t s) : sInf s = sInf t :=
  le_antisymm (sInf_le_sInf_of_isCoinitialFor hts) (sInf_le_sInf_of_isCoinitialFor hst)

/-- `iSup_eq_iSup_of_forall_exists_le` is a corollary of the set-level predicate lemma, obtained by
transporting mutual cofinality of the index families to the ranges. This shows the set-level lemma
is the more structural statement. -/
example {α : Type*} {ι ι' : Sort*} [CompleteSemilatticeSup α] {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i' := by
  rw [iSup, iSup]
  refine sSup_eq_sSup_of_isCofinalFor ?_ ?_
  · rintro _ ⟨i, rfl⟩; obtain ⟨i', hi'⟩ := h₁ i; exact ⟨g i', ⟨i', rfl⟩, hi'⟩
  · rintro _ ⟨i', rfl⟩; obtain ⟨i, hi⟩ := h₂ i'; exact ⟨f i, ⟨i, rfl⟩, hi⟩

/-- The third duplicate caller: `ENNReal.iInf_add_iInf`, reduced to the (already generated) dual
diagonal lemma `iInf₂_eq_diagonal`. This is the exact infimum mirror of
`ennreal_iSup_add_iSup_via_diagonal`. -/
theorem ennreal_iInf_add_iInf_via_diagonal {ι : Type*} {f g : ι → ENNReal}
    (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) :
    iInf f + iInf g = ⨅ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp only [iInf_of_empty, top_add]
  · simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
    exact iInf₂_eq_diagonal (fun i j ↦ f i + g j) h
