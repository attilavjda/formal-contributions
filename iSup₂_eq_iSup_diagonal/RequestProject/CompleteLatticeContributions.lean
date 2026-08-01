import Mathlib

/-!
# Prototypes for two complete-lattice contribution proposals

These declarations validate the proposed APIs and show representative downstream
refactors without modifying the vendored Mathlib source.
-/

open Function Set

namespace ContributionExamples

section Complete

variable {α : Type*} {ι ι' : Sort*}

/-- Mutual cofinality of two indexed families gives equal suprema. -/
theorem iSup_eq_iSup_of_forall_exists_le [CompleteSemilatticeSup α]
    {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i' := by
  apply le_antisymm
  · apply sSup_le
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨i', hi'⟩ := h₁ i
    exact hi'.trans (le_sSup ⟨i', rfl⟩)
  · apply sSup_le
    intro x hx
    obtain ⟨i', rfl⟩ := hx
    obtain ⟨i, hi⟩ := h₂ i'
    exact hi.trans (le_sSup ⟨i, rfl⟩)

/-- A double supremum collapses to its diagonal when the diagonal is cofinal. -/
@[to_dual iInf₂_eq_iInf_diagonal]
theorem iSup₂_eq_iSup_diagonal [CompleteSemilatticeSup α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · refine sSup_le ?_
    intro x hx
    simp only [iSup] at hx
    obtain ⟨i, rfl⟩ := hx
    apply sSup_le
    intro y hy
    simp only [mem_range] at hy
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨k₂, hk⟩ := h i j
    have : f k₂ k₂ ≤ iSup (fun k => f k k) := by
      rw [iSup]
      exact le_sSup (mem_range_self k₂)
    exact le_trans hk this
  · refine sSup_le ?_
    intro x hx
    simp only [mem_range] at hx
    obtain ⟨k₀, rfl⟩ := hx
    have h1 : f k₀ k₀ ≤ sSup (range fun j => f k₀ j) := le_sSup (mem_range_self k₀)
    have h2 : sSup (range fun j => f k₀ j) ≤ sSup (range fun i => sSup (range fun j => f i j)) :=
      le_sSup ⟨k₀, rfl⟩
    exact le_trans h1 h2

/-- Mutually cofinal sets have equal suprema. -/
theorem sSup_eq_sSup_of_isCofinalFor [CompleteSemilatticeSup α] {s t : Set α}
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) :
    sSup s = sSup t := by
  apply le_antisymm
  · apply sSup_le
    intro x hx
    obtain ⟨y, hyt, hxy⟩ := hst hx
    exact hxy.trans (le_sSup hyt)
  · apply sSup_le
    intro x hx
    obtain ⟨y, hys, hxy⟩ := hts hx
    exact hxy.trans (le_sSup hys)

/-- Mutually coinitial sets have equal infima. -/
theorem sInf_eq_sInf_of_isCoinitialFor [CompleteSemilatticeInf α] {s t : Set α}
    (hst : IsCoinitialFor s t) (hts : IsCoinitialFor t s) :
    sInf s = sInf t := by
  apply le_antisymm
  · -- sInf s ≤ sInf t
    rw [le_sInf_iff]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hts hy
    exact le_trans (sInf_le hx) hxy
  · -- sInf t ≤ sInf s
    rw [le_sInf_iff]
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hst hx
    exact le_trans (sInf_le hy) hyx

end Complete

section ExistingProofRefactors

/-- The generic diagonal lemma leaves only ENat-specific distribution over suprema. -/
theorem enat_iSup_add_iSup_example {ι : Type*} (f g : ι → ℕ∞)
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · rw [ENat.iSup_add]
    simp_rw [ENat.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h

/-- The same proof works for ENNReal. -/
theorem ennreal_iSup_add_iSup_example {ι : Type*} (f g : ι → ENNReal)
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · rw [ENNReal.iSup_add]
    simp_rw [ENNReal.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h

/-- The generated dual diagonal lemma shortens the corresponding ENNReal infimum proof. -/
theorem ennreal_iInf_add_iInf_example {ι : Type*} (f g : ι → ENNReal)
    (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) :
    iInf f + iInf g = ⨅ i, f i + g i := by
  rw [ENNReal.iInf_add]
  simp_rw [ENNReal.add_iInf]
  exact iInf₂_eq_iInf_diagonal (fun i j ↦ f i + g j) h

end ExistingProofRefactors

section Conditional

variable {α : Type*} {ι : Sort*}

/-- Conditionally complete diagonal collapse for a nonempty index type. -/
theorem ciSup₂_eq_ciSup_diagonal [ConditionallyCompleteLattice α] [Nonempty ι]
    (f : ι → ι → α) (hf : BddAbove (Set.range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    apply ciSup_le
    intro j
    obtain ⟨k, hk⟩ := h i j
    exact hk.trans (le_ciSup_of_le hf k (le_refl _))
  · -- Need to show ⨆ k, f k k ≤ ⨆ i, ⨆ j, f i j
    -- First establish that all f i j are bounded by some f k k which is bounded
    have hbb : ∀ i j, ∃ k, f i j ≤ f k k := h
    -- The range of (fun k => f k k) bounds everything
    apply ciSup_le
    intro k
    -- Bound for each row: range (fun j => f k j) is bounded by hf
    have hrow : ∀ k, BddAbove (range fun j => f k j) := fun k => by
      refine ⟨hf.choose, fun x hx => ?_⟩
      obtain ⟨j, rfl⟩ := hx
      obtain ⟨k', hk'⟩ := hbb k j
      exact le_trans hk' (hf.choose_spec ⟨k', rfl⟩)
    -- Bound for the double sup: range (fun i => ⨆ j, f i j) is bounded by hf
    have hdouble : BddAbove (range fun i => ⨆ j, f i j) := by
      refine ⟨hf.choose, fun x hx => ?_⟩
      obtain ⟨i, rfl⟩ := hx
      exact ciSup_le fun j => le_trans (hbb i j).choose_spec (hf.choose_spec ⟨_, rfl⟩)
    calc f k k ≤ ⨆ j, f k j := le_ciSup_of_le (hrow k) k (le_refl _)
      _ ≤ ⨆ i, ⨆ j, f i j := le_ciSup_of_le hdouble k (le_refl _)

/-- A bottom element handles the empty-index case, so `Nonempty ι` is unnecessary. -/
theorem ciSup₂_eq_ciSup_diagonal' [ConditionallyCompleteLinearOrderBot α]
    (f : ι → ι → α) (hf : BddAbove (Set.range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  by_cases hι : Nonempty ι
  · exact ciSup₂_eq_ciSup_diagonal f hf h
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    simp

/-- Corrected cross-index monotonicity for conditional infima.
The proposed version had the nonemptiness and boundedness assumptions on the
wrong families; it is not valid in a general conditionally complete lattice. -/
theorem ciInf_mono'_corrected {ι' : Sort*} [ConditionallyCompleteLattice α] [Nonempty ι']
    {f : ι → α} {g : ι' → α}
    (hf : BddBelow (Set.range f)) (h : ∀ i', ∃ i, f i ≤ g i') :
    ⨅ i, f i ≤ ⨅ i', g i' := by
  apply le_ciInf
  intro i'
  obtain ⟨i, hi⟩ := h i'
  exact (ciInf_le hf i).trans hi

/-- A cofinal family comparison for conditionally complete suprema. -/
theorem csSup_le_csSup_of_isCofinalFor [ConditionallyCompleteLattice α]
    {s t : Set α} (ht : BddAbove t) (hs : s.Nonempty)
    (hst : IsCofinalFor s t) :
    sSup s ≤ sSup t := by
  apply csSup_le hs
  intro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact hab.trans (le_csSup ht hb)

/-- Mutual cofinality gives equality for bounded nonempty sets. -/
theorem csSup_eq_csSup_of_isCofinalFor [ConditionallyCompleteLattice α]
    {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty)
    (hbs : BddAbove s) (hbt : BddAbove t)
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) :
    sSup s = sSup t := by
  exact le_antisymm
    (csSup_le_csSup_of_isCofinalFor hbt hs hst)
    (csSup_le_csSup_of_isCofinalFor hbs ht hts)

/-- A coinitial family comparison for conditionally complete infima. -/
theorem csInf_le_csInf_of_isCoinitialFor [ConditionallyCompleteLattice α]
    {s t : Set α} (ht : BddBelow t) (hs : s.Nonempty)
    (hst : IsCoinitialFor s t) :
    sInf t ≤ sInf s := by
  apply le_csInf hs
  intro a ha
  obtain ⟨b, hb, hba⟩ := hst ha
  exact le_trans (csInf_le ht hb) hba

/-- Mutual coinitiality gives equality for bounded nonempty sets. -/
theorem csInf_eq_csInf_of_isCoinitialFor [ConditionallyCompleteLattice α]
    {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty)
    (hbs : BddBelow s) (hbt : BddBelow t)
    (hst : IsCoinitialFor s t) (hts : IsCoinitialFor t s) :
    sInf s = sInf t := by
  exact le_antisymm
    (csInf_le_csInf_of_isCoinitialFor hbs ht hts)
    (csInf_le_csInf_of_isCoinitialFor hbt hs hst)

end Conditional

/-- Cardinal addition followed by conditional diagonal collapse. -/
theorem cardinal_ciSup_add_ciSup_diagonal {ι : Type} [Nonempty ι]
    (f g : ι → Cardinal)
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  rw [Cardinal.ciSup_add_ciSup f (Cardinal.bddAbove_range f) g (Cardinal.bddAbove_range g)]
  exact ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j)
    (Cardinal.bddAbove_range fun k ↦ f k + g k) h

end ContributionExamples
