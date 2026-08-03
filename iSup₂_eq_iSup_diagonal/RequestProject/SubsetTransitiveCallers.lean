import RequestProject.Diagonal
import Mathlib.Topology.Order.MonotoneConvergence

open Function Set

set_option autoImplicit false

/-- If `s` is a cofinal subset of `t`, then the two sets have the same supremum. -/
theorem sSup_eq_sSup_of_subset_of_isCofinalFor_demo {α : Type*} [CompleteSemilatticeSup α]
    {s t : Set α} (hst : s ⊆ t) (hts : IsCofinalFor t s) : sSup s = sSup t :=
  sSup_eq_sSup_of_isCofinalFor hst.isCofinalFor hts

/-- An indexed version of cofinal-subset invariance: a subfamily has the same supremum as the full
family when every value of the full family is bounded by a value of the subfamily. -/
theorem iSup_eq_iSup_of_range_subset_of_forall_exists_le_demo
    {α : Type*} {ι κ : Sort*} [CompleteSemilatticeSup α] {f : ι → α} {g : κ → α}
    (hsub : range g ⊆ range f) (hcof : ∀ i, ∃ k, f i ≤ g k) :
    ⨆ i, f i = ⨆ k, g k := by
  rw [iSup, iSup]
  symm
  apply sSup_eq_sSup_of_subset_of_isCofinalFor_demo hsub
  rintro _ ⟨i, rfl⟩
  obtain ⟨k, hik⟩ := hcof i
  exact ⟨g k, ⟨k, rfl⟩, hik⟩

/-- A cofinal reindexing has the same supremum. This is the natural intermediate API between the
set-level subset lemma and concrete diagonal/subsequence arguments. -/
theorem iSup_comp_eq_of_forall_exists_le_demo
    {α β : Type*} {ι : Sort*} [CompleteSemilatticeSup α] (f : β → α) (s : ι → β)
    (hcof : ∀ b, ∃ i, f b ≤ f (s i)) :
    ⨆ i, f (s i) = ⨆ b, f b := by
  symm
  apply iSup_eq_iSup_of_range_subset_of_forall_exists_le_demo
  · rintro _ ⟨i, rfl⟩
    exact ⟨s i, rfl⟩
  · exact hcof

/-- Refactoring of the diagonal lemma through the indexed cofinal-subfamily lemma. The product
reindexing used here requires `ι : Type*`; the direct diagonal proof remains useful for `Sort*`. -/
theorem iSup₂_eq_diagonal_via_cofinal_subset_demo
    {α ι : Type*} [CompleteLattice α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  rw [iSup_prod' (f := fun i j => f i j)]
  exact (iSup_comp_eq_of_forall_exists_le_demo (fun p ↦ f p.1 p.2) (fun k ↦ (k, k))
    (fun p ↦ h p.1 p.2)).symm

/-- Refactoring of `Monotone.iSup_comp_eq` through the indexed cofinal-subfamily lemma. -/
theorem monotone_iSup_comp_eq_via_cofinal_subset_demo
    {α β : Type*} {ι : Sort*} [CompleteLattice α] [Preorder β]
    {f : β → α} (hf : Monotone f) {s : ι → β} (hs : ∀ x, ∃ i, x ≤ s i) :
    ⨆ x, f (s x) = ⨆ y, f y := by
  exact iSup_comp_eq_of_forall_exists_le_demo f s fun x ↦
    (hs x).imp fun _ hxi ↦ hf hxi

/-- Refactoring of `iSup_eq_iSup_subseq_of_monotone`. -/
theorem iSup_eq_iSup_subseq_of_monotone_via_cofinal_subset_demo
    {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Filter.Tendsto φ l Filter.atTop) : ⨆ i, f i = ⨆ i, f (φ i) := by
  exact (iSup_comp_eq_of_forall_exists_le_demo f φ fun i ↦
    Exists.imp (fun _ hij ↦ hf hij) (hφ.eventually <| Filter.eventually_ge_atTop i).exists).symm

/-- Refactoring of `iSup_eq_iSup_subseq_of_antitone`. -/
theorem iSup_eq_iSup_subseq_of_antitone_via_cofinal_subset_demo
    {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Filter.Tendsto φ l Filter.atBot) : ⨆ i, f i = ⨆ i, f (φ i) := by
  exact (iSup_comp_eq_of_forall_exists_le_demo f φ fun i ↦
    Exists.imp (fun _ hji ↦ hf hji) (hφ.eventually <| Filter.eventually_le_atBot i).exists).symm

/-- Refactoring of `iSup_ne_bot_subtype`. -/
theorem iSup_ne_bot_subtype_via_cofinal_subset_demo
    {α : Type*} {ι : Sort*} [CompleteLattice α] (f : ι → α) :
    ⨆ i : {i // f i ≠ ⊥}, f i = ⨆ i, f i := by
  by_cases! htriv : ∀ i, f i = ⊥
  · simp only [iSup_bot, (funext htriv : f = _)]
  symm
  apply iSup_eq_iSup_of_range_subset_of_forall_exists_le_demo
  · rintro _ ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · intro i
    by_cases hi : f i = ⊥
    · obtain ⟨i₀, hi₀⟩ := htriv
      refine ⟨⟨i₀, hi₀⟩, ?_⟩
      rw [hi]
      exact bot_le
    · exact ⟨⟨i, hi⟩, le_rfl⟩
