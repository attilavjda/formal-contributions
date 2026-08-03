import Mathlib.Topology.Order.MonotoneConvergence

open Function Set
open Filter

set_option autoImplicit false

/-!
# Mutual cofinality equalities

This file contains only the declarations and replacement proofs proposed for the mutual-cofinality
PR.  The set-level equalities package the two existing one-sided comparison lemmas.  The indexed
versions apply them to `Set.range`.  The final two examples are drop-in replacement proof bodies
for the existing monotone and antitone subsequence theorems; their `iInf` duals already delegate to
those theorems and therefore need no separate rewrite.
-/

/-- Mutually cofinal sets have the same supremum. -/
theorem sSup_eq_sSup_of_isCofinalFor {α : Type*} [CompleteSemilatticeSup α] {s t : Set α}
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) : sSup s = sSup t :=
  le_antisymm (sSup_le_sSup_of_isCofinalFor hst) (sSup_le_sSup_of_isCofinalFor hts)

/-- Mutually coinitial sets have the same infimum. -/
theorem sInf_eq_sInf_of_isCoinitialFor {α : Type*} [CompleteSemilatticeInf α] {s t : Set α}
    (hst : IsCoinitialFor s t) (hts : IsCoinitialFor t s) : sInf s = sInf t :=
  le_antisymm
    (sInf_le_sInf_of_isCoinitialFor hts)
    (sInf_le_sInf_of_isCoinitialFor hst)

/-- Two indexed suprema are equal when their families are mutually cofinal. -/
theorem iSup_eq_iSup_of_forall_exists_le
    {α : Type*} {ι κ : Sort*} [CompleteSemilatticeSup α] {f : ι → α} {g : κ → α}
    (hfg : ∀ i, ∃ k, f i ≤ g k) (hgf : ∀ k, ∃ i, g k ≤ f i) :
    ⨆ i, f i = ⨆ k, g k := by
  rw [iSup, iSup]
  apply sSup_eq_sSup_of_isCofinalFor
  · rintro _ ⟨i, rfl⟩
    obtain ⟨k, hik⟩ := hfg i
    exact ⟨g k, ⟨k, rfl⟩, hik⟩
  · rintro _ ⟨k, rfl⟩
    obtain ⟨i, hki⟩ := hgf k
    exact ⟨f i, ⟨i, rfl⟩, hki⟩

/-- Two indexed infima are equal when their families are mutually coinitial. -/
theorem iInf_eq_iInf_of_forall_exists_le
    {α : Type*} {ι κ : Sort*} [CompleteSemilatticeInf α] {f : ι → α} {g : κ → α}
    (hfg : ∀ i, ∃ k, g k ≤ f i) (hgf : ∀ k, ∃ i, f i ≤ g k) :
    ⨅ i, f i = ⨅ k, g k := by
  rw [iInf, iInf]
  apply sInf_eq_sInf_of_isCoinitialFor
  · rintro _ ⟨i, rfl⟩
    obtain ⟨k, hki⟩ := hfg i
    exact ⟨g k, ⟨k, rfl⟩, hki⟩
  · rintro _ ⟨k, rfl⟩
    obtain ⟨i, hik⟩ := hgf k
    exact ⟨f i, ⟨i, rfl⟩, hik⟩

/-! ## Replacement proofs in `Mathlib.Topology.Order.MonotoneConvergence` -/

/-- Replacement proof for `iSup_eq_iSup_subseq_of_monotone`. -/
example {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atTop) : ⨆ i, f i = ⨆ i, f (φ i) :=
  iSup_eq_iSup_of_forall_exists_le
    (fun i ↦ Exists.imp (fun _ hij ↦ hf hij)
      (hφ.eventually <| eventually_ge_atTop i).exists)
    (fun i ↦ ⟨φ i, le_rfl⟩)

/-- Replacement proof for `iSup_eq_iSup_subseq_of_antitone`. -/
example {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atBot) : ⨆ i, f i = ⨆ i, f (φ i) :=
  iSup_eq_iSup_of_forall_exists_le
    (fun i ↦ Exists.imp (fun _ hji ↦ hf hji)
      (hφ.eventually <| eventually_le_atBot i).exists)
    (fun i ↦ ⟨φ i, le_rfl⟩)
