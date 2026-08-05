import Mathlib
import RequestProject.CiSupDiagonalPR2

/-!
# Which Mathlib callers does the `ciSup` diagonal lemma shorten?

This file is the machine-checked half of the caller survey for

```
Cardinal.ciSup₂_add_eq_ciSup_diagonal
  (g : ι → Cardinal) (hf : BddAbove (range fun k ↦ f k + g k))
  (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
  ⨆ i, ⨆ j, (f i + g j) = ⨆ k, (f k + g k)
```

and of its generic parent `ciSup₂_eq_ciSup_diagonal` (proved in
`RequestProject/CiSupDiagonalPR2.lean`, reused here rather than restated).
The prose half — the grep commands, the hit lists and the line counts — is in
`CISUP_DIAGONAL_CALLERS.md`.

Summary of what is checked below.

* **§1** The `Cardinal` add-form is a one-line corollary of the generic lemma, and so is the
  multiplicative form. Neither has a call site in the current Mathlib: a grep over `Mathlib/`
  finds no proof that collapses a doubly indexed supremum *of cardinals* onto its diagonal.
* **§2** The three in-tree proofs that *do* perform exactly this collapse are
  `ENNReal.iSup_add_iSup`, `ENat.iSup_add_iSup` and `ENNReal.iInf_add_iInf`. They are re-proved
  here through the conditionally complete lemma (the `BddAbove` hypothesis is discharged by
  `OrderTop.bddAbove`, and the `iInf` one by the order-dual form), and each replacement is
  checked with `rfl` against the current Mathlib statement.
* **§3** The three call sites of `Cardinal.ciSup_add_ciSup` in Mathlib
  (`rank_add_rank_le_rank_prod`, `rank_quotient_add_rank_le`, `lift_trdeg_add_le`) are **not**
  shortened by the diagonal lemma: they bound a double supremum, they do not collapse it. What
  they share is a different weakest generic statement, `Cardinal.ciSup_add_ciSup_le`, given here
  with all three callers rewritten through it and `rfl`-checked against Mathlib.
-/

open Set Cardinal Module Submodule
open scoped ENNReal

namespace CiSupCallers

/-! ## §1 The `Cardinal` specialisations, and the absence of callers for them -/

/-- The statement under discussion, proved from the generic conditionally complete lemma.
`Cardinal` is a `ConditionallyCompleteLinearOrderBot`, so the complete-lattice diagonal lemma
does not apply to it; the conditionally complete one does. -/
protected theorem Cardinal.ciSup₂_add_eq_ciSup_diagonal {ι : Type*} (f g : ι → Cardinal.{v})
    (hf : BddAbove (range fun k ↦ f k + g k)) (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    ⨆ i, ⨆ j, (f i + g j) = ⨆ k, (f k + g k) :=
  CiSupDiagonal.ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j) hf h

/-- The multiplicative twin comes out of the same generic lemma at no extra cost; it is the
companion of `Cardinal.ciSup_mul_ciSup` the way the additive one is of
`Cardinal.ciSup_add_ciSup`. It, too, has no call site in the current Mathlib. -/
protected theorem Cardinal.ciSup₂_mul_eq_ciSup_diagonal {ι : Type*} (f g : ι → Cardinal.{v})
    (hf : BddAbove (range fun k ↦ f k * g k)) (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) :
    ⨆ i, ⨆ j, (f i * g j) = ⨆ k, (f k * g k) :=
  CiSupDiagonal.ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i * g j) hf h

/-- Chained with `Cardinal.ciSup_add_ciSup`, the add-form gives the `Cardinal` analogue of
`ENNReal.iSup_add_iSup` / `ENat.iSup_add_iSup`. This is the shape a future caller would use, and
it is the only reason for the add-specialisation to exist as a separate declaration. -/
protected theorem Cardinal.ciSup_add_ciSup_diagonal {ι : Type*} [Nonempty ι]
    (f g : ι → Cardinal.{v}) (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (hfg : BddAbove (range fun k ↦ f k + g k)) (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, (f k + g k) := by
  rw [Cardinal.ciSup_add_ciSup f hf g hg]
  exact CiSupCallers.Cardinal.ciSup₂_add_eq_ciSup_diagonal f g hfg h

/-- A monotone pair over a directed index type meets the cofinality hypothesis, which is how such
a caller would discharge it. -/
example (f g : ℕ → Cardinal.{v}) (hf : Monotone f) (hg : Monotone g) (i j : ℕ) :
    ∃ k, f i + g j ≤ f k + g k :=
  ⟨max i j, add_le_add (hf (le_max_left i j)) (hg (le_max_right i j))⟩

/-! ## §2 The in-tree proofs that the diagonal collapse does shorten

`ℝ≥0∞` and `ℕ∞` are complete lattices, hence conditionally complete ones, and every family in
them is bounded above by `⊤`; so the conditionally complete diagonal lemma applies verbatim and
the three duplicated proofs below become the same two lines. -/

section CompleteExamples

/-- The order-dual of the diagonal lemma, needed for the `iInf` caller. -/
theorem ciInf₂_eq_ciInf_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (hf : BddBelow (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f k k ≤ f i j) :
    ⨅ i, ⨅ j, f i j = ⨅ k, f k k :=
  CiSupDiagonal.ciSup₂_eq_ciSup_diagonal (α := αᵒᵈ) f hf h

/-- Caller 1: `Mathlib/Data/ENNReal/Operations.lean`, `ENNReal.iSup_add_iSup`. -/
theorem ENNReal.iSup_add_iSup {ι : Sort*} {f g : ι → ℝ≥0∞}
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  rw [show iSup f + iSup g = ⨆ i, ⨆ j, (f i + g j) by
    simp_rw [ENNReal.iSup_add, ENNReal.add_iSup]]
  exact CiSupDiagonal.ciSup₂_eq_ciSup_diagonal _ (OrderTop.bddAbove _) h

/-- Caller 2: `Mathlib/Data/ENat/Lattice.lean`, `ENat.iSup_add_iSup`. -/
theorem ENat.iSup_add_iSup {ι : Sort*} {f g : ι → ℕ∞}
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  rw [show iSup f + iSup g = ⨆ i, ⨆ j, (f i + g j) by
    simp_rw [ENat.iSup_add, ENat.add_iSup]]
  exact CiSupDiagonal.ciSup₂_eq_ciSup_diagonal _ (OrderTop.bddAbove _) h

/-- Caller 3: `Mathlib/Data/ENNReal/Operations.lean`, `ENNReal.iInf_add_iInf`, through the dual.
No case split on emptiness is needed here, because `ENNReal.iInf_add` and `ENNReal.add_iInf`
hold for an empty index type. -/
theorem ENNReal.iInf_add_iInf {ι : Sort*} {f g : ι → ℝ≥0∞}
    (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a := by
  rw [show iInf f + iInf g = ⨅ i, ⨅ j, (f i + g j) by
    simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]]
  exact ciInf₂_eq_ciInf_diagonal _ (OrderBot.bddBelow _) h

/-- The three replacements prove exactly the statements Mathlib has today. -/
example : @CiSupCallers.ENNReal.iSup_add_iSup = @_root_.ENNReal.iSup_add_iSup := rfl

example : @CiSupCallers.ENat.iSup_add_iSup = @_root_.ENat.iSup_add_iSup := rfl

example : @CiSupCallers.ENNReal.iInf_add_iInf = @_root_.ENNReal.iInf_add_iInf := rfl

end CompleteExamples

/-! ## §3 The three `Cardinal.ciSup_add_ciSup` call sites want a different lemma

`rank_add_rank_le_rank_prod`, `rank_quotient_add_rank_le` and `lift_trdeg_add_le` all open with

```
rw [Cardinal.ciSup_add_ciSup _ (bddAbove_range _) _ (bddAbove_range _)]
refine ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦ ?_
```

i.e. they *bound* the double supremum rather than collapsing it onto a diagonal, and the two
families are indexed by different types, so no diagonal exists. The weakest statement they share
is the `le` form below. It is the additive analogue of `ENNReal.iSup_add_iSup_le`; the existing
generic `ciSup_add_ciSup_le` in `Mathlib/Order/ConditionallyCompleteLattice/Group.lean` cannot be
used, since it assumes `Group α` and `Cardinal` is not one. -/

section LeForm

/-- `Cardinal` analogue of `ENNReal.iSup_add_iSup_le`. -/
protected theorem Cardinal.ciSup_add_ciSup_le {ι ι' : Type*} [Nonempty ι] [Nonempty ι']
    {f : ι → Cardinal.{v}} {g : ι' → Cardinal.{v}} {c : Cardinal.{v}}
    (hf : BddAbove (range f)) (hg : BddAbove (range g)) (H : ∀ i j, f i + g j ≤ c) :
    (⨆ i, f i) + (⨆ j, g j) ≤ c := by
  rw [Cardinal.ciSup_add_ciSup f hf g hg]
  exact ciSup_le fun i ↦ ciSup_le (H i)

section Dimension

variable (R : Type u) (M : Type v) {M₁ : Type v} [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁]
  [Module R M] [Module R M₁]

/-- `Mathlib/LinearAlgebra/Dimension/Constructions.lean`, `rank_add_rank_le_rank_prod`. -/
theorem rank_add_rank_le_rank_prod [Nontrivial R] :
    Module.rank R M + Module.rank R M₁ ≤ Module.rank R (M × M₁) := by
  conv_lhs => simp only [Module.rank_def]
  exact Cardinal.ciSup_add_ciSup_le (bddAbove_range _) (bddAbove_range _)
    fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ (linearIndependent_inl_union_inr' hs ht).cardinal_le_rank

example : @CiSupCallers.rank_add_rank_le_rank_prod = @_root_.rank_add_rank_le_rank_prod := rfl

end Dimension

section Quotient

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- `Mathlib/LinearAlgebra/Dimension/Constructions.lean`, `rank_quotient_add_rank_le`. -/
theorem rank_quotient_add_rank_le [Nontrivial R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' ≤ Module.rank R M := by
  conv_lhs => simp only [Module.rank_def]
  choose f hf using Submodule.Quotient.mk_surjective M'
  exact Cardinal.ciSup_add_ciSup_le (bddAbove_range _) (bddAbove_range _)
    fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ by
      simpa [add_comm] using (LinearIndependent.sumElim_of_quotient ht (fun (i : s) ↦ f i)
        (by simpa [Function.comp_def, hf] using hs)).cardinal_le_rank

example : @CiSupCallers.rank_quotient_add_rank_le = @_root_.rank_quotient_add_rank_le := rfl

end Quotient

section Trdeg

variable {R : Type*} {S : Type u} {A : Type v} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- `Mathlib/RingTheory/AlgebraicIndependent/Transcendental.lean`, `lift_trdeg_add_le`. -/
theorem lift_trdeg_add_le [Nontrivial R] [FaithfulSMul R S] [FaithfulSMul S A] :
    lift.{v} (Algebra.trdeg R S) + lift.{u} (Algebra.trdeg S A) ≤ lift.{u} (Algebra.trdeg R A) := by
  simp_rw [Algebra.trdeg, lift_iSup (bddAbove_range _)]
  refine Cardinal.ciSup_add_ciSup_le (bddAbove_range _) (bddAbove_range _) fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ ?_
  rw [add_comm, ← mk_sum]
  have := hs.sumElim_comp ht
  refine le_ciSup_of_le (bddAbove_range _) ⟨_, this.to_subtype_range⟩ ?_
  rw [← lift_umax, mk_range_eq_of_injective this.injective, lift_id']

example : @CiSupCallers.lift_trdeg_add_le = @_root_.lift_trdeg_add_le := rfl

end Trdeg

end LeForm

end CiSupCallers
