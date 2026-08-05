import Mathlib

/-!
# Mathlib PR staging area

This file contains the code that `MATHLIB-PR-PLAN.md` proposes to upstream, written in
Mathlib style (statement shapes, naming, docstrings) and *self-contained*: it imports
only `Mathlib`, not the rest of this project, so each block can be copied into the
target Mathlib file with the enclosing `namespace MathlibPR` removed.

Everything is grouped by the PR it belongs to:

* **PR 1** — cofinality helpers (`Mathlib/Order/Bounds/Basic.lean`) and the diagonal
  collapse for complete lattices (`Mathlib/Order/CompleteLattice/Basic.lean`), plus the
  three call-site refactors (`ENNReal.iSup_add_iSup`, `ENNReal.iInf_add_iInf`,
  `ENat.iSup_add_iSup`).  The refactors appear as `example`s whose statements are
  checked to be *literally* the current Mathlib statements by the `rfl` tests that
  follow them (a proposition-valued `∀`-statement is a `Prop`, so `rfl` succeeds exactly
  when the two statements are definitionally equal).
* **PR 2** — the conditionally complete ("`c`") counterparts
  (`Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`) and the new `Cardinal`
  lemmas they buy (`Mathlib/SetTheory/Cardinal/Arithmetic.lean`).
* **PR 3** (optional) — the `of_monotone` corollaries and the operation-level packaging.

Nothing here is meant to be imported by the rest of the project; `RequestProject.Main`
compiles it only to keep it honest.
-/

namespace MathlibPR

open Set

/-! ## PR 1

### PR 1, part (a): `Mathlib/Order/Bounds/Basic.lean`

Two one-line lemmas about `IsCofinalFor`, next to `upperBounds_mono_of_isCofinalFor`.
They are what makes the cofinality argument usable for indexed families. -/

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

/-! ### PR 1, part (b): `Mathlib/Order/CompleteLattice/Basic.lean`

The abstraction behind `ENNReal.iSup_add_iSup`, `ENNReal.iInf_add_iInf` and
`ENat.iSup_add_iSup`: an iterated supremum collapses onto any cofinal family, in
particular onto its diagonal.  Suggested location: next to `iSup_prod` / `iSup_comm`. -/

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

/-! ### PR 1, part (c): the three call sites

The proposed replacement proofs, stated with exactly the current Mathlib signatures.
Each is followed by a `rfl` check against the existing declaration, which succeeds only
if the statement was not changed.

Note the residual `cases isEmpty_or_nonempty ι`: the distributivity lemmas
(`ENNReal.iSup_add`, `ENat.add_iSup`, …) need `[Nonempty ι]`, so the empty case cannot
be absorbed into the general lemma. -/

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

/-! Two multiplicative statements that Mathlib does not have yet, and that come for free
once the general lemma is in place.  They are optional additions to PR 1. -/

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

/-! ## PR 2

### PR 2, part (a): `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`

The conditionally complete counterparts.  Boundedness is the only extra ingredient, and
it enters exactly once, in the currying step `ciSup_prod`.  Suggested location: next to
`csSup_eq_csSup_of_forall_exists_le`. -/

section ConditionallyCompleteLattice

variable {α : Type*} {ι κ : Type*} [ConditionallyCompleteLattice α]

/-- Mutually cofinal bounded families have the same supremum.  (In a conditionally
complete *linear* order this holds with no hypotheses at all; see
`csSup_eq_csSup_of_forall_exists_le`.) -/
theorem ciSup_eq_ciSup_of_forall_exists_le [Nonempty ι] [Nonempty κ] {f : ι → α} {g : κ → α}
    (hf : BddAbove (range f)) (hg : BddAbove (range g)) (hfg : ∀ i, ∃ j, f i ≤ g j)
    (hgf : ∀ j, ∃ i, g j ≤ f i) : ⨆ i, f i = ⨆ j, g j :=
  le_antisymm (ciSup_le fun i => (hfg i).elim fun j hj => hj.trans (le_ciSup hg j))
    (ciSup_le fun j => (hgf j).elim fun i hi => hi.trans (le_ciSup hf i))

/-- A row of a family that is bounded on the product is bounded. -/
theorem bddAbove_range_curry {F : ι × κ → α} (hb : BddAbove (range F)) (i : ι) :
    BddAbove (range fun j => F (i, j)) :=
  hb.mono (range_subset_iff.2 fun j => mem_range_self (i, j))

/-- The row suprema of a family that is bounded on the product are bounded. -/
theorem bddAbove_range_ciSup_curry [Nonempty κ] {F : ι × κ → α} (hb : BddAbove (range F)) :
    BddAbove (range fun i => ⨆ j, F (i, j)) :=
  hb.imp fun _ hc => forall_mem_range.2 fun i => ciSup_le fun j => hc (mem_range_self (i, j))

/-- **Currying** for conditionally complete lattices: a doubly indexed supremum of a
bounded family is a supremum over the product index.  Conditionally complete counterpart
of `iSup_prod`. -/
theorem ciSup_prod [Nonempty ι] [Nonempty κ] {F : ι × κ → α} (hb : BddAbove (range F)) :
    ⨆ p : ι × κ, F p = ⨆ i, ⨆ j, F (i, j) :=
  le_antisymm
    (ciSup_le fun p => (le_ciSup (bddAbove_range_curry hb p.1) p.2).trans
      (le_ciSup (bddAbove_range_ciSup_curry hb) p.1))
    (ciSup_le fun i => ciSup_le fun j => le_ciSup hb (i, j))

/-- Under the diagonal hypothesis the square is cofinal in the diagonal, hence bounded as
soon as the diagonal is. -/
theorem bddAbove_range_uncurry {F : ι → ι → α} (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : BddAbove (range fun p : ι × ι => F p.1 p.2) :=
  IsCofinalFor.bddAbove (isCofinalFor_range_iff.2 fun p => h p.1 p.2) hb

/-- Conditionally complete counterpart of `iSup₂_eq_iSup_diagonal`: if every entry of a
square family is dominated by a diagonal entry and the diagonal is bounded above, then
the iterated supremum collapses onto the diagonal. -/
theorem ciSup₂_eq_ciSup_diagonal [Nonempty ι] (F : ι → ι → α) (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  (ciSup_prod (F := fun p : ι × ι => F p.1 p.2) (bddAbove_range_uncurry h hb)).symm.trans <|
    ciSup_eq_ciSup_of_forall_exists_le (bddAbove_range_uncurry h hb) hb
      (fun p => h p.1 p.2) fun k => ⟨(k, k), le_rfl⟩

/-- Conditionally complete counterpart of `iInf₂_eq_iInf_diagonal`. -/
theorem ciInf₂_eq_ciInf_diagonal [Nonempty ι] (F : ι → ι → α) (h : ∀ i j, ∃ k, F k k ≤ F i j)
    (hb : BddBelow (range fun k => F k k)) : ⨅ i, ⨅ j, F i j = ⨅ k, F k k :=
  ciSup₂_eq_ciSup_diagonal (α := αᵒᵈ) F h hb

end ConditionallyCompleteLattice

/-! ### PR 2, part (b): `Mathlib/SetTheory/Cardinal/Arithmetic.lean`

The lemmas that are actually being asked for: the `Cardinal` analogues of
`ENNReal.iSup_add_iSup` and of its multiplicative sibling.  Mathlib currently stops at
`Cardinal.ciSup_add_ciSup`, which produces the *double* supremum `⨆ i, ⨆ j, f i + g j`;
these collapse it onto the diagonal. -/

section Cardinal

universe u v

variable {ι : Type u} [Nonempty ι] {f g : ι → Cardinal.{v}}

/-- Sums of two bounded families are bounded. -/
theorem bddAbove_range_add {β : Type*} [Preorder β] [Add β]
    [CovariantClass β β (· + ·) (· ≤ ·)] [CovariantClass β β (Function.swap (· + ·)) (· ≤ ·)]
    {ι : Type*} {f g : ι → β} (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    BddAbove (range fun k => f k + g k) :=
  (hf.add hg).mono <| range_subset_iff.2 fun k =>
    Set.add_mem_add (mem_range_self k) (mem_range_self k)

omit [Nonempty ι] in
/-- Products of two bounded families of cardinals are bounded. -/
theorem bddAbove_range_mul (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    BddAbove (range fun k => f k * g k) :=
  hf.elim fun a ha => hg.elim fun b hb =>
    ⟨a * b, forall_mem_range.2 fun k =>
      mul_le_mul' (ha (mem_range_self k)) (hb (mem_range_self k))⟩

/-- Diagonal form of `Cardinal.ciSup_add_ciSup`: the conditionally complete counterpart of
`ENNReal.iSup_add_iSup`. -/
protected theorem Cardinal.ciSup_add_ciSup_diagonal (hf : BddAbove (range f))
    (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  (_root_.Cardinal.ciSup_add_ciSup f hf g hg).trans <|
    ciSup₂_eq_ciSup_diagonal _ h (bddAbove_range_add hf hg)

/-- Diagonal form of `Cardinal.ciSup_mul_ciSup`: the conditionally complete counterpart of
`ENNReal.iSup_mul_iSup`. -/
protected theorem Cardinal.ciSup_mul_ciSup_diagonal (hf : BddAbove (range f))
    (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) : (⨆ i, f i) * (⨆ j, g j) = ⨆ k, f k * g k :=
  (_root_.Cardinal.ciSup_mul_ciSup f g).trans <|
    ciSup₂_eq_ciSup_diagonal _ h (bddAbove_range_mul hf hg)

end Cardinal

/-! ## PR 3 (optional follow-up)

The `of_monotone` corollaries, mirroring `ENNReal.iSup_add_iSup_of_monotone`, and the
operation-level packaging that removes the `simp_rw [iSup_add, add_iSup]` step from call
sites. -/

section Monotone

universe u v

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {f g : ι → Cardinal.{v}}

/-- Over a directed index, monotone families satisfy the diagonal hypothesis
automatically. -/
protected theorem Cardinal.ciSup_add_ciSup_of_monotone (hf : BddAbove (range f))
    (hg : BddAbove (range g)) (hmf : Monotone f) (hmg : Monotone g) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  MathlibPR.Cardinal.ciSup_add_ciSup_diagonal hf hg fun i j =>
    (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ => add_le_add (hmf hi) (hmg hj)

/-- Over a directed index, monotone families satisfy the diagonal hypothesis
automatically. -/
protected theorem Cardinal.ciSup_mul_ciSup_of_monotone (hf : BddAbove (range f))
    (hg : BddAbove (range g)) (hmf : Monotone f) (hmg : Monotone g) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ k, f k * g k :=
  MathlibPR.Cardinal.ciSup_mul_ciSup_diagonal hf hg fun i j =>
    (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ => mul_le_mul' (hmf hi) (hmg hj)

end Monotone

section Packaging

variable {α : Type*} {ι : Sort*} [CompleteLattice α]

/-- Operation-level packaging: if `op` commutes with suprema in each argument, then `op`
of two suprema is the supremum of `op` along the diagonal.  This is what makes each call
site a single application, at the price of two extra hypotheses. -/
theorem iSup_op_iSup_diagonal {f g : ι → α} (op : α → α → α)
    (hl : ∀ (f : ι → α) (a : α), op (⨆ i, f i) a = ⨆ i, op (f i) a)
    (hr : ∀ (a : α) (g : ι → α), op a (⨆ j, g j) = ⨆ j, op a (g j))
    (h : ∀ i j, ∃ k, op (f i) (g j) ≤ op (f k) (g k)) :
    op (⨆ i, f i) (⨆ j, g j) = ⨆ k, op (f k) (g k) :=
  (hl f _).trans <| (iSup_congr fun i => hr (f i) g).trans <| iSup₂_eq_iSup_diagonal _ h

end Packaging

end MathlibPR
