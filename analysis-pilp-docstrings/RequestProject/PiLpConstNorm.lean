/-
Formal verification of the mathematical claims made in the `PiLp` docstrings that the
proposed Mathlib patch (`mathlib-pilp-docstring-fix.patch`) touches.

`Mathlib/Analysis/Normed/Lp/PiLp.lean` contains four lemmas computing the (nn)norm of a
constant vector in `PiLp p (fun _ : ι => β)`:

* `PiLp.nnnorm_toLp_const` and `PiLp.norm_toLp_const`, under the hypothesis `p ≠ ∞`;
* `PiLp.nnnorm_toLp_const'` and `PiLp.norm_toLp_const'`, under the hypothesis `[Nonempty ι]`.

Their docstrings assert two things, which are checked here:

* the hypotheses cannot simply be dropped
  (`PiLp.nnnorm_toLp_const_of_forall_false`, `PiLp.norm_toLp_const_of_forall_false`);
* the reason is that in the degenerate case `p = ∞` with `ι` empty the left-hand side
  collapses to `0` while the right-hand side collapses to `‖b‖₊`
  (`PiLp.nnnorm_toLp_const_top_of_isEmpty`, `PiLp.const_rhs_top_of_isEmpty`).

We also record that the two hypotheses are exactly complementary: their disjunction
`p ≠ ∞ ∨ Nonempty ι` suffices (`PiLp.nnnorm_toLp_const_of_ne_top_or_nonempty` and its `norm`
counterpart), and, up to the degenerate case `‖b‖₊ = 0`, is also necessary
(`PiLp.nnnorm_toLp_const_iff`).
-/
import Mathlib.Analysis.Normed.Lp.PiLp

open scoped ENNReal NNReal

namespace PiLp

section Merged

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] {β : Type*}
  [SeminormedAddCommGroup β]

/-- Common generalisation of `PiLp.nnnorm_toLp_const` (which assumes `p ≠ ∞`) and
`PiLp.nnnorm_toLp_const'` (which assumes `[Nonempty ι]`): only the disjunction of the two
hypotheses is needed. -/
theorem nnnorm_toLp_const_of_ne_top_or_nonempty (h : p ≠ ∞ ∨ Nonempty ι) (b : β) :
    ‖WithLp.toLp p (Function.const ι b)‖₊
      = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖₊ := by
  rcases h with hp | hι
  · exact nnnorm_toLp_const hp b
  · exact nnnorm_toLp_const' b

/-- Common generalisation of `PiLp.norm_toLp_const` (which assumes `p ≠ ∞`) and
`PiLp.norm_toLp_const'` (which assumes `[Nonempty ι]`): only the disjunction of the two
hypotheses is needed. -/
theorem norm_toLp_const_of_ne_top_or_nonempty (h : p ≠ ∞ ∨ Nonempty ι) (b : β) :
    ‖WithLp.toLp p (Function.const ι b)‖
      = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖ := by
  rcases h with hp | hι
  · exact norm_toLp_const hp b
  · exact norm_toLp_const' b

end Merged

section Degenerate

variable {ι : Type*} [Fintype ι] [IsEmpty ι] {β : Type*} [SeminormedAddCommGroup β]

/-- The docstrings' first claim about the degenerate case: when `p = ∞` and `ι` is empty, the
left-hand side of the constant-vector norm formula simplifies to `0`. -/
theorem nnnorm_toLp_const_top_of_isEmpty (b : β) :
    ‖(WithLp.toLp ∞ (Function.const ι b) : PiLp ∞ fun _ : ι => β)‖₊ = 0 := by
  rw [PiLp.nnnorm_eq_ciSup]
  simp

/-- The docstrings' second claim about the degenerate case: when `p = ∞` and `ι` is empty, the
right-hand side of the constant-vector norm formula simplifies to `‖b‖₊` (note that the
exponent `(1 / ∞).toReal` is `0`, so the vanishing factor `Fintype.card ι = 0` is raised to the
power `0` and contributes `1`). -/
theorem const_rhs_top_of_isEmpty (b : β) :
    ((Fintype.card ι : ℝ≥0) ^ (1 / (∞ : ℝ≥0∞)).toReal * ‖b‖₊) = ‖b‖₊ := by
  simp

end Degenerate

section Necessity

/-- The hypotheses of `PiLp.nnnorm_toLp_const` and `PiLp.nnnorm_toLp_const'` really are needed:
the formula for the norm of a constant vector is false in general.  The witness is the
degenerate case `p = ∞`, `ι = Fin 0`, `b = (1 : ℝ)`, where the two sides are `0` and `1`. -/
theorem nnnorm_toLp_const_of_forall_false :
    ¬ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (ι : Type) [Fintype ι] (β : Type)
        [SeminormedAddCommGroup β] (b : β),
      ‖WithLp.toLp p (Function.const ι b)‖₊
        = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖₊ := by
  intro h
  have h₀ := h ∞ (Fin 0) ℝ 1
  rw [PiLp.nnnorm_eq_ciSup] at h₀
  simp at h₀

/-- The `norm` counterpart of `PiLp.nnnorm_toLp_const_of_forall_false`. -/
theorem norm_toLp_const_of_forall_false :
    ¬ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (ι : Type) [Fintype ι] (β : Type)
        [SeminormedAddCommGroup β] (b : β),
      ‖WithLp.toLp p (Function.const ι b)‖
        = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖ := by
  intro h
  have h₀ := h ∞ (Fin 0) ℝ 1
  rw [PiLp.norm_eq_ciSup] at h₀
  simp at h₀

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] {β : Type*}
  [SeminormedAddCommGroup β]

/-- Exact characterisation: the constant-vector norm formula holds precisely when one of the
two hypotheses used in Mathlib is satisfied, or the degenerate situation `‖b‖₊ = 0` occurs. -/
theorem nnnorm_toLp_const_iff (b : β) :
    ‖WithLp.toLp p (Function.const ι b)‖₊
        = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖₊
      ↔ p ≠ ∞ ∨ Nonempty ι ∨ ‖b‖₊ = 0 := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨hp, hι, hb⟩ := hcon
    subst hp
    haveI : IsEmpty ι := hι
    rw [nnnorm_toLp_const_top_of_isEmpty, const_rhs_top_of_isEmpty] at h
    exact hb h.symm
  · rintro (hp | hι | hb)
    · exact nnnorm_toLp_const hp b
    · exact nnnorm_toLp_const' b
    · rcases eq_or_ne p ∞ with rfl | hp
      · rcases isEmpty_or_nonempty ι with hι | hι
        · rw [nnnorm_toLp_const_top_of_isEmpty, const_rhs_top_of_isEmpty, hb]
        · exact nnnorm_toLp_const' b
      · exact nnnorm_toLp_const hp b

end Necessity

end PiLp
