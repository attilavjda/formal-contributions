import Mathlib

/-!
# Reuse candidates from analysis and linear algebra

This file machine-checks a generic iteration lemma suggested by duplicated
inductive proofs for iterated derivatives of trigonometric and hyperbolic
functions.  Its hypotheses express the familiar linear-algebra pattern that a
vector is an eigenvector of an operator.
-/

namespace Function

/-
If `x` is scaled by `c` under `f`, and `f` commutes with scaling by `c`,
then the `n`-th iterate scales `x` by `c ^ n`.
-/
theorem Commute.iterate_apply_eq_pow_smul
    {R α : Type*} [Monoid R] [MulAction R α]
    {f : α → α} {c : R} {x : α}
    (hcomm : Function.Commute f (c • ·)) (hx : f x = c • x) (n : ℕ) :
    f^[n] x = c ^ n • x := by
  have hiter : f^[n] x = (fun x => c • x)^[n] x := by
    exact Commute.iterate_eq_of_map_eq hcomm n hx
  exact hiter.trans (smul_iterate_apply c n x)

end Function

/-- If the second derivative of `f` is a scalar multiple of `f`, then every
`2 * n`-th derivative is the corresponding power multiple. -/
theorem iteratedDeriv_two_mul_of_two_eq_smul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (f : 𝕜 → 𝕜) (c : 𝕜)
    (h : iteratedDeriv 2 f = c • f) (n : ℕ) :
    iteratedDeriv (2 * n) f = c ^ n • f := by
  rw [iteratedDeriv_eq_iterate, Function.iterate_mul]
  apply Function.Commute.iterate_apply_eq_pow_smul (c := c)
  · intro g
    ext x
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    rw [show deriv (c • g) = c • deriv g by
      ext y
      exact deriv_const_smul_field c g]
    exact deriv_const_smul_field c (deriv g)
  · simpa [Function.iterate_succ_apply, iteratedDeriv_eq_iterate] using h

namespace ReuseExamples

/-- A non-inductive replacement for the proof of `Real.iteratedDeriv_even_sin`. -/
theorem real_iteratedDeriv_even_sin_example (n : ℕ) :
    iteratedDeriv (2 * n) Real.sin = (-1) ^ n * Real.sin := by
  simpa only [Pi.smul_apply, smul_eq_mul] using iteratedDeriv_two_mul_of_two_eq_smul
    Real.sin (-1 : ℝ) (by
      rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one,
        Real.deriv_sin]
      ext x
      rw [Real.deriv_cos]
      simp) n

/-- A non-inductive replacement for the proof of `Real.iteratedDeriv_even_cos`. -/
theorem real_iteratedDeriv_even_cos_example (n : ℕ) :
    iteratedDeriv (2 * n) Real.cos = (-1) ^ n * Real.cos := by
  simpa only [Pi.smul_apply, smul_eq_mul] using iteratedDeriv_two_mul_of_two_eq_smul
    Real.cos (-1 : ℝ) (by
      rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
      rw [show deriv Real.cos = -Real.sin by ext x; exact Real.deriv_cos, deriv.neg']
      ext x
      simp) n

/-- A non-inductive replacement for the proof of `Real.iteratedDeriv_even_sinh`. -/
theorem real_iteratedDeriv_even_sinh_example (n : ℕ) :
    iteratedDeriv (2 * n) Real.sinh = Real.sinh := by
  simpa only [Pi.smul_apply, smul_eq_mul, one_pow, one_mul, one_smul] using
    iteratedDeriv_two_mul_of_two_eq_smul Real.sinh (1 : ℝ)
    (by rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one,
      Real.deriv_sinh, Real.deriv_cosh, one_smul]) n

end ReuseExamples