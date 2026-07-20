import MathlibExtras.FieldTheory.Finite.FrobeniusPeriod

/-!
# Examples for finite-field Frobenius period reduction

These examples demonstrate the endomorphism-level and pointwise APIs, including
an explicit reverse rewrite.
-/

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K]
variable {p n : ℕ} [Fact p.Prime] [CharP K p]

example (hcard : Fintype.card K = p ^ n) (m : ℕ) :
    frobenius K p ^ (m + n) = frobenius K p ^ ((m + n) % n) := by
  rw [frobenius_pow_eq_pow_mod hcard]

example (hcard : Fintype.card K = p ^ n) (m : ℕ) (x : K) :
    iterateFrobenius K p (m + n) x =
      iterateFrobenius K p ((m + n) % n) x := by
  rw [iterateFrobenius_mod_apply hcard]

example (hcard : Fintype.card K = p ^ n) (m : ℕ) (x : K) :
    iterateFrobenius K p (m % n) x = iterateFrobenius K p m x :=
  (iterateFrobenius_mod_apply hcard m x).symm

end FiniteField
