import Mathlib.FieldTheory.Finite.Basic

/-!
# Periodicity of Frobenius in a finite field

A small companion API intended to sit immediately after
`FiniteField.frobenius_pow`. It packages the common next step: reduce an
arbitrary Frobenius iterate modulo the extension degree. Both the endomorphism
equality and pointwise rewrite are provided for their distinct use cases; no
positivity hypothesis on the extension degree is needed.
-/

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K]
variable {p n : ℕ} [Fact p.Prime] [CharP K p]

/-- In a field of cardinality `p ^ n`, powers of Frobenius may be reduced
modulo `n`. -/
theorem frobenius_pow_eq_pow_mod (hcard : Fintype.card K = p ^ n) (m : ℕ) :
    frobenius K p ^ m = frobenius K p ^ (m % n) :=
  pow_eq_pow_mod m (FiniteField.frobenius_pow hcard)

/-- Pointwise form of `FiniteField.frobenius_pow_eq_pow_mod`. -/
theorem iterateFrobenius_mod_apply (hcard : Fintype.card K = p ^ n) (m : ℕ) (x : K) :
    iterateFrobenius K p m x = iterateFrobenius K p (m % n) x := by
  rw [iterateFrobenius_eq_pow, iterateFrobenius_eq_pow,
    frobenius_pow_eq_pow_mod hcard m]

end FiniteField