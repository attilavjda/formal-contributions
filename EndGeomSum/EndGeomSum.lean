module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Ring.GeomSum

public section

/-!
# Geometric sums of additive endomorphisms

This file gives pointwise versions of geometric-series identities for 
additive endomorphisms. It is separate from `Mathlib.Algebra.Group.Hom.End`
to avoid adding a dependency on geometric sums.
-/

namespace AddMonoidHom

open Finset

variable {ι A B : Type*} [AddMonoid A] [AddCommMonoid B]

/-- Evaluation of a finite sum of additive homomorphisms is the finite sum of
their evaluations. This is the additive-hom analogue of `LinearMap.sum_apply`. -/
theorem sum_apply (s : Finset ι) (f : ι → A →+ B) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x :=
  _root_.map_sum (AddMonoidHom.eval x) f s

end AddMonoidHom

namespace AddMonoid.End

open Finset

variable {A : Type*} [AddCommGroup A]

/-- Evaluate `mul_geom_sum` at an element. -/
theorem apply_mul_geom_sum (φ : AddMonoid.End A) (n : ℕ) (x : A) :
    (φ - 1) (∑ i ∈ range n, (φ ^ i) x) = (φ ^ n - 1) x := by
  have h := congrArg (fun g : AddMonoid.End A ↦ g x) (mul_geom_sum φ n)
  change (φ - 1) ((∑ i ∈ range n, φ ^ i) x) = (φ ^ n - 1) x at h
  rw [AddMonoidHom.sum_apply (range n) (fun i ↦ φ ^ i) x] at h
  exact h

/-- Pointwise telescoping for a geometric sum of additive endomorphisms. -/
theorem apply_sum_pow_sub (φ : AddMonoid.End A) (n : ℕ) (x : A) :
    φ (∑ i ∈ range n, (φ ^ i) x) - ∑ i ∈ range n, (φ ^ i) x =
      (φ ^ n) x - x := by
  simpa only [AddMonoidHom.sub_apply] using apply_mul_geom_sum φ n x

/-- A geometric orbit sum is fixed if the corresponding power of the
endomorphism is the identity. -/
theorem apply_sum_pow_eq_self {n : ℕ} (φ : AddMonoid.End A) (hφ : φ ^ n = 1)
    (x : A) : φ (∑ i ∈ range n, (φ ^ i) x) = ∑ i ∈ range n, (φ ^ i) x := by
  rw [← sub_eq_zero, apply_sum_pow_sub, hφ]
  simp

end AddMonoid.End
