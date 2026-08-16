/-
Machine-checked support for the follow-up part of the proposed Mathlib contribution
described in `CONTRIBUTION.md` (patch: `contribution/to_additive-env-generated.patch`).

The scan documented in `scripts/README.md` found further pairs of Mathlib theorems where
the additive member is written out by hand even though `@[to_additive]` on the
multiplicative member would generate exactly it.  For each pair below we copy the
multiplicative lemma verbatim (same statement, same proof), tag it `@[to_additive]`, and
check that the generated additive lemma has *literally* the type of the hand-written
Mathlib declaration: the `rfl` in `@Generated = @Mathlib.Name` would not even typecheck
otherwise.  Hence the hand-written additive declarations can be deleted with no change to
the public API.
-/
import Mathlib

namespace KalkulusContributionEnv

/-! ### `Mathlib/Algebra/BigOperators/Expect.lean` -/

open Finset in
open scoped BigOperators Pointwise in
/-- Copy of `Finset.expect_inv_index`, tagged `@[to_additive]`. -/
@[to_additive]
theorem expect_inv_index' {ι M : Type*} [AddCommMonoid M] [Module NNRat M] [DecidableEq ι]
    [InvolutiveInv ι] (s : Finset ι) (f : ι → M) :
    𝔼 i ∈ s⁻¹, f i = 𝔼 i ∈ s, f i⁻¹ := expect_image inv_injective.injOn

theorem expect_neg_index_statements_agree :
    @expect_neg_index' = @Finset.expect_neg_index := rfl

/-! ### `Mathlib/Algebra/Group/Translate.lean` -/

open scoped translate in
/-- Copy of `translate_prod_right`, tagged `@[to_additive]`. -/
@[to_additive]
theorem translate_prod_right' {ι M G : Type*} [AddCommGroup G] [CommMonoid M]
    (a : G) (f : ι → G → M) (s : Finset ι) :
    τ a (∏ i ∈ s, f i) = ∏ i ∈ s, τ a (f i) := by ext; simp

theorem translate_sum_right_statements_agree :
    @translate_sum_right' = @translate_sum_right := rfl

/-! ### `Mathlib/Algebra/Group/Action/End.lean` -/

/-- Copy of `MulAction.toPerm_one`, tagged `@[to_additive]`. -/
@[to_additive]
theorem toPerm_one' (G α : Type*) [Group G] [MulAction G α] :
    (MulAction.toPerm (1 : G)) = (1 : Equiv.Perm α) := by
  aesop

theorem toPerm_zero_statements_agree :
    @toPerm_zero' = @AddAction.toPerm_zero := rfl

/-! ### `Mathlib/Tactic/LinearCombination'.lean` -/

section LinearCombination

variable {α : Type*} {a a' a₁ a₂ b b' b₁ b₂ c : α}

/-- Copy of `Mathlib.Tactic.LinearCombination'.pf_mul_c`, tagged `@[to_additive]`. -/
@[to_additive]
theorem pf_mul_c' [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl

/-- Copy of `Mathlib.Tactic.LinearCombination'.c_mul_pf`, tagged `@[to_additive]`. -/
@[to_additive]
theorem c_mul_pf' [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl

/-- Copy of `Mathlib.Tactic.LinearCombination'.mul_pf`, tagged `@[to_additive]`. -/
@[to_additive]
theorem mul_pf' [Mul α] (p₁ : (a₁ : α) = b₁) (p₂ : a₂ = b₂) : a₁ * a₂ = b₁ * b₂ := p₁ ▸ p₂ ▸ rfl

/-- Copy of `Mathlib.Tactic.LinearCombination'.pf_div_c`, tagged `@[to_additive]`. -/
@[to_additive]
theorem pf_div_c' [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl

/-- Copy of `Mathlib.Tactic.LinearCombination'.c_div_pf`, tagged `@[to_additive]`. -/
@[to_additive]
theorem c_div_pf' [Div α] (p : b = c) (a : α) : a / b = a / c := p ▸ rfl

/-- Copy of `Mathlib.Tactic.LinearCombination'.div_pf`, tagged `@[to_additive]`. -/
@[to_additive]
theorem div_pf' [Div α] (p₁ : (a₁ : α) = b₁) (p₂ : a₂ = b₂) : a₁ / a₂ = b₁ / b₂ := p₁ ▸ p₂ ▸ rfl

/-- Copy of `Mathlib.Tactic.LinearCombination'.inv_pf`, tagged `@[to_additive]`. -/
@[to_additive]
theorem inv_pf' [Inv α] (p : (a : α) = b) : a⁻¹ = b⁻¹ := p ▸ rfl

end LinearCombination

open Mathlib.Tactic.LinearCombination' in
theorem linearCombination_statements_agree :
    (@pf_add_c' = @pf_add_c) ∧ (@c_add_pf' = @c_add_pf) ∧ (@add_pf' = @add_pf) ∧
      (@pf_sub_c' = @pf_sub_c) ∧ (@c_sub_pf' = @c_sub_pf) ∧ (@sub_pf' = @sub_pf) ∧
      (@neg_pf' = @neg_pf) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end KalkulusContributionEnv
