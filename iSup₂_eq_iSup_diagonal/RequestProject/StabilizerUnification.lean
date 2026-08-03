import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# A generic criterion for identifying a set stabilizer

This file explores the TODO preceding `MulAction.stabilizer_subgroup` in
`Mathlib.Algebra.Pointwise.Stabilizer`. The criterion below isolates the common argument: one point
detects membership in the candidate subgroup, while every member of that subgroup maps the set
into itself. Since the candidate is a subgroup, closure under inverses upgrades the one-sided
inclusion to stabilization.
-/

open Set
open scoped Pointwise

namespace MulAction

variable {G α : Type*} [Group G] [MulAction G α]

/-- Identify a set stabilizer from a point that detects membership in a candidate subgroup and
one-sided invariance under that subgroup. -/
@[to_additive]
lemma stabilizer_eq_of_smul_mem_iff (s : Set α) (H : Subgroup G) (b : α)
    (hmem : ∀ a : G, a • b ∈ s ↔ a ∈ H)
    (hsmul : ∀ a : G, a ∈ H → ∀ x : α, x ∈ s → a • x ∈ s) :
    stabilizer G s = H := by
  rw [SetLike.ext_iff]
  intro a
  rw [mem_stabilizer_set]
  constructor
  · intro h
    apply (hmem a).mp
    apply (h b).mpr
    simpa using (hmem 1).mpr H.one_mem
  · intro ha x
    constructor
    · intro hax
      have h := hsmul a⁻¹ (H.inv_mem ha) (a • x) hax
      simpa using h
    · exact hsmul a ha x

section Subgroup

/-- The first existing lemma becomes an application of the generic criterion. -/
lemma stabilizer_subgroup_via_smul_mem_iff (s : Subgroup G) : stabilizer G (s : Set G) = s := by
  apply stabilizer_eq_of_smul_mem_iff (s : Set G) s 1
  · simp [smul_eq_mul]
  · intro a ha x hx
    exact s.mul_mem ha hx

/-- The second existing lemma becomes an application of the same criterion. -/
lemma stabilizer_op_subgroup_via_smul_mem_iff (s : Subgroup G) :
    stabilizer Gᵐᵒᵖ (s : Set G) = s.op := by
  apply stabilizer_eq_of_smul_mem_iff (s : Set G) s.op 1
  · simp
  · intro a ha x hx
    exact s.mul_mem hx ha

/-- The third existing lemma becomes an application of the same criterion. -/
lemma stabilizer_subgroup_op_via_smul_mem_iff (s : Subgroup Gᵐᵒᵖ) :
    stabilizer G (s : Set Gᵐᵒᵖ) = s.unop := by
  apply stabilizer_eq_of_smul_mem_iff (s : Set Gᵐᵒᵖ) s.unop 1
  · intro a
    change MulOpposite.op (a * 1) ∈ s ↔ MulOpposite.op a ∈ s
    simp
  · intro a ha x hx
    exact s.mul_mem hx ha

end Subgroup

end MulAction
