# Exploring the stabilizer-subgroup unification TODO

The three lemmas at `Algebra/Pointwise/Stabilizer.lean:142` can be instances of one action-level
criterion. A useful formulation is:

```lean
@[to_additive]
lemma stabilizer_eq_of_smul_mem_iff (s : Set α) (H : Subgroup G) (b : α)
    (hmem : ∀ a : G, a • b ∈ s ↔ a ∈ H)
    (hsmul : ∀ a : G, a ∈ H → ∀ x : α, x ∈ s → a • x ∈ s) :
    stabilizer G s = H
```

This says:

1. one distinguished point `b` detects whether an acting element belongs to `H`; and
2. elements of `H` map `s` into itself.

The second condition is deliberately only one-sided. Because `H` is a subgroup, it also contains
`a⁻¹`; applying the same condition to `a⁻¹` gives the reverse membership implication needed for
stabilization. There is also no separate assumption `b ∈ s`: specializing `hmem` to `1` and using
`H.one_mem` already proves it.

## Proof idea

For `a ∈ stabilizer G s`, the stabilizer equivalence at `b` shows `a • b ∈ s`, so `hmem` gives
`a ∈ H`. Conversely, if `a ∈ H`, then `hsmul a` proves the forward implication
`x ∈ s → a • x ∈ s`; applying `hsmul a⁻¹` to `a • x` proves the reverse implication.

The complete checked proof is in `RequestProject/StabilizerUnification.lean`.

## The three callers

After extracting the criterion, the existing results reduce to identifying the detector and the
orientation of multiplication.

### 1. Ordinary subgroup

```lean
apply stabilizer_eq_of_smul_mem_iff (s : Set G) s 1
· simp [smul_eq_mul]
· intro a ha x hx
  exact s.mul_mem ha hx
```

Here the action is left multiplication, so closure is `a * x ∈ s`.

### 2. Ordinary subgroup acted on by the opposite group

```lean
apply stabilizer_eq_of_smul_mem_iff (s : Set G) s.op 1
· simp
· intro a ha x hx
  exact s.mul_mem hx ha
```

The opposite action becomes right multiplication in `G`, so closure is `x * a.unop ∈ s`.

### 3. Opposite subgroup acted on by the ordinary group

```lean
apply stabilizer_eq_of_smul_mem_iff (s : Set Gᵐᵒᵖ) s.unop 1
· intro a
  change MulOpposite.op (a * 1) ∈ s ↔ MulOpposite.op a ∈ s
  simp
· intro a ha x hx
  exact s.mul_mem hx ha
```

Multiplication reverses after passing to `Gᵐᵒᵖ`, which again makes the closure proof a right-hand
multiplication in the subgroup.

## Suggested upstream shape

Place `stabilizer_eq_of_smul_mem_iff` immediately before the three existing lemmas and rewrite their
proofs as above. Keep `@[to_additive]`: it successfully generates
`AddAction.stabilizer_eq_of_vadd_mem_iff` with the corresponding `AddSubgroup` statement.

The name follows the existing `mem_stabilizer_set` vocabulary and exposes the distinctive
hypothesis (`a • b ∈ s ↔ a ∈ H`). It introduces no new structure or framework.

One maintainership tradeoff remains: the extracted criterion is more general and conceptual, but
the total line-count reduction across only these three callers is modest. Its upstream case is
strongest if a search finds another caller where a subgroup is recovered as a set stabilizer from a
detecting point. Even without another caller, it directly resolves the maintainer-written TODO and
removes the duplicated inverse/cancellation argument from all three proofs.

## Verification

`RequestProject/StabilizerUnification.lean` builds without `sorry` or `admit`. The multiplicative
criterion, its generated additive theorem, and all three example callers are kernel-checked. Their
axiom dependencies are only Mathlib's accepted standard axioms (`propext`, `Classical.choice`, and
`Quot.sound`).
