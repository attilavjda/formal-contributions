# Duplicate search: limits, trigonometric functions, sequences, and linear algebra

## Strong candidate: iterating an eigen-relation

### Repeated proofs found

The clearest cluster is in the iterated-derivative sections of:

- `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean`
- `Mathlib/Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean`

There are separate inductions for each of the following, and then the same
families are repeated over `ℂ` and `ℝ`:

- `Complex.iteratedDeriv_even_sin`
- `Complex.iteratedDeriv_even_cos`
- `Real.iteratedDeriv_even_sin`
- `Real.iteratedDeriv_even_cos`
- `Complex.iteratedDeriv_even_sinh`
- `Complex.iteratedDeriv_even_cosh`
- `Real.iteratedDeriv_even_sinh`
- `Real.iteratedDeriv_even_cosh`

The common argument is not trigonometric.  If an operator `f` commutes with
scalar multiplication by `c`, and `f x = c • x`, then iterating gives
`f^[n] x = c ^ n • x`.  This is the elementary “powers preserve an
eigenvector” argument.

### Weak generic statement

```lean
theorem Function.Commute.iterate_apply_eq_pow_smul
    {R α : Type*} [Monoid R] [MulAction R α]
    {f : α → α} {c : R} {x : α}
    (hcomm : Function.Commute f (c • ·)) (hx : f x = c • x) (n : ℕ) :
    f^[n] x = c ^ n • x
```

This is deliberately weaker than introducing a linear-map framework: it only
requires a monoid action, commutation, and one pointwise relation.  The name is
predictable beside `Function.Commute.iterate_eq_of_map_eq`, which supplies the
main step, and `smul_iterate_apply` supplies the closed form.

A calculus-facing corollary packages the exact repeated pattern:

```lean
theorem iteratedDeriv_two_mul_of_two_eq_smul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (f : 𝕜 → 𝕜) (c : 𝕜)
    (h : iteratedDeriv 2 f = c • f) (n : ℕ) :
    iteratedDeriv (2 * n) f = c ^ n • f
```

The generic lemma and this corollary are proved in
`RequestProject/AnalysisDuplicates.lean`.

### Three checked simplifications

The same file gives non-inductive replacement proofs for:

1. `Real.iteratedDeriv_even_sin` with eigenvalue `-1` for the second derivative;
2. `Real.iteratedDeriv_even_cos` with eigenvalue `-1`;
3. `Real.iteratedDeriv_even_sinh` with eigenvalue `1`.

The corresponding complex results and the `cosh` results have exactly the same
shape.  Thus one small generic result addresses at least eight local induction
proofs, while each application only has to establish the relevant second-derivative identity.

### Suggested upstream placement

Two reasonable, small-scope options are:

- put `Function.Commute.iterate_apply_eq_pow_smul` near
  `Function.Commute.iterate_eq_of_map_eq` in `Mathlib/Logic/Function/Iterate.lean`;
- put `iteratedDeriv_two_mul_of_two_eq_smul` near `iteratedDeriv_eq_iterate` in
  `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean` or in the associated
  lemmas file.

The first is the more reusable contribution; the second makes the eight
trigonometric replacements especially direct.

## Linear-algebra cross-check

The same “multiplicative operation preserves powers” proof shape occurs in:

- `TensorProduct.map_pow`;
- `TensorProduct.congr_pow`;
- `LinearEquiv.baseChange_pow`;
- `LinearMap.toMatrix_pow` and `Matrix.toLin_pow`;
- `Matrix.adjugate_pow`.

This scan is useful mainly as a boundary check.  Several nearby cases are
already correctly bundled as homomorphisms and proved with generic `map_pow`:
`LinearMap.baseChange_pow` uses `Module.End.baseChangeHom`, and
`PiTensorProduct.map_pow` uses `mapMonoidHom`.  The remaining operations differ
in variance or orientation, so a new abstraction solely for them would be less
convincing than the iteration lemma above.  In particular, this search did not
find a second comparably weak statement that cleanly replaces three of these
proofs without adding framework.

## Limits and sequence/sum induction cross-check

I also inspected the induction-heavy parts of:

- `Mathlib/Analysis/SpecificLimits/ArithmeticGeometric.lean`;
- `Mathlib/Analysis/SpecificLimits/Normed.lean`;
- the trigonometric series files;
- sequence/sum proofs using repeated `Finset.sum_range_succ` steps.

`arithGeom_eq_add_sum` and `arithGeom_eq` are superficially similar recurrence
inductions, but they prove genuinely different normal forms (a finite geometric
sum versus a fixed-point expression).  The alternating-series bounds in
`SpecificLimits/Normed.lean` likewise share local `sum_range_succ` bookkeeping,
but their hypotheses and conclusions differ enough that extracting their proof
scripts would not produce a clean, weak API lemma.  Existing generic lemmas such
as `Finset.sum_range_succ`, `Function.iterate_mul`, and geometric-series results
already mark the appropriate abstraction boundaries.

So the iteration/eigen-relation cluster is the strongest contribution candidate
from this targeted search; the limits and sum scans produced useful negative
evidence rather than another equally clean proposal.
