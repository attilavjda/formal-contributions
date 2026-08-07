/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RequestProject.RpowLogIntent

/-!
# The name's reading, written out in the reviewer's own variables

The follow-up question is whether

```lean
lemma rpow_le_of_le_log (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z
```

should instead read

```lean
(h : z * log y ≤ log x) : y ^ z ≤ x
```

as the name announces.  That reading is exactly `RequestProject/RpowLogIntent.lean`'s
`Real.rpow_le_of_le_log_intended` with the two variable names exchanged; this file records the
translation (`rpow_le_of_le_log_as_named`) so the two formulations can be compared side by side,
and pins down the two details the informal version leaves open.

* **The positivity hypothesis has to move with the statement.**  In the current lemma `0 < y` is
  positivity of the *base*.  In the name's reading the base is `y` again but the bound is `x`, and
  it is the *bound* that must be positive: keeping `0 < y` and flipping the rest yields a false
  statement (`le_log_reading_needs_pos_bound`, witnessed at `y = 1, z = 1, x = -2`).  No positivity
  on the base is needed at all — that is the content of the generalised lemma.
* **`•` versus `*`.**  For `z : ℝ` acting on `ℝ`, `z • log y` and `z * log y` are the same term up
  to `smul_eq_mul`, and for `n : ℕ` the `nsmul` form is `nsmul_eq_mul`
  (`pow_le_of_le_log_as_named_smul`).  The surrounding block in Mathlib writes the coerced product
  `(n : ℝ) * log y`, so a patch should keep `*` for consistency with
  `Real.rpow_le_iff_le_log`, `Real.le_log_of_rpow_le` and their neighbours.
-/

namespace Real

variable {x y z : ℝ} {n : ℕ}

/-- The proposition the name `Real.rpow_le_of_le_log` announces, spelled with the base called `y`
and the bound called `x`: from `z * log y ≤ log x` and `0 < x` one gets `y ^ z ≤ x`, for an
arbitrary real base `y`.  This is `Real.rpow_le_of_le_log_intended` with `x` and `y` exchanged. -/
lemma rpow_le_of_le_log_as_named (hx : 0 < x) (h : z * log y ≤ log x) : y ^ z ≤ x :=
  rpow_le_of_le_log_intended hx h

/-- The `nsmul` spelling of `Real.rpow_le_of_le_log_as_named`: `n • log y` is `(n : ℝ) * log y`, so
the `•` form is the same lemma, not a new one. -/
lemma pow_le_of_le_log_as_named_smul (hx : 0 < x) (h : n • log y ≤ log x) : y ^ n ≤ x :=
  pow_le_of_le_log_intended hx (by rwa [nsmul_eq_mul] at h)

/-- For a real scalar the two spellings are literally equal. -/
lemma smul_log_eq_mul_log (z w : ℝ) : z • log w = z * log w := smul_eq_mul ..

/-- Flipping the statement while keeping the old binder `0 < y` (positivity of the *base*) would be
false: at `y = 1, z = 1, x = -2` one has `0 < y` and `z * log y = 0 ≤ log 2 = log (-2) = log x`,
yet `y ^ z = 1 ≤ -2` fails.  The positivity must be transferred to the bound `x`. -/
lemma le_log_reading_needs_pos_bound :
    ∃ x y z : ℝ, 0 < y ∧ z * log y ≤ log x ∧ ¬ y ^ z ≤ x := by
  refine ⟨-2, 1, 1, one_pos, ?_, ?_⟩
  · rw [log_one, one_mul, log_neg_eq_log]
    exact (log_pos (by norm_num)).le
  · rw [rpow_one]
    norm_num

end Real
