/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# What the misleading names *would* mean, and whether stating that is better

`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` contains six lemmas whose names promise a
conclusion they do not have, and which are byte-identical duplicates of six correctly named
lemmas a few lines above (see `RequestProject/RpowLogDedup.lean`):

```lean
lemma le_rpow_of_log_le (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z   -- correctly named
lemma rpow_le_of_le_log (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z   -- same statement (P1)
```

The name `rpow_le_of_le_log` announces the *other* proposition,

```lean
P2 : (h : z * log x ≤ log y) : x ^ z ≤ y
```

matching its neighbours `rpow_le_iff_le_log` and `le_log_of_rpow_le`.  This file settles what
`P2` actually costs, because that decides whether "repair the statement to match the name" is a
sensible alternative to "deprecate the duplicate name".

The outcome, in three points.

* **`P2` with the hypotheses of the iff is pure redundancy.**  `(rpow_le_iff_le_log hx hy).2` is
  literally `P2` under `0 < x`, `0 < y`; adding it as a lemma adds a name and no mathematics.
* **`P2` has a genuinely more general form, and it is *not* the `.2` of the iff.**  The positivity
  of the base can be dropped entirely: `rpow_le_of_le_log_intended` below assumes only `0 < y`.
  This is the exact mirror of what `le_rpow_of_log_le` does (it drops `0 < x` from
  `le_rpow_iff_log_le`), so the "intended" reading of the name is a real, currently missing lemma —
  a symmetry gap, not a duplicate.  `rpow_le_of_le_log_intended_strictly_stronger` witnesses the
  strengthening at `x = -2`.
* **Nothing more can be dropped, and the iff cannot absorb it.**  `0 < y` is necessary
  (`rpow_le_of_le_log_intended_needs_pos_right`), and `rpow_le_iff_le_log` cannot be generalised by
  removing `0 < x`, because its forward direction fails there
  (`rpow_le_iff_le_log_needs_pos_left`).

Consequently the two options are *not* interchangeable: deprecating the duplicates removes
duplication (it is the line-removing contribution), whereas restating them as `P2` is a silent
change of meaning of a two-year-old public name **plus** an addition.  The clean split is to
deprecate now and, separately, offer the generalised `P2` lemmas below under fresh names.

The six `…_intended` lemmas below are what the patch
`mathlib-patch-rpow-log-dedup-plus-general.diff` installs upstream, there under the
collision-free names `rpow_le_of_mul_log_le`, `pow_le_of_mul_log_le`, `zpow_le_of_mul_log_le`,
`rpow_lt_of_mul_log_lt`, `pow_lt_of_mul_log_lt`, `zpow_lt_of_mul_log_lt` (the names
`rpow_le_of_le_log` &c. being occupied by the deprecated aliases); the proofs are identical.

All statements here are about `Real.rpow` with an arbitrary real base; recall that
`Real.log x = Real.log |x|`, which is why the general form is true at all.
-/

namespace Real

variable {x y z : ℝ} {n : ℕ}

/-! ### The proposition the name `rpow_le_of_le_log` promises, in its natural generality -/

/-- If `z * log x ≤ log y` and `0 < y`, then `x ^ z ≤ y`, *with no positivity assumption on the
base `x`*.  Under `0 < x` this is `(Real.rpow_le_iff_le_log hx hy).2`; the point of the lemma is
that the hypothesis `0 < x` is not needed, exactly as `Real.le_rpow_of_log_le` does not need it.
Upstream this would be the honest content of the name `Real.rpow_le_of_le_log`. -/
lemma rpow_le_of_le_log_intended (hy : 0 < y) (h : z * log x ≤ log y) : x ^ z ≤ y := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [log_zero, mul_zero] at h
    obtain rfl | hz := eq_or_ne z 0
    · simpa using (log_nonneg_iff hy).1 h
    · simpa [zero_rpow hz] using hy.le
  · calc x ^ z ≤ |x| ^ z := (le_abs_self _).trans (abs_rpow_le_abs_rpow x z)
      _ ≤ y := (rpow_le_iff_le_log (abs_pos.2 hx) hy).2 (by rwa [log_abs])

/-- Natural-power form of `Real.rpow_le_of_le_log_intended`. -/
lemma pow_le_of_le_log_intended (hy : 0 < y) (h : n * log x ≤ log y) : x ^ n ≤ y :=
  rpow_natCast _ _ ▸ rpow_le_of_le_log_intended hy h

/-- Integer-power form of `Real.rpow_le_of_le_log_intended`. -/
lemma zpow_le_of_le_log_intended {n : ℤ} (hy : 0 < y) (h : n * log x ≤ log y) : x ^ n ≤ y :=
  rpow_intCast _ _ ▸ rpow_le_of_le_log_intended hy h

/-- Strict form of `Real.rpow_le_of_le_log_intended`. -/
lemma rpow_lt_of_lt_log_intended (hy : 0 < y) (h : z * log x < log y) : x ^ z < y := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [log_zero, mul_zero] at h
    obtain rfl | hz := eq_or_ne z 0
    · simpa using (log_pos_iff hy.le).1 h
    · simpa [zero_rpow hz] using hy
  · calc x ^ z ≤ |x| ^ z := (le_abs_self _).trans (abs_rpow_le_abs_rpow x z)
      _ < y := (rpow_lt_iff_lt_log (abs_pos.2 hx) hy).2 (by rwa [log_abs])

/-- Natural-power form of `Real.rpow_lt_of_lt_log_intended`. -/
lemma pow_lt_of_lt_log_intended (hy : 0 < y) (h : n * log x < log y) : x ^ n < y :=
  rpow_natCast _ _ ▸ rpow_lt_of_lt_log_intended hy h

/-- Integer-power form of `Real.rpow_lt_of_lt_log_intended`. -/
lemma zpow_lt_of_lt_log_intended {n : ℤ} (hy : 0 < y) (h : n * log x < log y) : x ^ n < y :=
  rpow_intCast _ _ ▸ rpow_lt_of_lt_log_intended hy h

/-! ### The generalised statement is strictly stronger than the `.2` of the iff -/

/-- A case the `.2` direction of `Real.rpow_le_iff_le_log` cannot reach: the base is negative.
Here `(-2 : ℝ) ^ (2 : ℝ) = 4 ≤ 4` is obtained from `2 * log (-2) ≤ log 4`. -/
lemma rpow_le_of_le_log_intended_strictly_stronger :
    ((-2 : ℝ) ^ (2 : ℝ) ≤ 4) ∧ ¬ (0 : ℝ) < -2 := by
  refine ⟨rpow_le_of_le_log_intended (by norm_num) ?_, by norm_num⟩
  have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
  rw [log_neg_eq_log, h4, log_pow]
  push_cast
  ring_nf
  exact le_refl _

/-! ### Neither remaining hypothesis can be removed -/

/-- The hypothesis `0 < y` in `Real.rpow_le_of_le_log_intended` is necessary: at
`x = 2, z = 1, y = -2` one has `z * log x ≤ log y` (because `log (-2) = log 2`) while
`x ^ z ≤ y` fails. -/
lemma rpow_le_of_le_log_intended_needs_pos_right :
    ∃ x y z : ℝ, z * log x ≤ log y ∧ ¬ x ^ z ≤ y := by
  refine ⟨2, -2, 1, ?_, ?_⟩
  · rw [log_neg_eq_log, one_mul]
  · rw [rpow_one]
    norm_num

/-- `Real.rpow_le_iff_le_log` itself cannot be generalised by dropping `0 < x`: its forward
direction fails at `x = -2, z = 1, y = 1`, where `x ^ z = -2 ≤ 1` but `1 * log (-2) = log 2 > 0`. -/
lemma rpow_le_iff_le_log_needs_pos_left :
    ∃ x y z : ℝ, 0 < y ∧ x ^ z ≤ y ∧ ¬ z * log x ≤ log y := by
  refine ⟨-2, 1, 1, one_pos, ?_, ?_⟩
  · rw [rpow_one]; norm_num
  · rw [log_neg_eq_log, one_mul, log_one]
    have : (0 : ℝ) < log 2 := log_pos (by norm_num)
    linarith

end Real
