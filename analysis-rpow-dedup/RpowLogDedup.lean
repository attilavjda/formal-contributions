/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Six duplicated `rpow`/`log` comparison lemmas in `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`

`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` contains two blocks of lemmas relating
`Real.log` to real, natural and integer powers.  Three lemmas of the second block are
character-for-character copies of three lemmas of the first block, under different names:

| kept name (correct)     | duplicate name (misleading) |
| ----------------------- | --------------------------- |
| `Real.le_rpow_of_log_le`| `Real.rpow_le_of_le_log`    |
| `Real.le_pow_of_log_le` | `Real.pow_le_of_le_log`     |
| `Real.le_zpow_of_log_le`| `Real.zpow_le_of_le_log`    |
| `Real.lt_rpow_of_log_lt`| `Real.rpow_lt_of_lt_log`    |
| `Real.lt_pow_of_log_lt` | `Real.pow_lt_of_lt_log`     |
| `Real.lt_zpow_of_log_lt`| `Real.zpow_lt_of_lt_log`    |

Each pair has *the same statement and the same proof*, so the second block is redundant.  Moreover
the names in the second block are misleading: the conclusion of `Real.rpow_le_of_le_log` is
`x ≤ y ^ z`, which the naming convention spells `le_rpow_of_log_le` (as the first block does);
the name `rpow_le_of_le_log` announces a conclusion of the form `x ^ z ≤ y`, matching its
neighbours `Real.rpow_le_iff_le_log` and `Real.le_log_of_rpow_le`, and is therefore actively
confusing.

This file certifies both halves of the deduplication claim:

* `Real.rpow_le_of_le_log_eq` and friends check, by `rfl`, that the two members of each pair are
  *the same theorem* (same statement, hence the equality typechecks, and same proof term);
* `Real.le_rpow_of_log_le_covers_duplicate` and friends check that the statement of each duplicate
  is discharged by the surviving lemma alone, i.e. no API is lost by replacing the duplicates with
  `@[deprecated] alias`es.

The accompanying patch `mathlib-patch-rpow-log-dedup.diff` performs the deletion
(6 insertions, 20 deletions).  At the time of writing, no declaration anywhere in Mathlib, the
Archive, the Counterexamples or the test suite refers to any of the six duplicate names.
-/

namespace Real

/-! ### The two members of each pair are literally the same theorem -/

theorem rpow_le_of_le_log_eq : @rpow_le_of_le_log = @le_rpow_of_log_le := rfl

theorem pow_le_of_le_log_eq : @pow_le_of_le_log = @le_pow_of_log_le := rfl

theorem zpow_le_of_le_log_eq : @zpow_le_of_le_log = @le_zpow_of_log_le := rfl

theorem rpow_lt_of_lt_log_eq : @rpow_lt_of_lt_log = @lt_rpow_of_log_lt := rfl

theorem pow_lt_of_lt_log_eq : @pow_lt_of_lt_log = @lt_pow_of_log_lt := rfl

theorem zpow_lt_of_lt_log_eq : @zpow_lt_of_lt_log = @lt_zpow_of_log_lt := rfl

/-! ### The surviving lemmas provide the full API of the duplicates -/

theorem le_rpow_of_log_le_covers_duplicate {x y z : ℝ} (hy : 0 < y) (h : log x ≤ z * log y) :
    x ≤ y ^ z :=
  le_rpow_of_log_le hy h

theorem le_pow_of_log_le_covers_duplicate {x y : ℝ} {n : ℕ} (hy : 0 < y)
    (h : log x ≤ n * log y) : x ≤ y ^ n :=
  le_pow_of_log_le hy h

theorem le_zpow_of_log_le_covers_duplicate {x y : ℝ} {n : ℤ} (hy : 0 < y)
    (h : log x ≤ n * log y) : x ≤ y ^ n :=
  le_zpow_of_log_le hy h

theorem lt_rpow_of_log_lt_covers_duplicate {x y z : ℝ} (hy : 0 < y) (h : log x < z * log y) :
    x < y ^ z :=
  lt_rpow_of_log_lt hy h

theorem lt_pow_of_log_lt_covers_duplicate {x y : ℝ} {n : ℕ} (hy : 0 < y)
    (h : log x < n * log y) : x < y ^ n :=
  lt_pow_of_log_lt hy h

theorem lt_zpow_of_log_lt_covers_duplicate {x y : ℝ} {n : ℤ} (hy : 0 < y)
    (h : log x < n * log y) : x < y ^ n :=
  lt_zpow_of_log_lt hy h

end Real
