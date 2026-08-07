# Review of the naming diagnosis, and the adjustments it implies for the PR

This note answers the review round on the six misnamed duplicates in
`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`. Verdict first, then the four concrete
adjustments, then the two places where the informal statement of the intended lemma needs
correcting before it goes into a patch.

## 1. The diagnosis is right

```lean
lemma rpow_le_of_le_log (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h
```

Name, statement and proof disagree exactly as described. `rpow_le_of_le_log` promises
`(le_log) → (rpow_le)`, i.e. base to the left of `≤` in the conclusion, `log` on the right of `≤`
in the hypothesis; the declaration delivers `(log_le) → (le_rpow)`, and its proof goes through
`le_rpow_iff_log_le`, whose very name records that. The neighbours `rpow_le_iff_le_log` and
`le_log_of_rpow_le` fix the convention, so the misnaming is not a matter of taste. And the
correctly named theorem already exists forty lines up, verbatim: `le_rpow_of_log_le`. That is what
`RequestProject/RpowLogDedup.lean` certifies with `@rpow_le_of_le_log = @le_rpow_of_log_le := rfl`
for all six pairs.

The order of priorities in the review — correct statement > correct name > short proof — is also
the right one here, and it is what makes the alias patch, not a restatement, the correct first
move: the statement is already correct, so only the name is in question, and a public name is
repaired by deprecation, never by overwriting.

## 2. Adjustments to the cleanup PR (`mathlib-patch-rpow-log-dedup.diff`)

Substance unchanged: six `@[deprecated] alias`es, 6 insertions / 20 deletions, no declaration
leaves the environment, no call site anywhere in Mathlib, Archive, Counterexamples or tests.
Three mechanical points to settle before opening it:

1. **`since` date.** `(since := "2026-08-06")` is a placeholder; set it to the date the PR is
   opened, as the convention expects.
2. **Where the aliases live.** The patch leaves them in place of the deleted block. Placing them
   immediately after their targets (`le_rpow_of_log_le` &c.), or in a `### Deprecated lemmas`
   group at the end of the section, is the more usual layout and makes the duplicated block
   disappear from the file's structure, not just from its content.
3. **PR description.** Say explicitly that the aliases preserve the *statements*, so nothing
   downstream can change meaning; and that the proposition the misleading names suggest is
   available under positivity as `(rpow_le_iff_le_log hx hy).2` — nothing is lost.

## 3. Adjustments to the follow-up PR (`mathlib-patch-rpow-log-dedup-plus-general.diff`)

Keep it a *separate* PR. Its content is the honest reading of the six names, in the generality it
actually has:

```lean
lemma rpow_le_of_mul_log_le (hy : 0 < y) (h : z * log x ≤ log y) : x ^ z ≤ y
```

for **every** real base `x` (`log x = log |x|` and `x ^ z ≤ |x| ^ z`), which is strictly stronger
than `(rpow_le_iff_le_log hx hy).2`; the mirror of what `le_rpow_of_log_le` does on the other side.
Adjustments:

* **Names.** With the hypothesis spelled as a product, the convention gives
  `rpow_le_of_mul_log_le` / `rpow_lt_of_mul_log_lt` (plus `pow_`/`zpow_` forms) — the plain
  `rpow_le_of_le_log` is occupied by the deprecated alias.
* **Follow-up plan, stated in the PR.** Once the deprecations expire and the aliases are removed,
  the general lemmas can be renamed onto the freed names. That is the only route to "the name
  finally means what it says" that never repurposes a live name.
* **Sharpness in the description, not in the file.** `0 < y` is necessary (`x = 2, z = 1, y = -2`),
  and the iff cannot be generalised because its forward direction fails (`x = -2, z = 1, y = 1`);
  both are proved in `RequestProject/RpowLogIntent.lean` and belong in the PR text, not in Mathlib.

## 4. Two corrections to the informal "intended" statement

The review proposes `(h : z • log y ≤ log x) : y ^ z ≤ x`. Both details are checked in
`RequestProject/RpowLogNameReading.lean`:

* **The positivity hypothesis must move to the bound.** In the current lemma `0 < y` is positivity
  of the base. In the flipped statement the bound is `x`, and it is `x` that must be positive:
  `Real.le_log_reading_needs_pos_bound` exhibits `y = 1, z = 1, x = -2`, where `0 < y` and
  `z * log y = 0 ≤ log 2 = log (-2) = log x` hold while `y ^ z = 1 ≤ -2` fails. The correct
  binder is `(hx : 0 < x)`, and then *no* positivity on the base is needed at all
  (`Real.rpow_le_of_le_log_as_named`, which is the generalised lemma with `x` and `y` exchanged).
* **`*`, not `•`.** For real `z`, `z • log y = z * log y` (`smul_eq_mul`), and for `n : ℕ` the
  `nsmul` form is `nsmul_eq_mul` (`Real.pow_le_of_le_log_as_named_smul` derives the `•` version in
  one line). So `•` is not a different lemma; the whole surrounding block writes the coerced
  product `(n : ℝ) * log y`, and a patch should match it.

## 5. Recommendation

Land the alias PR as it stands (with the three mechanical fixes in §2); open the generalisation as
a second, independent PR with the names in §3. The first is a pure deletion that cannot break
anything; the second is a small feature whose fate — does `Real.rpow` at a negative base deserve
API? — is a reviewer judgement that should not hold up the cleanup.
