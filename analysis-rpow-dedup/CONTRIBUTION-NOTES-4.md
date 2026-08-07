# Deprecate the misnamed duplicates, or restate them as the name promises?

This note answers the follow-up question: instead of aliasing the six duplicated lemmas in
`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` away, should the *statements* be adjusted to
the proposition their names announce?

Recall the situation (details in `CONTRIBUTION-NOTES-3.md`). The file contains, a few lines apart,

```lean
lemma le_rpow_of_log_le (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z   -- P1, correctly named
lemma rpow_le_of_le_log (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z   -- P1 again, misnamed
```

and five more such pairs. The name `rpow_le_of_le_log` announces

```lean
P2 : (h : z * log x ≤ log y) : x ^ z ≤ y
```

matching its neighbours `rpow_le_iff_le_log` and `le_log_of_rpow_le`.

## The new fact this session establishes

The earlier note said "P2 is already available as the `.2` direction of `rpow_le_iff_le_log`, so
nothing is missing mathematically". **That is true only of the weak form of P2.** In its natural
generality P2 is strictly stronger than `(rpow_le_iff_le_log hx hy).2`, because the positivity of
the *base* can be dropped completely:

```lean
lemma rpow_le_of_mul_log_le (hy : 0 < y) (h : z * log x ≤ log y) : x ^ z ≤ y
```

holds for every real `x`, positive, zero or negative. The reason is that `Real.log x = Real.log |x|`
and `x ^ z ≤ |x ^ z| ≤ |x| ^ z` (`Real.abs_rpow_le_abs_rpow`), so the hypothesis already controls
`|x| ^ z`; the base case `x = 0` is handled by `log 0 = 0`. This is the exact mirror image of what
`le_rpow_of_log_le` does on the other side (it drops `0 < x` from `le_rpow_iff_log_le` by the
trivial bound `x ≤ 0 < y ^ z`).

So the "intended" reading of the misleading name is a genuine **symmetry gap**, not a duplicate:
the block currently has the degenerate-base version of P1 but not of P2.

Two sharpness checks accompany it, so no hypothesis is left in by accident:

* `0 < y` cannot be dropped: at `x = 2, z = 1, y = -2` one has `z * log x = log 2 = log (-2) = log y`
  but `2 ≤ -2` fails.
* `rpow_le_iff_le_log` itself cannot be generalised by removing `0 < x`: its forward direction fails
  at `x = -2, z = 1, y = 1`, where `(-2) ^ (1 : ℝ) = -2 ≤ 1` while `1 * log (-2) = log 2 > 0 = log 1`.
  Only the `←` direction survives, which is precisely the new lemma.

Everything above is proved in `RequestProject/RpowLogIntent.lean` (no `sorry`/`admit`/`axiom`;
axioms `propext`, `Classical.choice`, `Quot.sound` only).

## Why "adjust the statement to the name" is still not the right patch

1. **It repurposes a public name.** `rpow_le_of_le_log` and its five siblings entered Mathlib on
   2024-08-26 (PR #15859) and have carried the P1 meaning ever since. Silently giving an existing
   name a different theorem is the one thing the deprecation machinery cannot warn about; downstream
   users get either a type error at best or, in a sufficiently generic context, a different fact than
   they read in the docs. Mathlib's convention is to deprecate and re-introduce, never to overwrite.
2. **It fails the test the original task set.** "The diff removes something." Restating the six
   duplicates as P2 removes nothing: the duplication of P1 stays (the six copies are still
   redundant with `le_rpow_of_log_le` &c. only if you also delete them), and six new theorems are
   added. It is a feature PR wearing a cleanup PR's clothes.
3. **The two changes are logically independent.** Deprecating the duplicates is unconditional and
   riskless (no call site anywhere in Mathlib, the Archive, Counterexamples or tests). Adding the
   generalised P2 is a judgement call about whether `Real.rpow` at a negative base is worth API —
   a reviewer may reasonably say no, and that should not block the cleanup.

## What is on offer

Two ready-to-apply patches, both compiled against the pinned Mathlib checkout with no errors and no
linter warnings (the checkout was reverted afterwards):

* `mathlib-patch-rpow-log-dedup.diff` — **recommended, the cleanup PR.** Six deprecated aliases
  replace the six duplicates; 6 insertions, 20 deletions; no declaration leaves the environment.
* `mathlib-patch-rpow-log-dedup-plus-general.diff` — the cleanup *plus* the six generalised P2
  lemmas, under collision-free names `rpow_le_of_mul_log_le`, `pow_le_of_mul_log_le`,
  `zpow_le_of_mul_log_le`, `rpow_lt_of_mul_log_lt`, `pow_lt_of_mul_log_lt`,
  `zpow_lt_of_mul_log_lt`; 40 insertions, 20 deletions. (The obvious names `rpow_le_of_le_log` &c.
  are occupied by the deprecated aliases; once those expire — Mathlib removes deprecations after
  about six months — the new lemmas could be renamed onto them, which is the only way the "fix the
  statement to match the name" outcome can be reached without repurposing a live name.)

Verification artefacts:

| file | contents |
| ---- | -------- |
| `RequestProject/RpowLogDedup.lean` | the six pairs are literally the same theorem (`rfl`), and the survivors cover the duplicates' API |
| `RequestProject/RpowLogIntent.lean` | the six generalised P2 lemmas, the negative-base witness that they exceed `(rpow_le_iff_le_log hx hy).2`, and the two sharpness counterexamples |
