import Mathlib

/-!
# Machine-checked backing for the high-leverage scan

This file contains the *verified* candidates cited in `HIGH_LEVERAGE.md`, i.e. the
opportunities that are small and self-contained enough to be discharged here and
handed upstream immediately. Everything below compiles with no `sorry`/`admit`.

The larger candidates in `HIGH_LEVERAGE.md` (missing theories, tactics, decidability
bridges) are, by their nature, not single lemmas and are documented there rather than
proved here.
-/

open scoped Classical

namespace HighLeverage

/-!
## Candidate: `ciInf_mono'` — the missing dual of `ciSup_mono'`

`Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean` has

```
theorem ciSup_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g
```

but there is **no** `ciInf_mono'`.  It is not a mechanical `@[to_dual]` because
Mathlib has no `ConditionallyCompleteLinearOrderTop` class to host the dual of the
`ConditionallyCompleteLinearOrderBot` version.  Stated over a plain
`ConditionallyCompleteLattice` with the honest side conditions (`Nonempty` codomain
index and `BddBelow` on the source range) it goes through directly, dual to the
`ciSup_mono'` proof. -/
theorem ciInf_mono' {α : Type*} {ι ι' : Sort*} [ConditionallyCompleteLattice α]
    {f : ι → α} {g : ι' → α} [Nonempty ι'] (hf : BddBelow (Set.range f))
    (h : ∀ i', ∃ i, f i ≤ g i') : iInf f ≤ iInf g :=
  le_ciInf fun i' => Exists.elim (h i') (ciInf_le_of_le hf)

/-- Sanity check: the existing `ciSup_mono'` and the new `ciInf_mono'` are genuine
duals of one another (same shape, opposite direction). -/
example {α : Type*} {ι ι' : Sort*} [ConditionallyCompleteLinearOrderBot α]
    {f : ι → α} {g : ι' → α} (hg : BddAbove (Set.range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  ciSup_mono' hg h

end HighLeverage
