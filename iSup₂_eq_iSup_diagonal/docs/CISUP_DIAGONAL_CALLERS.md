# Which Mathlib callers does the `ciSup` diagonal lemma shorten?

Target of the survey:

```lean
protected theorem ciSup₂_add_eq_ciSup_diagonal (g : ι → Cardinal.{v})
    (hf : BddAbove (range fun k ↦ f k + g k)) (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    ⨆ i, ⨆ j, (f i + g j) = ⨆ k, (f k + g k) :=
  ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j) hf h
```

and its generic parent

```lean
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k
```

Everything claimed below is checked in `RequestProject/CiSupDiagonalCallerSurvey.lean`
(builds, no `sorry`). Greps were run over `Mathlib/` at the commit this project pins.

## Short answer

* The **`Cardinal` add-form has no caller in Mathlib today**, and neither would a multiplicative
  twin. There is no proof anywhere in `Mathlib/` that collapses a doubly indexed supremum *of
  cardinals* onto its diagonal — the search for that pattern returns nothing outside
  `SetTheory/Cardinal/Arithmetic.lean` itself.
* The **generic conditionally complete lemma has three real callers**, all of them the same
  duplicated argument in three different files:
  `ENNReal.iSup_add_iSup`, `ENat.iSup_add_iSup`, `ENNReal.iInf_add_iInf`.
  All three are re-proved through it in the Lean file, with `rfl` checks that the replacements
  prove exactly the current statements.
* The three call sites of `Cardinal.ciSup_add_ciSup` (`rank_add_rank_le_rank_prod`,
  `rank_quotient_add_rank_le`, `lift_trdeg_add_le`) are **not** shortened by the diagonal lemma.
  They share a *different* weakest statement, `Cardinal.ciSup_add_ciSup_le`; all three are
  rewritten through it and `rfl`-checked.

## Method

Ripgrep over `Mathlib/`, in four passes:

```bash
# 1. the lemma names in the neighbourhood
rg -n "iSup_add_iSup|iInf_add_iInf|ciSup_add|ciSup₂|ciSup_add_ciSup|ciSup_mul_ciSup" Mathlib

# 2. the *statement shape*: a doubly indexed supremum
rg -n "⨆ *[^,]*, *⨆|⨆ *\([a-zA-Z_]*\) *\("                    Mathlib

# 3. the *hypothesis shape*: the cofinality side condition of the lemma
rg -n "∃ k, .*≤.*k"                                            Mathlib

# 4. the *proof shape*: nested conditionally complete sup eliminations
rg -n "ciSup₂|ciSup_le.*ciSup_le|ciSup_comm|ciSup_prod|le_ciSup₂" Mathlib
```

Pass 3 is the discriminating one: `∀ i j, ∃ k, … ≤ … k …` is exactly the cofinality hypothesis,
so any proof that could be routed through the lemma has to carry it (or derive it on the spot
from directedness/monotonicity).

## Pass 3, complete hit list (the cofinality hypothesis)

| file | line | declaration |
|---|---|---|
| `Data/ENNReal/Operations.lean` | 690 | `ENNReal.iSup_add_iSup` |
| `Data/ENNReal/Operations.lean` | 564 | `ENNReal.iInf_add_iInf` (dual) |
| `Data/ENat/Lattice.lean` | 223 | `ENat.iSup_add_iSup` |
| `Data/ENNReal/BigOperators.lean` | 156 | `ENNReal.finsetSum_iSup` (uses `iSup_add_iSup`) |
| `Data/ENNReal/BigOperators.lean` | 55 | `ENNReal.iInf_sum` (uses `iInf_add_iInf`) |
| `Data/ENat/BigOperators.lean` | 22 | `ENat.sum_iSup` (uses `iSup_add_iSup`) |

The remaining hits of pass 3 (`MeasureTheory/PiSystem.lean`, `Data/Nat/Nth.lean`,
`Algebra/Lie/Nilpotent.lean`, `NumberTheory/RamificationInertia/Basic.lean`, …) are unrelated
`∃ k` statements, not cofinality of a two-parameter family.

So: **three direct callers, three second-order beneficiaries** (the `BigOperators` lemmas call the
direct ones inside a `Finset.cons_induction`, and they in turn are used in
`MeasureTheory/Integral/Lebesgue/Basic.lean:424`, `…/Lebesgue/Add.lean:264,281` via
`iSup_add_iSup_of_monotone`).

### The three callers, before and after

Current `ENNReal.iSup_add_iSup` / `ENat.iSup_add_iSup` (character-for-character the same proof in
two files):

```lean
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk
```

through the lemma:

```lean
  cases isEmpty_or_nonempty ι
  · simp
  rw [show iSup f + iSup g = ⨆ i, ⨆ j, (f i + g j) by simp_rw [ENNReal.iSup_add, ENNReal.add_iSup]]
  exact ciSup₂_eq_ciSup_diagonal _ (OrderTop.bddAbove _) h
```

Current `ENNReal.iInf_add_iInf`:

```lean
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]
```

through the order-dual of the lemma (no emptiness case split is needed, because `ENNReal.iInf_add`
and `ENNReal.add_iInf` hold for an empty index type):

```lean
  rw [show iInf f + iInf g = ⨅ i, ⨅ j, (f i + g j) by simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]]
  exact ciInf₂_eq_ciInf_diagonal _ (OrderBot.bddBelow _) h
```

Honest accounting: per site the proof body goes 6 → 4, 6 → 4 and 6 → 3 lines (the Lean file wraps
the `rw [show …]` over two lines, so it reads one line longer there). The argument for upstreaming is
not the line count, it is that one order-theoretic fact currently exists as three copies in three
files, none of which mention each other.

Caveat worth stating in the PR: `ℝ≥0∞` and `ℕ∞` are *complete* lattices, so these three sites can
equally be served by the complete-lattice form `iSup₂_eq_iSup_diagonal` (where the `BddAbove`
argument disappears instead of being `OrderTop.bddAbove _`). The conditionally complete form is
what is needed for `Cardinal`, which is only a `ConditionallyCompleteLinearOrderBot`; the
complete-lattice form cannot serve it.

## Why there is no `Cardinal` caller

Passes 1–2 restricted to `SetTheory/Cardinal/`, `LinearAlgebra/Dimension/` and
`RingTheory/AlgebraicIndependent/` return, for `⨆ … + …`, only the four lines of
`Cardinal.ciSup_add`, `Cardinal.add_ciSup` and `Cardinal.ciSup_add_ciSup` themselves. The three
places that *use* `Cardinal.ciSup_add_ciSup` are

| file | line | declaration |
|---|---|---|
| `LinearAlgebra/Dimension/Constructions.lean` | 92 | `rank_quotient_add_rank_le` |
| `LinearAlgebra/Dimension/Constructions.lean` | 132 | `rank_add_rank_le_rank_prod` |
| `RingTheory/AlgebraicIndependent/Transcendental.lean` | 250 | `lift_trdeg_add_le` |

and all three open the same way:

```lean
  rw [Cardinal.ciSup_add_ciSup _ (bddAbove_range _) _ (bddAbove_range _)]
  refine ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦ ?_
```

They *bound* the double supremum; they never collapse it. And they cannot: the two families are
indexed by different types (independent sets in `M` and in `M₁`; in `M ⧸ M'` and in `M'`;
transcendence bases of `S/R` and of `A/S`), so there is no diagonal to collapse onto. The diagonal
lemma is inapplicable at all three sites.

### What those three sites do share

The weakest statement they have in common is the `le` form — the additive `Cardinal` analogue of
`ENNReal.iSup_add_iSup_le`:

```lean
protected theorem Cardinal.ciSup_add_ciSup_le {ι ι' : Type*} [Nonempty ι] [Nonempty ι']
    {f : ι → Cardinal.{v}} {g : ι' → Cardinal.{v}} {c : Cardinal.{v}}
    (hf : BddAbove (range f)) (hg : BddAbove (range g)) (H : ∀ i j, f i + g j ≤ c) :
    (⨆ i, f i) + (⨆ j, g j) ≤ c := by
  rw [Cardinal.ciSup_add_ciSup f hf g hg]
  exact ciSup_le fun i ↦ ciSup_le (H i)
```

Note that Mathlib's existing generic `ciSup_add_ciSup_le`
(`Order/ConditionallyCompleteLattice/Group.lean`, `to_additive` of `ciSup_mul_ciSup_le`) does *not*
cover this: it assumes `Group α`, and `Cardinal` is not a group. Making the general version work
for cancel-free ordered monoids would be the more general fix; the `Cardinal`-local lemma is the
small one.

With it, each of the three sites loses its `rw` and one of its two `ciSup_le`s, e.g.

```lean
theorem rank_add_rank_le_rank_prod [Nontrivial R] :
    Module.rank R M + Module.rank R M₁ ≤ Module.rank R (M × M₁) := by
  conv_lhs => simp only [Module.rank_def]
  exact Cardinal.ciSup_add_ciSup_le (bddAbove_range _) (bddAbove_range _)
    fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ (linearIndependent_inl_union_inr' hs ht).cardinal_le_rank
```

All three rewrites are in the Lean file with `example : @… = @… := rfl` checks against the current
Mathlib statements.

## Naming observation

`rg -n "ciSup₂" Mathlib` returns **no hits**: there is no `ciSup₂` API in Mathlib at all (no
`ciSup₂_le`, no `le_ciSup₂`). The `₂` infix is used only on the complete-lattice side (`iSup₂_le`,
`le_iSup₂`, `iSup₂_eq_bot`, …). A reviewer may therefore object to `ciSup₂_add_eq_ciSup_diagonal`
as introducing a prefix with no precedent; `ciSup_ciSup_eq_ciSup_diagonal`, or dropping the
add-specialisation entirely and exposing only the generic
`ciSup₂_eq_ciSup_diagonal`/`ciSup_ciSup_eq_ciSup_diagonal`, avoids the question.

## Recommendation

1. Post the **generic** lemma (`ConditionallyCompleteLattice`, no `Nonempty ι`) in
   `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`, and rewrite the three
   `ENNReal`/`ENat` proofs through it (or through its complete-lattice form) in the same PR. That
   is the "new lemma → replace duplicates" shape, with three genuine duplicate removals.
2. Ship the `Cardinal` add-specialisation only together with
   `Cardinal.ciSup_add_ciSup_diagonal` (`(⨆ f) + (⨆ g) = ⨆ k, f k + g k`, the `Cardinal` analogue
   of `ENNReal.iSup_add_iSup`), and say plainly in the PR that it has no in-tree caller yet — it
   completes the `ciSup_add` / `add_ciSup` / `ciSup_add_ciSup` block in
   `SetTheory/Cardinal/Arithmetic.lean` rather than removing duplication.
3. `Cardinal.ciSup_add_ciSup_le` is the separate small lemma that actually shortens existing
   `Cardinal` proofs (3 call sites). It is independent of the diagonal lemma and should be its own
   PR, ideally as a generalisation of the `Group`-assuming `ciSup_add_ciSup_le`.
