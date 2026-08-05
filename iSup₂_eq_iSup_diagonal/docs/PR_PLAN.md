# A more complete PR: diagonal / cofinal supremum lemmas

This document expands the original single-lemma idea (`iSup₂_eq_diagonal`) into a small,
focused, well-motivated family of lemmas, following the reviewer's Zulip requests. Everything
described here is machine-checked in `Main.lean` (builds with no `sorry`/`admit`).

## 1. What the reviewer asked for

> "This is sort of a combination of `iSup₂_mono'` and `iSup_mono'`, and also it's an equality since
> only one function is involved. If you add this, could you please also add versions for
> `ConditionallyCompleteLattice`/`ConditionallyCompleteLinearOrderBot`? See
> `ciSup_mono_of_forall_exists` and `ciSup_mono_of_forall_exists'`."

So the requested additions are:
1. the complete-lattice diagonal equality (`iSup₂_eq_diagonal`), plus its `to_dual` infimum
   partner;
2. a `ConditionallyCompleteLattice` version;
3. a `ConditionallyCompleteLinearOrderBot` version (where the empty index collapses to `⊥`, so the
   `Nonempty` hypothesis is dropped).

## 2. What to add (all checked in `Main.lean`)

### 2a. The genuinely reusable core — mutually cofinal families

The reviewer correctly observes the diagonal lemma is `iSup_mono'` applied in both directions. The
weakest statement carrying that content drops the "diagonal" shape entirely:

```lean
@[to_dual]
theorem iSup_eq_iSup_of_forall_exists_le {α : Type*} {ι ι' : Sort*} [CompleteSemilatticeSup α]
    {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i'
```

- Assumes only `CompleteSemilatticeSup` (the weakest class with `sSup`).
- `@[to_dual]` generates `iInf_eq_iInf_of_forall_exists_le` over `CompleteSemilatticeInf`.
- The diagonal lemma is the special case `g k = f k k` (see the checked `example` in `Main.lean`
  deriving it via `iSup_prod'`). We keep the diagonal lemma stated directly, because it works for
  `ι : Sort*`, whereas the reduction through `iSup_prod'` needs `ι : Type*`.

### 2b. The diagonal equality (complete lattice) — already present

```lean
@[to_dual iInf₂_eq_diagonal]
theorem iSup₂_eq_diagonal {α : Type*} {ι : Sort*} [CompleteSemilatticeSup α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k
```

Note it is stated over `CompleteSemilatticeSup` (weaker than `CompleteLattice`) and the proof is
written so `@[to_dual]` succeeds (a naive `le_iSup_of_le` proof does not dualize cleanly — see
`UPSTREAM_REVIEW.md`).

### 2c. Conditionally complete versions

```lean
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (hf : BddAbove (Set.range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k

theorem ciSup₂_eq_ciSup_diagonal' {α : Type*} {ι : Sort*} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → ι → α) (hf : BddAbove (Set.range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k
```

Design notes:
- A single hypothesis `BddAbove (range (fun k ↦ f k k))` suffices: by cofinality every `f i j` is
  bounded by any upper bound of the diagonal, so the inner and outer families are automatically
  bounded above. No separate boundedness hypotheses are needed.
- The primed CCLOB version drops `Nonempty ι`, mirroring the `ciSup_mono` / `ciSup_mono'` pair.
- These are the versions the reviewer explicitly requested, and they cover `ℝ`, `ℝ≥0`, `Cardinal`,
  etc., where `CompleteLattice` does not apply.

Their `iInf` duals could be added the same way (via `OrderDual` or a manual mirror); left out here
to keep the initial PR focused, but easy to include if the reviewer wants them.

## 3. What to change — the duplicate callers (verified)

The identical seven-line diagonal argument currently appears in two places:

- `Mathlib/Data/ENat/Lattice.lean`, `ENat.iSup_add_iSup` (~line 223).
- `Mathlib/Data/ENNReal/Operations.lean`, `ENNReal.iSup_add_iSup` (~line 690).

Both currently read:

```lean
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk
```

and become (checked as `enat_iSup_add_iSup_via_diagonal` / `ennreal_iSup_add_iSup_via_diagonal`):

```lean
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [iSup_add, add_iSup]
    exact iSup₂_eq_diagonal (fun i j ↦ f i + g j) h
```

This exposes the shared order-theoretic step (`iSup₂_eq_diagonal`) instead of re-deriving it,
which is the whole point of the contribution.

## 4. Are there more general forms / more downstream callers?

Findings from searching the Mathlib source (leads confirmed or ruled out, not guesses):

- **Confirmed duplicate callers:** `ENat.iSup_add_iSup` and `ENNReal.iSup_add_iSup` (Section 3).
  These are the two identical proofs and are the core justification for the PR.
- **`iSup_mul_iSup` equalities do not exist** for `ENat`/`ENNReal`/`NNReal`; only the `_le`
  half-versions (`iSup_mul_iSup_le`, `NNReal`'s `iSup_mul_iSup_le`) are present. So there is no
  existing multiplicative duplicate to collapse — an equality would need extra `BddAbove`/`≠ ∞`
  side conditions and is out of scope.
- **Concrete new caller enabled by the conditionally complete version:**
  `Cardinal.ciSup_add_ciSup` and `Cardinal.ciSup_mul_ciSup`
  (`Mathlib/SetTheory/Cardinal/Arithmetic.lean`) currently produce the *uncollapsed* double sup
  `⨆ i, ⨆ j, f i + g j`. A diagonal version follows immediately from `ciSup₂_eq_ciSup_diagonal`;
  this is checked as `cardinal_ciSup_add_ciSup_via_diagonal` in `Main.lean`. `Cardinal` is a
  `ConditionallyCompleteLinearOrderBot`, so this use is only possible with the conditionally
  complete lemma — direct evidence that the reviewer-requested versions have real callers.
- **`lintegral` / measure theory** already route through `ENNReal.iSup_add_iSup`
  (`MeasureTheory/Integral/Lebesgue/Basic.lean` and `.../Add.lean`), so they benefit transitively
  once the `ENNReal` caller is simplified; no separate change needed.
- **A dedicated "cofinal subfamily" typeclass or a general
  "binary-operation-commutes-with-sup" abstraction** would be new framework and is deliberately
  *not* proposed. Reviewers prefer several small discoverable lemmas with demonstrated callers over
  one clever abstraction.

## 5. Suggested upstream placement

- `iSup_eq_iSup_of_forall_exists_le` (+ dual) and `iSup₂_eq_diagonal` (+ dual): near
  `iSup_mono'` / `iSup₂_mono'` in `Mathlib/Order/CompleteLattice/Basic.lean`.
- `ciSup₂_eq_ciSup_diagonal` / `ciSup₂_eq_ciSup_diagonal'`: next to `ciSup_mono'` in
  `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean` (the CCLOB primed version belongs in
  the `ConditionallyCompleteLinearOrderBot` section there).
- Then simplify the two `iSup_add_iSup` callers.

## 6. Suggested PR shape

Keep it as one focused PR: `new lemmas → replace the two duplicate callers`. Optionally split into
(a) the plain + conditionally complete lemmas and (b) the caller simplifications, if reviewers
prefer smaller diffs. The `Cardinal` diagonal corollary can be offered as a follow-up so the main
PR stays minimal.
