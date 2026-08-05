# What the reviewer is asking for

> As I said on the Zulip thread `#mathlib4 > Duplicate ENat/ENNReal iSup_add_iSup proofs`, could you
> please also add versions for `ConditionallyCompleteLattice`/`ConditionallyCompleteLinearOrderBot`?
> See `ciSup_mono_of_forall_exists` and `ciSup_mono_of_forall_exists'`.

Short version: *your lemma currently only works for complete lattices, which is exactly the two
types you deduplicated. Please also state it in the conditionally complete setting, following the
existing two-lemma pattern in `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean` — the
unprimed lemma for `ConditionallyCompleteLattice`, the primed one for
`ConditionallyCompleteLinearOrderBot` — and use `ciSup_mono_of_forall_exists` /
`ciSup_mono_of_forall_exists'` as the model for naming, hypotheses and proof style.*

Everything asserted below is machine-checked in `RequestProject/ReviewerCCLRequest.lean` (builds,
no `sorry`).

## 1. "versions" = the same statement, weaker order assumptions

Your PR extracts, from the duplicated `ENat.iSup_add_iSup` / `ENNReal.iSup_add_iSup` /
`ENNReal.iInf_add_iInf` proofs, the diagonal-collapse lemma

```lean
theorem iSup₂_eq_iSup_diagonal [CompleteSemilatticeSup α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) : ⨆ i, ⨆ j, f i j = ⨆ k, f k k
```

`ℕ∞` and `ℝ≥0∞` are complete lattices, so as stated the lemma serves only the call sites you
already touched. The same argument is used verbatim for orders that have suprema of *bounded*
families only — `Cardinal`, `ℝ≥0`, `ℝ` — and there the complete-lattice lemma does not typecheck.
The reviewer is asking you to add the conditionally complete statement, in which the boundedness
that the complete lattice supplied for free becomes an explicit hypothesis:

```lean
theorem ciSup₂_eq_ciSup_diagonal [ConditionallyCompleteLattice α] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k
```

Note only the *diagonal* has to be assumed bounded: cofinality then bounds each row and the row
suprema.

## 2. "`ConditionallyCompleteLattice`/`ConditionallyCompleteLinearOrderBot`" = the standard pair

In `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean` most `ciSup` lemmas come in two:

| section | typeclass | convention |
| --- | --- | --- |
| `ConditionallyCompleteLattice` | general | needs `[Nonempty ι]`; uses `ciSup_le`, `le_ciSup` |
| `ConditionallyCompleteLinearOrderBot` | has `⊥` | `'`-suffixed name; no `[Nonempty ι]`; uses `ciSup_le'` |

The reason for the split: over a conditionally complete lattice `⨆ i, f i` for empty `ι` is the junk
value `sSup ∅`, about which nothing is known, so the empty index has to be excluded; when the order
has a bottom element, `⨆ i, f i = ⊥` there and the hypothesis can be dropped
(`ciSup_le'`, `ciSup_of_empty`).

So the request is for two declarations, `ciSup₂_eq_ciSup_diagonal` and `ciSup₂_eq_ciSup_diagonal'`,
placed in those two sections.

## 3. The two lemmas cited are the template — and are literally half of your proof

```lean
theorem ciSup_mono_of_forall_exists [ConditionallyCompleteLattice α] [Nonempty ι]
    (hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k) : ⨆ i, f i ≤ ⨆ k, g k

theorem ciSup_mono_of_forall_exists' [ConditionallyCompleteLinearOrderBot α]
    (hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k) : ⨆ i, f i ≤ ⨆ k, g k
```

They are cited for three reasons:

1. **Placement and naming.** They are the nearest neighbours of what you are adding, in the file
   you should add to, and they show the naming convention (`'` = the `…Bot` copy) and the
   hypothesis order `(hg : BddAbove …) (h : ∀ …, ∃ …, … ≤ …)` you should mirror.
2. **Proof.** The `≤` half of the diagonal collapse *is* this lemma applied row by row:
   `ciSup_le fun i ↦ ciSup_mono_of_forall_exists hf (h i)`. Reuse it rather than re-proving it.
3. **Hypothesis shape.** They already use the "every element of the source is below some element of
   the target" (cofinality) hypothesis that your lemma uses, so the reviewer is signalling that your
   statement fits the existing idiom and should not introduce a new one.

(In the Mathlib version pinned by this project the `…Bot` member of that pair still has its former
name `ciSup_mono'`; the two are checked to be the same statement in the Lean file.)

## 4. One thing to reply to the reviewer: here the `'` version is not a second lemma

For the template pair, the primed version is genuinely stronger: `ciSup_mono_of_forall_exists`
compares two *different* families, and for empty `ι` its left-hand side `sSup ∅` need not be below
the right-hand side. That is why both exist.

For the diagonal collapse both sides are `sSup ∅` simultaneously when `ι` is empty, so
`[Nonempty ι]` can simply be dropped from the `ConditionallyCompleteLattice` version:

```lean
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
```

Once it is dropped, `ciSup₂_eq_ciSup_diagonal'` is *literally the same statement*, specialised along
`ConditionallyCompleteLinearOrderBot → ConditionallyCompleteLattice` (checked in the Lean file: the
`…Bot` statement is closed by `exact ciSup₂_eq_ciSup_diagonal f hf h`, and the two proof terms are
`rfl`-equal). Suggested reply: add the conditionally complete version without `[Nonempty ι]`, and
say that this makes the `…Bot` copy redundant — or add it anyway as a one-line alias if the reviewer
prefers the symmetry with the neighbouring pair. Both forms are in the Lean file, so you can post
either.

## 5. Callers to quote, so the addition is not an isolated convenience lemma

* `Cardinal.ciSup_add_ciSup_diagonal` — `(⨆ i, f i) + ⨆ j, g j = ⨆ k, f k + g k` under the same
  cofinality hypothesis; the `Cardinal` analogue of `ENNReal.iSup_add_iSup`. `Cardinal` is a
  `ConditionallyCompleteLinearOrderBot` and has no greatest element, so this caller cannot be served
  by the complete-lattice lemma (also checked).
* `ℝ≥0` / `ℝ`: monotone doubly indexed families with a bounded diagonal, cofinality met by
  `k = max i j`.
* The original `ℕ∞`/`ℝ≥0∞` call sites are still served — the conditionally complete lemma applies to
  them too, with `OrderTop.bddAbove` discharging the side condition — but there the complete-lattice
  version is the better statement, so keep both.

## 6. Concretely, what to add to the PR

In `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`, right after
`ciSup_mono_of_forall_exists`:

```lean
theorem ciSup₂_eq_ciSup_diagonal [ConditionallyCompleteLattice α] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  -- The central fact: every entry is below the diagonal supremum, `f i j ≤ ⨆ k, f k k`.
  have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
    let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hf k)
  have hrow : ∀ i, BddAbove (range (f i)) := fun i ↦ ⟨_, forall_mem_range.2 (hle i)⟩
  have hcol : BddAbove (range fun i ↦ ⨆ j, f i j) :=
    ⟨_, forall_mem_range.2 fun i ↦ ciSup_le (hle i)⟩
  exact le_antisymm (ciSup_le fun i ↦ ciSup_mono_of_forall_exists hf (h i))
    (ciSup_le fun k ↦ le_ciSup_of_le hcol k (le_ciSup (hrow k) k))
```

plus, if the reviewer still wants it, the `'` copy in the
`ConditionallyCompleteLinearOrderBot` section (same statement, `ciSup_le'` for `ciSup_le`), and the
`Cardinal` caller in `Mathlib/SetTheory/Cardinal/Arithmetic.lean`.
