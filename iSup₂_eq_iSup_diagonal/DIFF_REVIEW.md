# Review of the diagonal `iSup`/`iInf` diff

## Verdict

The extracted order-theoretic lemma is a good contribution and the three call sites are the right reuse examples. The diff should **not be merged as written**, however: both supremum refactors have correctness/elaboration issues. The infimum refactor is sound.

## Blocking issues

### 1. `ENNReal.iSup_add_iSup` rewrites with an `ENat` theorem

In `Mathlib/Data/ENNReal/Operations.lean`, the proposed proof starts with

```lean
rw [ENat.iSup_add]
simp_rw [ENat.add_iSup]
```

but the terms have type `ℝ≥0∞`, not `ℕ∞`. These must be

```lean
rw [ENNReal.iSup_add]
simp_rw [ENNReal.add_iSup]
```

This is a hard elaboration error, not merely a namespace/style issue.

### 2. Both `iSup` refactors drop the necessary empty-index case

`ENat.iSup_add`, `ENat.add_iSup`, `ENNReal.iSup_add`, and `ENNReal.add_iSup` require a `[Nonempty ι]` instance. The hypothesis

```lean
h : ∀ i j, ∃ k, f i + g j ≤ f k + g k
```

does not imply `Nonempty ι`: it is vacuously true when `ι` is empty. The new diagonal lemma itself works for an empty index type, but the distribution rewrites used immediately before it do not.

Consequently, retain the existing split in both supremum proofs:

```lean
  cases isEmpty_or_nonempty ι
  · simp
  · rw [ENat.iSup_add]
    simp_rw [ENat.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h
```

and, for `ENNReal`, use the same proof with the namespace changed:

```lean
  cases isEmpty_or_nonempty ι
  · simp
  · rw [ENNReal.iSup_add]
    simp_rw [ENNReal.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h
```

Using the more explicit existing empty-case line (`simp only [iSup_of_empty, bot_eq_zero, zero_add]`) is also fine.

## The generic lemma

The statement has the right strength:

```lean
@[to_dual iInf₂_eq_iInf_diagonal]
theorem iSup₂_eq_iSup_diagonal [CompleteSemilatticeSup α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k
```

In particular:

- it uses only `CompleteSemilatticeSup`, rather than unnecessarily requiring a complete lattice;
- its hypothesis is exactly one-sided cofinality of the diagonal;
- the generated dual has the expected coinitiality hypothesis;
- it does not require `Nonempty ι`, and equality is valid for the empty type.

The submitted proof is valid in the tested environment, but it is more implementation-level than the surrounding API: it unfolds `iSup` into `sSup (Set.range ...)` and manually manipulates range witnesses. That is maintainable, but it obscures the elementary order argument. A shorter high-level proof would be preferable if it can be made compatible with `to_dual` at this weak typeclass level. If not, the submitted proof is acceptable; preserving the weak statement matters more than shortening its implementation.

Minor naming cleanup inside that proof would help: use `k` consistently rather than `k₂` and `k₀`, since there is no collision requiring numbered names.

## `ENNReal.iInf_add_iInf`

This refactor is correct as proposed:

```lean
  rw [ENNReal.iInf_add]
  simp_rw [ENNReal.add_iInf]
  exact iInf₂_eq_iInf_diagonal (fun i j ↦ f i + g j) h
```

Unlike the supremum distribution lemmas, these `ENNReal` infimum distribution lemmas do not require `Nonempty ι`, so no case split was lost.

## Style issue

The replacement body in `Mathlib/Data/ENat/Lattice.lean` is indented by four spaces after `:= by`; Mathlib style here uses two:

```lean
lemma ... := by
  rw [...]
  ...
```

## Recommended corrected patch shape

Keep the new complete-semilattice lemma and its generated dual. Apply these three downstream bodies:

```lean
-- ENat
by
  cases isEmpty_or_nonempty ι
  · simp
  · rw [ENat.iSup_add]
    simp_rw [ENat.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h

-- ENNReal supremum
by
  cases isEmpty_or_nonempty ι
  · simp
  · rw [ENNReal.iSup_add]
    simp_rw [ENNReal.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h

-- ENNReal infimum
by
  rw [ENNReal.iInf_add]
  simp_rw [ENNReal.add_iInf]
  exact iInf₂_eq_iInf_diagonal (fun i j ↦ f i + g j) h
```

Machine-checked versions of the generic lemma, generated dual, and these corrected reuse examples are in `RequestProject/CompleteLatticeContributions.lean`.
