# Code to submit for the ENat and ENNReal callers

These caller changes assume that `iSup₂_eq_diagonal` has been added to
`Mathlib/Order/CompleteLattice/Basic.lean` with
`@[to_dual iInf₂_eq_diagonal]`.

## `Mathlib/Data/ENat/Lattice.lean`

Replace the proof of `ENat.iSup_add_iSup` with:

```lean
lemma iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · simp_rw [ENat.iSup_add, ENat.add_iSup]
    exact iSup₂_eq_diagonal (fun i j ↦ f i + g j) h
```

## `Mathlib/Data/ENNReal/Operations.lean`: supremum

Replace the proof of `ENNReal.iSup_add_iSup` with:

```lean
lemma iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · simp_rw [ENNReal.iSup_add, ENNReal.add_iSup]
    exact iSup₂_eq_diagonal (fun i j ↦ f i + g j) h
```

## `Mathlib/Data/ENNReal/Operations.lean`: infimum

Replace the proof of `ENNReal.iInf_add_iInf` with:

```lean
theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) :
    iInf f + iInf g = ⨅ a, f a + g a := by
  cases isEmpty_or_nonempty ι
  · simp only [iInf_of_empty, top_add]
  · simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
    exact iInf₂_eq_diagonal (fun i j ↦ f i + g j) h
```

The explicit empty-index branch is needed for each supremum proof because addition does not
preserve the empty supremum in the same way as a nonempty one. The ENNReal infimum proof likewise
keeps an explicit empty-index branch. In each nonempty branch, distributing addition turns the
left side into the doubly indexed extremum, after which the generic diagonal lemma closes the goal.

Submit all three caller replacements together with the generic lemma and its generated dual. There
is no corresponding `ENat.iInf_add_iInf` caller.
