# Reusable duplicated proof pattern found in mathlib

## Candidate

```lean
theorem iSup₂_eq_iSup_diagonal {α : Type*} {ι : Sort*} [CompleteLattice α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k
```

This is the weakest clear common statement behind the duplicated proofs: it only requires a
complete lattice and a cofinality condition for the diagonal. In particular, it does not mention
addition, monotonicity, `ENat`, or `ENNReal`. The name follows existing indexed-supremum names such
as `iSup₂_le` and describes both sides of the equality.

## Existing proofs simplified

The same seven-line argument currently occurs in:

1. `Mathlib/Data/ENat/Lattice.lean`, lemma `ENat.iSup_add_iSup` (around line 223).
2. `Mathlib/Data/ENNReal/Operations.lean`, lemma `ENNReal.iSup_add_iSup` (around line 690).

Both existing proofs:

```lean
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk
```

can instead expose their shared order-theoretic step directly:

```lean
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENat.iSup_add, ENat.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h
```

and, respectively:

```lean
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENNReal.iSup_add, ENNReal.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h
```

`RequestProject/Main.lean` contains a checked implementation of the generic lemma and checked
versions of both replacement proofs.

## Suggested upstream shape

Place the generic lemma near `iSup₂_mono'` in `Mathlib/Order/CompleteLattice/Basic.lean`, then replace
the two duplicated proofs above. This is one small order lemma plus two callers, with no new
abstraction or framework.
