# What to put in the two Mathlib PRs

## Short recommendation

Yes, the underlying contributions are meaningful, but the proposed second PR is too broad as written. The clearest review story is:

1. **PR 1: diagonal collapse in complete lattices**, with three concrete refactors.
2. **PR 2: the conditionally complete analogue**, with the Cardinal application.

The `sSup`/`sInf` cofinal-family API is valid and useful, but it is a second theme. Either leave it out initially or send it as a small third PR. Do not put the originally proposed `ciInf_mono'` statement into a PR: its assumptions are on the wrong sides. A corrected version is given below and machine-checked in the project.

## PR 1 — complete-lattice diagonal collapse

### Title

`Order: add diagonal iSup/iInf lemmas`

### Main declaration

Put beside `iSup₂_mono'` in `Mathlib/Order/CompleteLattice/Basic.lean`:

```lean
@[to_dual iInf₂_eq_iInf_diagonal]
theorem iSup₂_eq_iSup_diagonal {α : Type*} {ι : Sort*}
    [CompleteSemilatticeSup α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k
```

This is the strongest part of the proposal: it names a standard order-theoretic move and directly removes duplicated local lattice reasoning.

Optionally include the more general mutual-cofinality lemma beside `iSup_mono'`:

```lean
@[to_dual]
theorem iSup_eq_iSup_of_forall_exists_le ...
```

It is valid, but the diagonal lemma is the declaration with the clearest demonstrated reuse. The diagonal lemma can also be proved from the general lemma, so including both is reasonable if reviewers prefer a small API ladder.

### Required refactors demonstrating reuse

Refactor these existing declarations in the same PR:

- `ENat.iSup_add_iSup`;
- `ENNReal.iSup_add_iSup`;
- `ENNReal.iInf_add_iInf` using the generated dual.

After distributing addition through the indexed suprema/infima, each proof ends with one application of the diagonal lemma. Checked examples are in `RequestProject/CompleteLatticeContributions.lean`:

```lean
rw [ENat.iSup_add]
simp_rw [ENat.add_iSup]
exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h
```

The ENNReal supremum proof is identical apart from the namespace. The infimum proof is:

```lean
rw [ENNReal.iInf_add]
simp_rw [ENNReal.add_iInf]
exact iInf₂_eq_iInf_diagonal (fun i j ↦ f i + g j) h
```

These are the 2–3 simplifications that make the PR persuasive.

### What not to mix into PR 1

The set-level equalities

```lean
sSup_eq_sSup_of_isCofinalFor
sInf_eq_sInf_of_isCoinitialFor
```

are valid and predictably named, but they do not simplify the three cited ENat/ENNReal proofs as directly as the diagonal lemma does. Adding them makes the PR look like a general collection of cofinality conveniences rather than one extraction motivated by duplicate proofs. Keep them for a separate API PR unless a maintainer explicitly requests them together.

## PR 2 — conditionally complete diagonal collapse

### Title

`Order: add conditionally complete diagonal iSup lemma`

### Main declarations

Put beside `ciSup_mono'` in `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`:

```lean
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*}
    [ConditionallyCompleteLattice α] [Nonempty ι]
    (f : ι → ι → α) (hf : BddAbove (Set.range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k
```

and the empty-index convenience for structures with bottom:

```lean
theorem ciSup₂_eq_ciSup_diagonal' {α : Type*} {ι : Sort*}
    [ConditionallyCompleteLinearOrderBot α]
    (f : ι → ι → α) (hf : BddAbove (Set.range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k
```

The primed theorem should simply split on `Nonempty ι`, call the first theorem in the nonempty case, and simplify in the empty case.

### Concrete downstream contribution

In `Mathlib/SetTheory/Cardinal/Arithmetic.lean`, add:

```lean
theorem Cardinal.ciSup_add_ciSup_diagonal {ι : Type} [Nonempty ι]
    (f g : ι → Cardinal)
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k
```

No explicit boundedness hypotheses are needed here: `Cardinal.bddAbove_range` supplies them for a small index type. The checked proof is essentially:

```lean
rw [Cardinal.ciSup_add_ciSup f (Cardinal.bddAbove_range f)
  g (Cardinal.bddAbove_range g)]
exact ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j)
  (Cardinal.bddAbove_range fun k ↦ f k + g k) h
```

This application gives PR 2 a concrete reason to exist instead of presenting an isolated order lemma.

## Corrections to the follow-up list

### The proposed `ciInf_mono'` is not correct as stated

The proposal said:

```lean
[Nonempty ι]
(hg : BddBelow (Set.range g))
(h : ∀ i', ∃ i, f i ≤ g i')
```

For proving `⨅ i, f i ≤ ⨅ i', g i'`, conditional infimum elimination needs:

- `Nonempty ι'`, because the **right-hand** infimum is introduced with `le_ciInf`;
- `BddBelow (Set.range f)`, because the **left-hand** infimum is compared to a selected `f i` using `ciInf_le`.

The corrected theorem is:

```lean
theorem ciInf_mono'_corrected {α : Type*} {ι ι' : Sort*}
    [ConditionallyCompleteLattice α] [Nonempty ι']
    {f : ι → α} {g : ι' → α}
    (hf : BddBelow (Set.range f))
    (h : ∀ i', ∃ i, f i ≤ g i') :
    ⨅ i, f i ≤ ⨅ i', g i'
```

Before proposing a final upstream name, compare this corrected signature against the intended dual of the relevant conditional-supremum theorem; the current `ciSup_mono'` in Mathlib is in the `ConditionallyCompleteLinearOrderBot` section, whose bottom element changes the empty-family behavior.

### The conditional set-cofinality lemmas are valid but should be separate

The four `csSup`/`csInf` comparison and equality lemmas are machine-checked in the example file. They form a coherent API contribution of their own:

- `csSup_le_csSup_of_isCofinalFor`;
- `csSup_eq_csSup_of_isCofinalFor`;
- `csInf_le_csInf_of_isCoinitialFor`;
- `csInf_eq_csInf_of_isCoinitialFor`.

Suggested title for a later PR:

`Order: compare conditional suprema of cofinal sets`

That PR can place the one-sided comparison near `csSup_le_csSup` in `ConditionallyCompleteLattice/Basic.lean`, generate or prove the infimum dual, and derive both equalities by antisymmetry. It is meaningful, but bundling it with diagonal indexed suprema weakens the focused duplicate-removal narrative.

## Final assessment

- **PR 1 is meaningful and ready in concept**, especially if it contains the diagonal lemma, its dual, and the three ENat/ENNReal refactors.
- **PR 2 is meaningful after narrowing it** to the conditional diagonal lemmas plus the Cardinal application.
- **Do not submit the proposed `ciInf_mono'` unchanged.**
- **Move the `sSup`/`sInf` and `csSup`/`csInf` cofinality families to a separate PR** unless maintainers ask for a larger cofinality API.

All theorem prototypes and example refactors discussed here are implemented without placeholders in `RequestProject/CompleteLatticeContributions.lean`.
