# Grep results and PR recommendation for the cofinal-`sSup` lemmas

## Executive recommendation

The highest-leverage split is:

### PR 1 — diagonal lemma with demonstrated reuse

Add:

- `iSup₂_eq_diagonal`;
- its dual `iInf₂_eq_diagonal`.

Simplify the three existing duplicate proofs:

1. `ENat.iSup_add_iSup`;
2. `ENNReal.iSup_add_iSup`;
3. `ENNReal.iInf_add_iInf`.

This is the strongest first PR because it has the clearest contribution shape: one small generic lemma pair immediately replaces three local proofs. The third caller is important: the opportunity is not merely the two supremum proofs; the ENNReal infimum proof is the same pattern on the dual side.

### PR 2 — general cofinal-family equalities

Add:

- `sSup_eq_sSup_of_isCofinalFor`;
- `sInf_eq_sInf_of_isCoinitialFor`;
- optionally the indexed range-level pair
  `iSup_eq_iSup_of_forall_exists_le` / `iInf_eq_iInf_of_forall_exists_le`.

Use the indexed theorem to simplify existing cofinal-reindexing proofs, especially:

- `iSup_eq_iSup_subseq_of_monotone`;
- `iSup_eq_iSup_subseq_of_antitone`;
- potentially `Monotone.iSup_comp_eq` (although its current proof is already very short).

Do **not** initially add
`sSup_eq_sSup_of_subset_of_isCofinalFor` unless a reviewer asks for it. It is mathematically natural and has a checked one-line proof, but the source search found no existing complete-lattice caller that it directly simplifies. It is therefore a convenience wrapper without demonstrated reuse, while the mutual-cofinality theorem is the foundational API result.

If a reviewer explicitly asks that the first PR be organized around `IsCofinalFor`, combining the mutual-cofinality pair with PR 1 is defensible. Otherwise, the two-PR split above gives a tighter first diff and avoids making the diagonal contribution look over-generalized.

## The two set-level statements

The foundational statement is:

```lean
theorem sSup_eq_sSup_of_isCofinalFor
    [CompleteSemilatticeSup α] {s t : Set α}
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) :
    sSup s = sSup t
```

Its proof packages the two existing inequalities:

```lean
le_antisymm
  (sSup_le_sSup_of_isCofinalFor hst)
  (sSup_le_sSup_of_isCofinalFor hts)
```

The subset statement is a direct corollary because `hst.isCofinalFor` turns `s ⊆ t` into
`IsCofinalFor s t`:

```lean
theorem sSup_eq_sSup_of_subset_of_isCofinalFor
    [CompleteSemilatticeSup α] {s t : Set α}
    (hst : s ⊆ t) (hcf : IsCofinalFor t s) :
    sSup s = sSup t :=
  sSup_eq_sSup_of_isCofinalFor hst.isCofinalFor hcf
```

This formulation and proof have been checked in `Main.lean`.

The manually stated dual has the orientation:

```lean
theorem sInf_eq_sInf_of_isCoinitialFor
    [CompleteSemilatticeInf α] {s t : Set α}
    (hst : IsCoinitialFor s t) (hts : IsCoinitialFor t s) :
    sInf s = sInf t :=
  le_antisymm
    (sInf_le_sInf_of_isCoinitialFor hts)
    (sInf_le_sInf_of_isCoinitialFor hst)
```

The reversed order of `hts` and `hst` in the two inequalities is intentional.

## Exact source-search results

The search covered all Lean source files in the checked-out Mathlib tree (7,648 files).

### Existing `IsCofinalFor` API and uses

`IsCofinalFor` occurs in only these Mathlib files:

- `Mathlib/Order/Bounds/Defs.lean` — definition;
- `Mathlib/Order/Bounds/Basic.lean` — `.of_subset`, `.rfl`, `.trans`, monotonicity helpers, and upper-bound behavior;
- `Mathlib/Order/Bounds/Image.lean` — image lemmas;
- `Mathlib/Order/CompleteLattice/Basic.lean` — `sSup_le_sSup_of_isCofinalFor`.

Outside those API files, the only direct use of
`sSup_le_sSup_of_isCofinalFor` is:

- `Mathlib/RingTheory/Filtration.lean`, in the proof that the `sSup` of a family of filtrations is again a filtration.

That use proves only a one-way monotonicity condition. It is **not** an equality and is not a caller for either proposed equality theorem.

Consequently:

- there are no current exact callers of `sSup_eq_sSup_of_isCofinalFor` (the theorem does not yet exist);
- there is no existing proof combining `sSup_le_sSup` with
  `sSup_le_sSup_of_isCofinalFor` that the subset wrapper would directly replace;
- the subset wrapper currently has zero demonstrated complete-lattice callers.

### Strong precedent in the conditionally complete API

Mathlib already has the analogous, more laborious conditionally complete theorem:

```lean
csSup_eq_csSup_of_forall_exists_le
```

in `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`, together with its infimum dual. Its hypotheses are exactly mutual cofinality written out rather than named with `IsCofinalFor`.

Its direct uses are:

- `sSup_iUnion_Iic` in the same file;
- `Finset.ciSup_eq_max'_image` in
  `Mathlib/Order/ConditionallyCompleteLattice/Finset.lean`.

There are also specialized subset-plus-cofinality image lemmas:

- `MonotoneOn.csInf_eq_of_subset_of_forall_exists_le`;
- `MonotoneOn.csSup_eq_of_subset_of_forall_exists_le`.

Their direct callers are the two slope lemmas in
`Mathlib/Analysis/Convex/Deriv.lean`.

This is strong naming/API precedent for the **mutual-cofinality equality**, but it does not create a caller for the proposed complete-lattice subset wrapper: these results need conditionally complete boundedness and monotonicity machinery.

## Caller search for the indexed mutual-cofinality theorem

Searching for equality proofs that apply `iSup_mono'` in both directions found two especially clean candidates:

- `iSup_eq_iSup_subseq_of_monotone`;
- `iSup_eq_iSup_subseq_of_antitone`;

both in `Mathlib/Topology/Order/MonotoneConvergence.lean`.

Each currently has the shape:

```lean
le_antisymm
  (iSup_mono' fun i => ...)
  (iSup_mono' fun i => ⟨φ i, le_rfl⟩)
```

This is precisely what
`iSup_eq_iSup_of_forall_exists_le` packages. Their `iInf` counterparts are already obtained by duality from these supremum results, so simplifying the two supremum proofs also benefits the two infimum theorems transitively.

Other related candidates are:

- `Monotone.iSup_comp_eq` in `Order/CompleteLattice/Basic.lean`, which packages cofinal reindexing but is already a concise one-line `le_antisymm` proof;
- `iSup_ne_bot_subtype` in the same file, which drops bottom-valued indices and uses one generic cofinal inequality plus a case split;
- two Krull-dimension proofs in `RingTheory/Ideal/Height.lean`, which use `iSup_mono'` in both directions but contain substantial domain-specific work and are not clean drop-in callers.

Thus the best evidence for an indexed mutual-cofinality PR is the two subsequence theorems, not the subset `sSup` wrapper.

## Caller search for the diagonal pair

The three direct duplicate proofs are:

| Generic direction | Existing theorem | File |
|---|---|---|
| supremum | `ENat.iSup_add_iSup` | `Mathlib/Data/ENat/Lattice.lean` |
| supremum | `ENNReal.iSup_add_iSup` | `Mathlib/Data/ENNReal/Operations.lean` |
| infimum | `ENNReal.iInf_add_iInf` | `Mathlib/Data/ENNReal/Operations.lean` |

The ENat and ENNReal supremum proofs share the same diagonal-cofinal argument. The ENNReal infimum theorem is its exact order dual. There is no corresponding `ENat.iInf_add_iInf` theorem.

Downstream uses of these add lemmas (for example in ENat/ENNReal big operators and Lebesgue integration) benefit transitively, but should not be edited merely to increase the PR's caller count.

## Why not put every theorem in one PR?

The logical dependency diagram is real:

```text
mutual cofinality of sets
        ↓
mutual cofinality of indexed ranges
        ↓
cofinal diagonal
```

But logical generality is not the only PR-design criterion:

- the diagonal pair has three immediate duplicate callers;
- the indexed pair has at least two clean reindexing callers;
- the mutual set pair fills a natural API gap and matches conditionally complete precedent;
- the subset wrapper has no caller found by the source search.

Bundling all four layers would add several public names and mix two motivations: eliminating duplicated diagonal proofs and completing the cofinality API. Splitting those motivations makes review easier. The subset wrapper can be added later once an actual caller appears.

## Suggested final PR order

1. Submit `iSup₂_eq_diagonal` / `iInf₂_eq_diagonal` with the three add callers.
2. Submit `sSup_eq_sSup_of_isCofinalFor` / `sInf_eq_sInf_of_isCoinitialFor`, plus the indexed mutual-cofinality pair if desired, with the two subsequence simplifications.
3. Add `sSup_eq_sSup_of_subset_of_isCofinalFor` only in response to a concrete use or reviewer preference.

This maximizes demonstrated reuse while keeping every public declaration predictable and independently justified.
