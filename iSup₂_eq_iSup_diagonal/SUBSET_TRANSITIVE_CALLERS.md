# Scan for genuine transitive callers of the cofinal-subset `sSup` lemma

## Bottom line

Yes: there is a mathematically natural intermediate statement, not just a wrapper invented to
increase dependency depth.

```lean
sSup equality for a cofinal subset
        ↓
indexed cofinal-subfamily / cofinal-reindexing equality
        ↓
├─ diagonal equality
├─ monotone subsequence equality
├─ antitone subsequence equality
├─ monotone cofinal-map equality
└─ dropping bottom-valued indices
```

The strongest intermediate form found is:

```lean
theorem iSup_comp_eq_of_forall_exists_le
    [CompleteSemilatticeSup α] (f : β → α) (s : ι → β)
    (hcof : ∀ b, ∃ i, f b ≤ f (s i)) :
    ⨆ i, f (s i) = ⨆ b, f b
```

It follows from the proposed subset lemma by applying it to
`range (f ∘ s) ⊆ range f`; the reverse cofinality is exactly `hcof`. This is a recurring concept:
cofinal reindexing preserves a supremum.

## What was scanned

The pinned checkout contains 7,648 Lean files. I used several complementary searches:

1. exact uses of `IsCofinalFor`, `.isCofinalFor`, subset/cofinal combinations, and the existing
   `sSup_le_sSup_of_isCofinalFor`;
2. multiline searches for `le_antisymm` proofs using `iSup_mono'` in both directions;
3. theorem-name searches for `iSup` with `comp`, `range`, `image`, `subtype`, `restrict`, and
   subsequence vocabulary;
4. searches for subtype-indexed suprema and proofs that remove or restrict indices;
5. dual checks for the corresponding `iInf` pattern.

Exact `IsCofinalFor` usage remains sparse: outside its API files, the existing one-way `sSup`
lemma has only the filtration use previously identified. The productive search was therefore for
*proof shape* rather than predicate spelling.

## Existing proofs the intermediate lemma can simplify

### 1. `iSup_eq_iSup_subseq_of_monotone` — strong caller

`Topology/Order/MonotoneConvergence.lean:308` currently proves equality with two explicit
`iSup_mono'` branches. Its first branch establishes that every `f i` is dominated by some
`f (φ j)`; the reverse range inclusion is automatic. It becomes one application of the cofinal
reindexing lemma after constructing the eventual witness.

### 2. `iSup_eq_iSup_subseq_of_antitone` — strong caller

`Topology/Order/MonotoneConvergence.lean:316` repeats exactly the same shape at `atBot` with an
antitone function. It gets the same one-application refactor. Their two existing `iInf` duals then
benefit transitively.

### 3. The diagonal lemma — conceptually strong, with a generality caveat

After rewriting the double supremum as a supremum over `ι × ι`, use the diagonal map
`k ↦ (k, k)`. Its cofinality hypothesis is precisely the hypothesis of the cofinal-reindexing
lemma. This establishes the intended chain to the three ENat/ENNReal addition callers.

Caveat: Mathlib's convenient `iSup_prod'` reshaping is for `ι : Type*`, whereas the direct diagonal
lemma can be stated for `ι : Sort*`. Thus this is excellent conceptual/API reuse, but upstream may
prefer retaining the direct proof to preserve maximal universe generality.

### 4. `Monotone.iSup_comp_eq` — exact concept, but already concise

`Order/CompleteLattice/Basic.lean:508` is already cofinal reindexing under an order-level
cofinality hypothesis and monotonicity. It is an immediate corollary of the value-level statement.
This is strong evidence that the concept and naming are genuine, but weak evidence for changing
that proof: its current body is already one short `le_antisymm`.

The new statement should therefore be named to sit predictably beside this theorem, rather than
creating a competing unexplained API. Possible name: `iSup_comp_eq_of_forall_exists_le`.

### 5. `iSup_ne_bot_subtype` — real but only partial simplification

`Order/CompleteLattice/Basic.lean:1144` removes indices where `f i = ⊥`. This is another cofinal
subfamily. The generic lemma replaces the two supremum-comparison steps, but the proof still needs
the existing all-bottom case split to produce an index in the restricted subtype. It is a genuine
caller, though not as clean as the two subsequence results.

## Assessment of the proposed chain

A defensible chain is:

```text
sSup_eq_sSup_of_subset_of_isCofinalFor
  → iSup_comp_eq_of_forall_exists_le
    → iSup_eq_iSup_subseq_of_monotone
    → iSup_eq_iSup_subseq_of_antitone
    → iSup₂_eq_diagonal (modulo Type/Sort generality)
```

This meets the requested “one intermediate caller with more than two callers” criterion: the
intermediate theorem has at least four genuine specializations, including two clean existing
proof simplifications and the diagonal concept.

However, there are two review risks:

1. Mathlib already has `Monotone.iSup_comp_eq`, so reviewers may prefer generalizing or pairing
   with that API rather than adding a nearly synonymous theorem.
2. The mutual indexed-family equality
   `iSup_eq_iSup_of_forall_exists_le` is more symmetric and directly simplifies the two subsequence
   proofs. If the only goal is the cleanest small PR, it may still be preferable to the longer
   subset → range → composition dependency chain.

## Recommendation

The evidence is now substantially better than “the subset lemma has no caller.” If proposing the
subset lemma, present the indexed cofinal-reindexing theorem as its natural range corollary and show
the two subsequence refactors plus the diagonal derivation. Do **not** claim all five candidates are
equally compelling: lead with the two subsequence proofs; use the diagonal as structural evidence;
mention `Monotone.iSup_comp_eq` as API precedent; keep `iSup_ne_bot_subtype` optional.

For the smallest, lowest-risk upstream contribution, the earlier diagonal-only PR with its three
direct ENat/ENNReal callers remains cleaner. The longer chain is credible, but is best submitted as
a coherent cofinal-reindexing API PR rather than added solely to justify the subset wrapper.

## Machine-checked artifact

`RequestProject/SubsetTransitiveCallers.lean` checks the following without `sorry`/`admit`:

- the cofinal-subset `sSup` equality;
- the indexed cofinal-subfamily corollary;
- the cofinal-composition specialization;
- refactored diagonal, monotone-subsequence, antitone-subsequence,
  `Monotone.iSup_comp_eq`, and `iSup_ne_bot_subtype` proofs.
