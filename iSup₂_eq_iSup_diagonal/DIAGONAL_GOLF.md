# Golfing `iSup₂_eq_iSup_diagonal` and its three reuse proofs

All alternatives discussed below are machine-checked in
`RequestProject/DiagonalGolf.lean`.

## Recommendation

For an upstream patch, I would use:

1. the compact `CompleteSemilatticeSup` proof in
   `iSup₂_eq_iSup_diagonal_compact`; and
2. the `simpa only [...] using ...` versions of the three call sites.

This preserves the weakest useful statement, preserves automatic `to_dual`
generation, and makes each reuse proof visibly say: “distribute addition, then
collapse the double supremum/infimum to its diagonal.”

## 1. The generic lemma

### Best compact version without changing the API

The original proof can be shortened while retaining
`[CompleteSemilatticeSup α]` and `@[to_dual]`. The main savings are:

- use `mem_range_self` rather than spelling out `⟨k, rfl⟩` where inference is
  reliable;
- chain inequalities directly with `.trans`;
- avoid intermediate `have` declarations;
- avoid numbered witness names.

The resulting proof is still necessarily somewhat low-level: the familiar
lemmas `iSup_le`, `le_iSup`, `iSup₂_le`, and `le_iSup₂` are stated under
`CompleteLattice`, not merely `CompleteSemilatticeSup`.

```lean
@[to_dual iInf₂_eq_iInf_diagonal]
theorem iSup₂_eq_iSup_diagonal [CompleteSemilatticeSup α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · apply sSup_le
    intro _ hx
    obtain ⟨i, rfl⟩ := hx
    apply sSup_le
    intro _ hx
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨k, hk⟩ := h i j
    exact hk.trans <| le_sSup (mem_range_self k)
  · apply sSup_le
    intro _ hx
    obtain ⟨k, rfl⟩ := hx
    exact (le_sSup (show f k k ∈ range (f k) from mem_range_self k)).trans <|
      le_sSup (show sSup (range (f k)) ∈ range (fun i ↦ sSup (range (f i))) from
        mem_range_self k)
```

The explicit `show` clauses on the reverse inequality are useful rather than
mere verbosity: without them Lean cannot reliably infer which nested range a
`mem_range_self k` witness belongs to.

### Much shorter, but with an unnecessarily strong assumption

If the statement is changed to `[CompleteLattice α]`, the ordinary indexed-sup
API gives a very clean proof:

```lean
by
  exact le_antisymm
    (iSup₂_le fun i j ↦ (h i j).elim fun k hk ↦ le_iSup_of_le k hk)
    (iSup_le fun k ↦ le_iSup_of_le k <| le_iSup (f k) k)
```

This is attractive locally, but I would **not** use it upstream: proof golf is
not worth weakening the theorem's generality.

A tempting compromise is to install
`completeLatticeOfCompleteSemilatticeSup α` locally and use the short proof.
That proof itself checks, but automatic dual generation then becomes awkward:
the local construction and all proof terms must translate coherently to the
infimum side. The direct `sSup` proof is more robust for a `@[to_dual]` theorem.

## 2. The two supremum reuse proofs

The conservative style is already good:

```lean
  cases isEmpty_or_nonempty ι
  · simp
  · rw [ENat.iSup_add]
    simp_rw [ENat.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h
```

A tighter version combines distribution and collapse:

```lean
  cases isEmpty_or_nonempty ι
  · simp
  · simpa only [ENat.iSup_add, ENat.add_iSup] using
      iSup₂_eq_iSup_diagonal (fun i j ↦ f j + g i) fun i j ↦ h j i
```

For `ENNReal`, only the namespace changes:

```lean
  cases isEmpty_or_nonempty ι
  · simp
  · simpa only [ENNReal.iSup_add, ENNReal.add_iSup] using
      iSup₂_eq_iSup_diagonal (fun i j ↦ f j + g i) fun i j ↦ h j i
```

Why transpose the arguments? Simplifying the left side with the distribution
lemmas produces the nested family in the opposite binder order. Since the
indices have the same type, applying the diagonal lemma to
`fun i j ↦ f j + g i` makes the result match definitionally after
simplification. This removes a separate `rw`/`simp_rw` sequence.

The empty-index split **cannot be golfed away** with the current API:
`ENat.iSup_add`, `ENat.add_iSup`, `ENNReal.iSup_add`, and
`ENNReal.add_iSup` require `[Nonempty ι]`, while the cofinality hypothesis is
vacuously true when `ι` is empty.

### Readability tradeoff

The transposition is slightly clever. If minimizing surprise matters more than
line count, keep the original orientation and the three-step proof. If the
surrounding file commonly uses `simpa ... using`, the compact form is still
clear and avoids unrestricted `simp`.

## 3. The infimum reuse proof

This one has the cleanest golf because the ENNReal infimum distribution lemmas
do not require a nonempty index:

```lean
by
  simpa only [ENNReal.iInf_add, ENNReal.add_iInf] using
    iInf₂_eq_iInf_diagonal (fun i j ↦ f j + g i) fun i j ↦ h j i
```

That replaces the current `rw`, `simp_rw`, `exact` sequence with one semantic
step. As above, transposition merely aligns the binder order created by the
simplifier.

## Practical ranking

1. **Best balance:** weak generic lemma with compact `sSup` proof; three
   `simpa only ... using` call sites.
2. **Most explicit/readable:** weak generic lemma; retain `rw`, `simp_rw`,
   `exact` at call sites.
3. **Shortest generic proof:** strengthen to `CompleteLattice`; not recommended
   because it worsens the API solely to shorten implementation code.

In particular, avoid replacing `simpa only` with broad `simp`: the extra few
characters make the normalization contract explicit and reduce brittleness.
