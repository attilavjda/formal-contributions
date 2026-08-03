# Second review round: is the pattern exhausted, and what would a third reviewer ask for?

This note answers the follow-up questions:

- *Are the two callers (`ENat.iSup_add_iSup`, `ENNReal.iSup_add_iSup`) exhaustive?*
- *What further additions/refactors of the same "cofinal ⇒ equal extremal bound" pattern exist?*
- *Is there a more structural home (cofinality predicate / categorical bridge)?*

Everything labelled **confirmed** below was checked against the pinned Mathlib
(`v4.28.0`, this project's dependency) by reading the source and, where a new lemma is proposed,
compiling it in `Main.lean` (which builds with no `sorry`/`admit`).

---

## 1. The two callers are **not** exhaustive — there is a third

**Confirmed.** `ENNReal.iInf_add_iInf` (`Mathlib/Data/ENNReal/Operations.lean:564`) is the
infimum dual of `ENNReal.iSup_add_iSup` and repeats the identical diagonal argument:

```lean
theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]
```

It is simplified by the **already generated** dual lemma `iInf₂_eq_diagonal` (the `@[to_dual]`
partner of `iSup₂_eq_diagonal`), exactly mirroring the two supremum callers:

```lean
  cases isEmpty_or_nonempty ι
  · simp only [iInf_of_empty, top_add]
  · simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
    exact iInf₂_eq_diagonal (fun i j ↦ f i + g j) h
```

Checked in `Main.lean` as `ennreal_iInf_add_iInf_via_diagonal`.

Asymmetry worth noting: there is **no** `ENat.iInf_add_iInf` — `Data/ENat/Lattice.lean` has only
the supremum version. So the third caller is ENNReal-only, and the honest count is **three**
duplicate callers (two sup, one inf), all collapsing to the sup lemma and its `to_dual` dual.

Not callers, but part of the same file cluster (do **not** fold them into this PR): the
`*_of_monotone` variants (`iSup_add_iSup_of_monotone`, `iInf_add_iInf_of_monotone` for both ENat and
ENNReal) are derived *from* the base lemmas via `IsDirectedOrder`/`IsCodirectedOrder`, and the
`BigOperators` files reuse the base lemmas — all benefit transitively once the base callers are
simplified.

---

## 2. The most structural home already exists: `IsCofinalFor`

The earlier round recommended *against* introducing a cofinality predicate, calling it "new
framework". That recommendation is **superseded**: the predicate already exists in Mathlib.

**Confirmed API (all present):**

- `IsCofinalFor s t := ∀ ⦃a⦄, a ∈ s → ∃ b ∈ t, a ≤ b`  (`Mathlib/Order/Bounds/Defs.lean:59`)
- `IsCofinalFor.of_subset`, `IsCofinalFor.rfl`, `IsCofinalFor.trans`  (`Order/Bounds/Basic.lean`)
- `@[to_dual]` dual predicate `IsCoinitialFor`
- `sSup_le_sSup_of_isCofinalFor` (`Order/CompleteLattice/Basic.lean:54`) — the `≤` half
- `sInf_le_sInf_of_isCoinitialFor` (`Order/CompleteLattice/Basic.lean:68`) — the dual `≤` half

**Confirmed missing:** the mutual-cofinality **equality** on either side. That is exactly the gap
this contribution fills, and it is the "add the equality next to the existing inequality" shape
reviewers like best. Added and checked in `Main.lean`:

```lean
theorem sSup_eq_sSup_of_isCofinalFor [CompleteSemilatticeSup α] {s t : Set α}
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) : sSup s = sSup t :=
  le_antisymm (sSup_le_sSup_of_isCofinalFor hst) (sSup_le_sSup_of_isCofinalFor hts)

theorem sInf_eq_sInf_of_isCoinitialFor [CompleteSemilatticeInf α] {s t : Set α}
    (hst : IsCoinitialFor s t) (hts : IsCoinitialFor t s) : sInf s = sInf t :=
  le_antisymm (sInf_le_sInf_of_isCoinitialFor hts) (sInf_le_sInf_of_isCoinitialFor hst)
```

The indexed lemma `iSup_eq_iSup_of_forall_exists_le` is then a one-line corollary via `Set.range`
(checked as an `example` in `Main.lean`). This reframes the whole contribution: the set-level
predicate lemma is the structural core, and the indexed/diagonal lemmas are its corollaries.

Caveat on dualization: `@[to_dual]` does **not** transport `sSup_eq_sSup_of_isCofinalFor`
automatically, because the underlying `≤`-half lemmas are not themselves `to_dual`-linked in
Mathlib. So the dual is stated manually (one line). This matches what earlier rounds found for the
diagonal lemma's dualization.

---

## 3. What a third reviewer would (and would not) ask for

Sorted by how mechanical the addition is.

### Tier A — cheap siblings, in scope for this PR family (confirmed by source)

| Lemma | Status | Note |
|---|---|---|
| `iInf₂_eq_diagonal` | already generated (`@[to_dual]`) | now has a real caller (§1) |
| `iInf_eq_iInf_of_forall_exists_le` | already generated (`@[to_dual]`) | dual of the indexed core |
| `sSup_eq_sSup_of_isCofinalFor` | **added** here | equality companion of existing `≤` lemma |
| `sInf_eq_sInf_of_isCoinitialFor` | **added** here | dual, stated manually |
| `ennreal_iInf_add_iInf_via_diagonal` | **added** here | the third caller |

### Tier B — genuine gaps, plausible but need care (confirmed observations)

- `ciInf_mono'`: the dual of `ciSup_mono'` (`Order/ConditionallyCompleteLattice/Indexed.lean:523`)
  is **missing** (only `ciSup_mono'` exists; `ciInf_mono` without a prime exists). Not a mechanical
  `to_dual`: `ciSup_mono'` lives in the `ConditionallyCompleteLinearOrderBot` section, and Mathlib
  has **no** `ConditionallyCompleteLinearOrderTop` class, so the dual must be stated over
  `ConditionallyCompleteLattice` with a `Nonempty` index (or via `OrderDual`). Worth its own tiny
  PR rather than folding in here.
- `ciInf₂_eq_ciInf_diagonal` / `...'`: infimum duals of the two conditionally-complete diagonal
  lemmas already in `Main.lean`. Same `Top`-class subtlety; easy to add via `OrderDual` if wanted.
- `csSup_le_csSup_of_isCofinalFor` (+ equality, + duals): the conditionally-complete analogue of
  the §2 set lemmas is **entirely absent** (`grep` finds no `isCofinalFor` usage under
  `Order/ConditionallyCompleteLattice/`). It needs `BddAbove` side conditions, so it is a separate,
  slightly heavier addition — a reasonable follow-up, not part of the minimal PR.

### Tier C — already covered, so nothing to add (confirmed)

- **Cofinal reindexing equality already exists:** `Monotone.iSup_comp_eq`
  (`Order/CompleteLattice/Basic.lean:510`): `(∀ x, ∃ i, x ≤ s i) → ⨆ x, f (s x) = ⨆ y, f y`, with
  dual `Monotone.iInf_comp_eq`. The `≤` halves `iSup_comp_le` / `le_iInf_comp`, and the surjective/
  equiv reindexings `Function.Surjective.iSup_comp`, `Equiv.iSup_comp` are all present. So the
  "cofinal map" family the earlier round flagged as "the closest genuine relative" is in fact
  *already there* as an equality; our diagonal lemma is a different shape (the diagonal map is not
  of the form `f ∘ s` with `f` monotone), so there is nothing to unify.
- **Product/iterated reshaping:** `iSup_prod'`, `iSup_sigma'` (`Order/CompleteLattice/Basic.lean`)
  handle `⨆ i, ⨆ j` ↔ `⨆ (i,j)`; orthogonal to cofinality (used only to derive the diagonal form).

### Tier D — the conceptual home, but **not** a small-lemma target (unchanged assessment)

- **`ENat.iSup_mul_iSup` / `ENNReal`/`NNReal` multiplicative equalities:** confirmed **absent** —
  only `_le` halves exist (`iSup_mul_iSup_le`, `NNReal.iSup_mul_iSup_le`). An equality would need
  extra `≠ ∞` / `BddAbove` side conditions; out of scope, no existing duplicate to collapse.
- **Heyting / frames / complete Boolean algebras / topoi:** these are complete lattices, so the
  complete-lattice lemma already applies unchanged; the distinctively frame-theoretic lemmas are a
  different shape (a binary op distributing over a product-indexed double sup), not the
  cofinal-diagonal collapse. Nothing to add.
- **Category theory / Caramello "bridge" / Morita equivalence:** the genuine generalization of
  "cofinal ⇒ same colimit" is `CategoryTheory.Functor.Final`/`Initial` (final functors induce
  isomorphic colimits). The order lemma is the thin-category (poset) special case. The
  Caramello/Morita idea — "the same invariant read across two presentations of the same theory" —
  is the right *philosophical* framing (cofinality is exactly such a presentation-invariant of the
  colimit), but it is a large independent framework and the order lemma is **not** a mechanical
  corollary of it in Mathlib. It should be cited as lineage in the docstring, not imported as
  machinery. Assessment unchanged from the first round.

---

## 4. Recommendation

1. **Reframe the PR around `IsCofinalFor`.** Lead with `sSup_eq_sSup_of_isCofinalFor` /
   `sInf_eq_sInf_of_isCoinitialFor` as the equality companions of the existing `≤` lemmas (place
   them immediately after `sSup_le_sSup_of_isCofinalFor` in `Order/CompleteLattice/Basic.lean`).
   Keep `iSup_eq_iSup_of_forall_exists_le` and `iSup₂_eq_diagonal` (+ duals) as corollaries.
2. **Simplify all three callers**, not two: `ENat.iSup_add_iSup`, `ENNReal.iSup_add_iSup`, and
   `ENNReal.iInf_add_iInf`.
3. **Defer** the `ciInf_mono'` / conditionally-complete-cofinal (`csSup..._of_isCofinalFor`) gaps to
   a small follow-up PR; note them in the PR description as natural next steps.
4. **Do not** add multiplicative equalities, Heyting-specific lemmas, or any categorical machinery.

All proposed new lemmas are checked in `Main.lean`.
