# What to upstream, and in which PR

Companion to `RequestProject/MathlibPR.lean`, which contains every declaration listed
below in Mathlib style, compiling against Mathlib (Lean `v4.28.0`).  That file is
self-contained (`import Mathlib` only) and lives in a `namespace MathlibPR` shim: drop
the shim and each block is the literal PR content.

The guiding idea: **one abstraction, three existing specialisations, then the
conditionally complete version people keep asking for.**  Mathlib already contains three
copies of the same proof — `ENNReal.iSup_add_iSup`, `ENNReal.iInf_add_iInf`,
`ENat.iSup_add_iSup` — and lacks the `Cardinal` analogue entirely, because `Cardinal` is
only *conditionally* complete.  Splitting along that line gives two self-justifying PRs.

| PR | Title | Files touched | Character |
| --- | --- | --- | --- |
| **1** | *feat(Order/CompleteLattice): diagonal collapse for iterated suprema* | `Order/Bounds/Basic`, `Order/CompleteLattice/Basic`, `Data/ENNReal/Operations`, `Data/ENat/Lattice` | new abstraction + de-duplication of 3 existing proofs; **no statement changes** |
| **2** | *feat(Order/ConditionallyCompleteLattice): diagonal collapse, and `Cardinal.ciSup_add_ciSup_diagonal`* | `Order/ConditionallyCompleteLattice/Basic`, `SetTheory/Cardinal/Arithmetic` | the requested `c`-lemmas; depends on PR 1 |
| **3** *(optional)* | *feat(SetTheory/Cardinal): monotone-family suprema; operation-level packaging* | `SetTheory/Cardinal/Arithmetic`, `Order/CompleteLattice/Basic` | convenience corollaries; only if reviewers want them |

Merging order is 1 → 2 → 3; PR 2 needs `iSup₂_eq_iSup_diagonal`'s neighbourhood and the
two `IsCofinalFor` helpers from PR 1, PR 3 needs PR 2's `Cardinal` lemmas.

---

## PR 1 — the abstraction and the three specialisations

### (a) `Mathlib/Order/Bounds/Basic.lean`

Next to `upperBounds_mono_of_isCofinalFor` (currently line ~144), two lemmas that make
`IsCofinalFor` usable for indexed families and transport boundedness:

```lean
@[simp] theorem isCofinalFor_range_iff {f : ι → α} {g : κ → α} :
    IsCofinalFor (range f) (range g) ↔ ∀ i, ∃ j, f i ≤ g j
theorem IsCofinalFor.bddAbove {s t : Set α} (h : IsCofinalFor s t) (ht : BddAbove t) :
    BddAbove s
theorem IsCoinitialFor.bddBelow {s t : Set α} (h : IsCoinitialFor s t) (ht : BddBelow t) :
    BddBelow s
```

Three lines of proof in total.  `IsCofinalFor.bddAbove` is the only one PR 2 needs; the
`range` iff is what keeps the later statements readable.  If a reviewer prefers, (a) can
be split off as a trivial standalone PR, but it is too small to be worth its own review.

### (b) `Mathlib/Order/CompleteLattice/Basic.lean`

Insert after `iSup_comm` (currently line ~630), i.e. in the `iSup₂` neighbourhood:

```lean
theorem iSup_eq_iSup_of_forall_exists_le   -- mutually cofinal families, equal suprema
theorem iInf_eq_iInf_of_forall_exists_le   -- dual, via αᵒᵈ
theorem iSup₂_eq_iSup_of_forall_exists_le  -- ⨆ i, ⨆ j, F i j = ⨆ k, G k
theorem iInf₂_eq_iInf_of_forall_exists_le  -- dual, via αᵒᵈ
theorem iSup₂_eq_iSup_diagonal (F : ι → ι → α) (h : ∀ i j, ∃ k, F i j ≤ F k k) :
    ⨆ i, ⨆ j, F i j = ⨆ k, F k k
theorem iInf₂_eq_iInf_diagonal             -- dual, via αᵒᵈ
```

All six are one- or two-liners (`le_antisymm (iSup_mono' _) (iSup_mono' _)` and
`iSup₂_le`/`le_iSup₂`); the four `iInf` statements are `(α := αᵒᵈ)` applications, so the
mathematical content is two lemmas.  The naming follows
`csSup_eq_csSup_of_forall_exists_le`, which is the existing Mathlib lemma with exactly
this shape.

### (c) The three call sites

Statements are **unchanged**; only proofs shrink.  `RequestProject/MathlibPR.lean`
pins this down: each replacement proof is stated with the current signature and followed
by an `example : @<new> = @<existing> := rfl`, which type-checks only if the statement is
definitionally the old one.

`Mathlib/Data/ENNReal/Operations.lean`, `ENNReal.iSup_add_iSup`:

```lean
-- before: le_antisymm + iSup_add_iSup_le + rcases + le_iSup_of_le (6 lines)
-- after:
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [iSup_add, add_iSup]
    exact iSup₂_eq_iSup_diagonal _ h
```

`ENNReal.iInf_add_iInf` (same file) loses its `calc` block entirely:

```lean
  simp_rw [iInf_add, add_iInf]
  exact iInf₂_eq_iInf_diagonal _ h
```

`Mathlib/Data/ENat/Lattice.lean`, `ENat.iSup_add_iSup`: byte-for-byte the `ENNReal`
`iSup` proof above.

Honest accounting: the call sites lose about 8 lines while (b) adds about 20 lines of
reusable API, so this is not a line-count win.  The argument for the PR is that the three
proofs stop being three independent copies of one lattice-theoretic fact, and that the
fact becomes available on its own (`Cardinal` in PR 2 is the immediate customer;
`MeasureTheory.lintegral_add_measure` is an example of a place that reaches for the
`ENNReal` copy today).  The `cases isEmpty_or_nonempty ι` survives because
`ENNReal.iSup_add` and `ENat.add_iSup` are stated with `[Nonempty ι]`; only the `iInf`
proof, whose inputs `ENNReal.iInf_add`/`ENNReal.add_iInf` have no such hypothesis, becomes
a two-liner.

### (d) Optional in the same PR: two missing multiplicative lemmas

```lean
theorem ENNReal.iSup_mul_iSup [Nonempty ι] (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) :
    iSup f * iSup g = ⨆ i, f i * g i
theorem ENat.iSup_mul_iSup   -- same statement in ℕ∞
```

Both are two lines given (b) (`ENNReal.iSup_mul`, `ENNReal.mul_iSup` and their `ENat`
counterparts already exist), and they are the natural completion of the `iSup_add_iSup`
family.  Drop them if a reviewer wants PR 1 to be pure refactoring.

---

## PR 2 — the conditionally complete lemmas

This is the part that has been requested repeatedly: Mathlib stops at
`Cardinal.ciSup_add_ciSup`, which turns `(⨆ i, f i) + ⨆ j, g j` into the *double*
supremum `⨆ i, ⨆ j, f i + g j`, and every user then has to redo the diagonal collapse by
hand.  The complete-lattice lemma of PR 1 does not apply, since `Cardinal` is only
conditionally complete.

### (a) `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`

Insert after `csSup_eq_csSup_of_forall_exists_le` (currently line ~495):

```lean
theorem ciSup_eq_ciSup_of_forall_exists_le [Nonempty ι] [Nonempty κ] {f : ι → α} {g : κ → α}
    (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (hfg : ∀ i, ∃ j, f i ≤ g j) (hgf : ∀ j, ∃ i, g j ≤ f i) : ⨆ i, f i = ⨆ j, g j
theorem bddAbove_range_curry        -- a row of a product-bounded family is bounded
theorem bddAbove_range_ciSup_curry  -- its row-suprema are bounded
theorem ciSup_prod (hb : BddAbove (range F)) :
    ⨆ p : ι × κ, F p = ⨆ i, ⨆ j, F (i, j)   -- conditionally complete `iSup_prod`
theorem bddAbove_range_uncurry      -- diagonal bounded ⇒ square bounded (uses PR 1(a))
theorem ciSup₂_eq_ciSup_diagonal [Nonempty ι] (F : ι → ι → α)
    (h : ∀ i j, ∃ k, F i j ≤ F k k) (hb : BddAbove (range fun k => F k k)) :
    ⨆ i, ⨆ j, F i j = ⨆ k, F k k
theorem ciInf₂_eq_ciInf_diagonal    -- dual, via αᵒᵈ
```

Structure worth pointing out in the PR description: the argument is the *same two steps*
as in PR 1 — currying, then cofinality — and boundedness is consumed in exactly one
place, `ciSup_prod`.  `ciSup_prod` is independently useful: it is the conditionally
complete counterpart of the existing `iSup_prod`, which Mathlib does not have.

Note for reviewers: in a conditionally complete **linear** order the cofinality step
needs no hypotheses at all (`csSup_eq_csSup_of_forall_exists_le` handles empty and
unbounded sets, since both sides are then the same junk value), so
`ciSup_eq_ciSup_of_forall_exists_le` could additionally be stated hypothesis-free in that
setting.  The general-lattice version above is what `ciSup₂_eq_ciSup_diagonal` needs, and
it keeps the boundedness bookkeeping in one place; the linear-order variant can be added
later if there is demand.

### (b) `Mathlib/SetTheory/Cardinal/Arithmetic.lean`

Right after the existing `Cardinal.ciSup_add_ciSup` / `Cardinal.ciSup_mul_ciSup`:

```lean
protected theorem Cardinal.ciSup_add_ciSup_diagonal (hf : BddAbove (range f))
    (hg : BddAbove (range g)) (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k
protected theorem Cardinal.ciSup_mul_ciSup_diagonal (hf : BddAbove (range f))
    (hg : BddAbove (range g)) (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ k, f k * g k
```

each a `.trans` of the existing double-supremum lemma with `ciSup₂_eq_ciSup_diagonal`,
plus the two boundedness helpers `bddAbove_range_add` (generic: covariant `Add`) and
`bddAbove_range_mul`.  `bddAbove_range_add` is stated for any preordered `Add` with the
two `CovariantClass` instances, so it belongs in an order/algebra file rather than in
`Cardinal`; `Mathlib/Order/Bounds/Image.lean` (which already has `BddAbove.add`) is the
natural home, and then `Cardinal` only needs `bddAbove_range_mul`.

Names: `_diagonal` mirrors the general lemma.  Alternatives to raise in review are
`Cardinal.ciSup_add_ciSup'` (primed sibling of the existing lemma) or
`Cardinal.ciSup_add_ciSup_of_exists_le` (hypothesis-describing, Mathlib's more usual
convention).  Pick one before writing PR 2, since PR 3 builds on it.

---

## PR 3 (optional) — corollaries

Only worth opening if reviewers ask for them during PR 2.

```lean
protected theorem Cardinal.ciSup_add_ciSup_of_monotone [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (hmf : Monotone f) (hmg : Monotone g) : (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k
protected theorem Cardinal.ciSup_mul_ciSup_of_monotone  -- likewise
```

These mirror the existing `ENNReal.iSup_add_iSup_of_monotone` /
`ENat.iSup_add_iSup_of_monotone` and are one-liners (`exists_ge_ge` supplies the
diagonal hypothesis), so the `Cardinal` API ends up matching the `ℝ≥0∞`/`ℕ∞` API
lemma for lemma.

Also in this bucket, and the most likely to be rejected:

```lean
theorem iSup_op_iSup_diagonal (op : α → α → α)
    (hl : ∀ f a, op (⨆ i, f i) a = ⨆ i, op (f i) a)
    (hr : ∀ a g, op a (⨆ j, g j) = ⨆ j, op a (g j))
    (h : ∀ i j, ∃ k, op (f i) (g j) ≤ op (f k) (g k)) :
    op (⨆ i, f i) (⨆ j, g j) = ⨆ k, op (f k) (g k)
```

It makes each call site a single application instead of `simp_rw [...] ; exact ...`, at
the cost of an unbundled `op` with two distributivity hypotheses — a shape Mathlib
usually spells with a typeclass instead.  Recommendation: leave it out of PR 1, mention
it in the PR description, and only add it if a reviewer asks for the call sites to be
one-liners.

---

## Deliberately *not* upstreamed

From this project, the following are exploratory and should stay here:

* `RequestProject/Bridges.lean` — the transports (order iso, `sSupHom`, Galois
  connection, `Functor.diag` finality).  The categorical route is a nice remark for a PR
  description (*"for a monotone family over a directed index, the collapse is exactly
  finality of the diagonal functor"*) but adds no lemma Mathlib needs.
* `RequestProject/ProofGraph.lean`, `RequestProject/Variations.lean` — meta-material.
* `Golf.iSup_pprod` / `Golf.ciSup_pprod` (`PProd` currying).  PR 2 uses the `Prod`
  version `ciSup_prod` instead, matching the existing `iSup_prod`; the `Sort`-level
  `PProd` variant is only needed if someone wants `ciSup₂_eq_ciSup_diagonal` for
  `ι : Sort*`, which no call site does.

## Pre-submission checklist

* [ ] `Cardinal` naming decided (`_diagonal` vs `'` vs `_of_exists_le`).
* [ ] Decide whether PR 1 includes the two new `iSup_mul_iSup` lemmas.
* [ ] `bddAbove_range_add` placed in `Order/Bounds/Image.lean`, not in `Cardinal`.
* [ ] No new files, so `Mathlib.lean` is untouched and no import graph changes; confirm
      with `lake exe shake` and `lake exe mk_all --check`.
* [ ] Run `#lint` on the touched files (the code here is lint-clean: no unused section
      variables, all lines ≤ 100 chars, every declaration has a docstring).
* [ ] No deprecations needed anywhere: PR 1 changes proofs only, PR 2 and 3 are additive.
* [ ] Check the two downstream users of `Cardinal.ciSup_add_ciSup`
      (`LinearAlgebra/Dimension/Constructions.lean`,
      `RingTheory/AlgebraicIndependent/Transcendental.lean`) — they may simplify with the
      new diagonal lemmas, which is a good line to include in the PR 2 description.
