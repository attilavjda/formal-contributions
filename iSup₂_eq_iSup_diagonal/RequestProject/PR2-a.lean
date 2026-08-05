import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# PR 2 — what to add

PR 1 carried the complete-lattice diagonal lemma `iSup₂_eq_iSup_diagonal` (with its `@[to_dual]`
partner) and the three caller rewrites `ENat.iSup_add_iSup`, `ENNReal.iSup_add_iSup`,
`ENNReal.iInf_add_iInf`. This file is the analogous read-off of **PR 2**: it contains exactly the
declarations that PR 2 adds, in their final names, argument order and proofs, and nothing else.
Everything below compiles, so the PR contents can be checked, not just described.

**Title:** `feat(Order/ConditionallyCompleteLattice): diagonal collapse for doubly indexed suprema`

**Files touched**

| file | addition |
| --- | --- |
| `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean` | `ciSup₂_eq_ciSup_diagonal` (§1) |
| `Mathlib/SetTheory/Cardinal/Arithmetic.lean` | `Cardinal.ciSup_add_ciSup_diagonal` (§2) |
| `Mathlib/Order/Bounds/Basic.lean` | *optional:* `IsCofinalFor.bddAbove` (§3) |

**Scope.** PR 2 holds only the conditionally complete side: one lemma plus its one caller. It is
separated from PR 1 because the statement lives in a different file and under a different typeclass
(`ConditionallyCompleteLattice`, where the `sSup_le`/`le_sSup` proof of PR 1 does not run), and
because its caller is a `Cardinal` result — `Cardinal` is a `ConditionallyCompleteLinearOrderBot`,
not a complete lattice, so it cannot be served by PR 1's lemma.

**Things for the PR text, not for the code** (§4): the `ConditionallyCompleteLinearOrderBot`
variant asked for in review is *not* a second lemma — once `Nonempty ι` is dropped it is literally
the same statement, specialised along `ConditionallyCompleteLinearOrderBot →
ConditionallyCompleteLattice`.
-/

open Set

set_option autoImplicit false

namespace PR2

/-! ### Shim (not part of the PR)

Upstream, one half of the antisymmetry below is the neighbouring lemma
`ciSup_mono_of_forall_exists`, which should be reused rather than re-proved. The Mathlib pinned by
this project has only its `ConditionallyCompleteLinearOrderBot` copy `ciSup_mono'`, so the general
form is restated here privately to keep this file self-contained. Delete it when preparing the
patch and call the upstream lemma. -/

private theorem ciSup_mono_of_forall_exists {α : Type*} {ι κ : Sort*}
    [ConditionallyCompleteLattice α] [Nonempty ι] {f : ι → α} {g : κ → α}
    (hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k) : ⨆ i, f i ≤ ⨆ k, g k := by
  refine ciSup_le fun i ↦ ?_
  obtain ⟨k, hk⟩ := h i
  exact hk.trans (le_ciSup hg k)

/-! ## §1 The lemma

Goes in `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`, in the
`ConditionallyCompleteLattice` section, after `ciSup_mono_of_forall_exists` (the lemma its proof
uses).

Argument order `(f) (hf) (h)`: the family first, then the boundedness hypothesis, then the
cofinality hypothesis — matching `ciSup_mono`/`le_ciSup`, where the `BddAbove` argument precedes
the pointwise one. `hf` is explicit and about the *diagonal* only: cofinality then bounds the whole
square family, so no separate hypothesis on `f i j` is needed.

There is deliberately **no** `[Nonempty ι]`: for empty `ι` both sides are `sSup ∅`, handled by the
first branch. -/

/-- A doubly indexed supremum in a conditionally complete lattice equals the supremum along its
diagonal, provided the diagonal is bounded above and cofinal: every entry `f i j` is dominated by
some diagonal entry `f k k`. -/
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · -- The central fact: every entry is below the diagonal supremum, `f i j ≤ ⨆ k, f k k`. It is
    -- the only use of `hf`, and it yields the row bound, the bound on the row suprema, and the
    -- second half of the antisymmetry.
    have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
      let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hf k)
    have hrow : ∀ i, BddAbove (range (f i)) := fun i ↦ ⟨_, forall_mem_range.2 (hle i)⟩
    have hcol : BddAbove (range fun i ↦ ⨆ j, f i j) :=
      ⟨_, forall_mem_range.2 fun i ↦ ciSup_le (hle i)⟩
    exact le_antisymm (ciSup_le fun i ↦ ciSup_mono_of_forall_exists hf (h i))
      (ciSup_le fun k ↦ le_ciSup_of_le hcol k (le_ciSup (hrow k) k))

/-- The empty index case really is covered: with `ι` empty the hypotheses are vacuous and the
statement still applies. This is the machine check behind "no `Nonempty ι`". -/
example : (⨆ _ : PEmpty.{1}, ⨆ _ : PEmpty.{1}, (0 : Cardinal)) = ⨆ _ : PEmpty.{1}, (0 : Cardinal) :=
  ciSup₂_eq_ciSup_diagonal (fun _ _ ↦ 0) ⟨0, by rintro _ ⟨⟨⟩, _⟩⟩ (by rintro ⟨⟩)

/-! ## §2 The caller

Goes in `Mathlib/SetTheory/Cardinal/Arithmetic.lean`, immediately after
`Cardinal.ciSup_add_ciSup`, whose double supremum it collapses. This is the sole caller of §1 and
the reason PR 2 is not merely a generalisation with no user.

Only the `hf`/`hg` bounds are assumed on the summands; the bound `bf + bg` for the diagonal family
is produced inside the proof, so the caller's interface stays exactly that of
`Cardinal.ciSup_add_ciSup` plus the cofinality hypothesis. -/

/-- A diagonal strengthening of `Cardinal.ciSup_add_ciSup`: if every mixed sum `f i + g j` is
dominated by a diagonal sum `f k + g k`, the double supremum collapses to the diagonal. -/
protected theorem Cardinal.ciSup_add_ciSup_diagonal {ι : Type*} [Nonempty ι] (f g : ι → Cardinal)
    (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  obtain ⟨bf, hbf⟩ := id hf
  obtain ⟨bg, hbg⟩ := id hg
  rw [Cardinal.ciSup_add_ciSup f hf g hg]
  exact ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j)
    ⟨bf + bg, by rintro _ ⟨k, rfl⟩; exact add_le_add (hbf ⟨k, rfl⟩) (hbg ⟨k, rfl⟩)⟩ h

/-- Why the caller cannot be served by PR 1's complete-lattice lemma: `Cardinal` has no greatest
element, so it carries no `CompleteLattice` structure for its order. This is the formal version of
the scope argument for splitting PR 2 off from PR 1. -/
theorem cardinal_not_bddAbove_univ : ¬ ∃ t : Cardinal, ∀ c : Cardinal, c ≤ t := by
  rintro ⟨t, ht⟩
  exact (Order.lt_succ t).not_ge (ht _)

/-- The cofinality hypothesis of the caller is the expected one and is easy to meet in practice:
for monotone families on a directed index type it holds by taking `k = max i j`. Worth quoting in
the PR body as the usage pattern. -/
example (f g : ℕ → Cardinal) (hf : Monotone f) (hg : Monotone g) (i j : ℕ) :
    ∃ k, f i + g j ≤ f k + g k :=
  ⟨max i j, add_le_add (hf (le_max_left i j)) (hg (le_max_right i j))⟩

/-! ## §3 Optional companion: `IsCofinalFor.bddAbove`

Goes in `Mathlib/Order/Bounds/Basic.lean`, next to `BddAbove.mono` (the `⊆` version of the same
fact) and after `upperBounds_mono_of_isCofinalFor`, which proves it.

It was proposed as part (a) of the modular draft but has no caller in PR 1. It does have one here:
it discharges the *inner* boundedness side condition of §1 — each row `range (f i)` is cofinal in
the diagonal, hence inherits the diagonal's bound. So if part (a) is shipped at all, PR 2 is where
it is load-bearing; if it is dropped, §1 is unaffected (its proof above gets the row bound from
`hle` instead).

Note the *outer* condition `BddAbove (range fun i ↦ ⨆ j, f i j)` is **not** an instance of it: a
row supremum need not lie below any single diagonal entry. That is why the proof in §1 still builds
the outer bound by hand, and why this companion is a convenience rather than a prerequisite. -/

/-- A set that is cofinal in a bounded-above set is itself bounded above. Cofinal version of
`BddAbove.mono`. -/
@[to_dual IsCoinitialFor.bddBelow /-- A set that is coinitial in a bounded-below set is itself
bounded below. Coinitial version of `BddBelow.mono`. -/]
theorem IsCofinalFor.bddAbove {α : Type*} [Preorder α] {s t : Set α} (h : IsCofinalFor s t)
    (ht : BddAbove t) : BddAbove s :=
  ht.imp fun _ hc ↦ upperBounds_mono_of_isCofinalFor h hc

/-- The use in §1: rows are cofinal in the diagonal, hence bounded above by it. -/
theorem bddAbove_row_of_bddAbove_diagonal {α : Type*} {ι : Sort*}
    [ConditionallyCompleteLattice α] (f : ι → ι → α) (hf : BddAbove (range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) (i : ι) : BddAbove (range (f i)) :=
  IsCofinalFor.bddAbove
    (by rintro _ ⟨j, rfl⟩; obtain ⟨k, hk⟩ := h i j; exact ⟨f k k, ⟨k, rfl⟩, hk⟩) hf

/-- With §3 available, the row bound `hrow` of §1 is a named lemma rather than a `have` derived
from `hle`. Shipping part (a) therefore shortens the main proof by one hypothesis-building step;
this `example` is the check that the shortened proof still closes the goal. -/
example {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
      let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hf k)
    have hcol : BddAbove (range fun i ↦ ⨆ j, f i j) :=
      ⟨_, forall_mem_range.2 fun i ↦ ciSup_le (hle i)⟩
    exact le_antisymm (ciSup_le fun i ↦ ciSup_mono_of_forall_exists hf (h i))
      (ciSup_le fun k ↦ le_ciSup_of_le hcol k
        (le_ciSup (bddAbove_row_of_bddAbove_diagonal f hf h k) k))

/-! ## §4 Not in PR 2

Each item below is excluded, with the reason. Nothing here is a live declaration.

**(a) The `ConditionallyCompleteLinearOrderBot` variant.** Requested in review as a second lemma.
It is not one: once `Nonempty ι` is dropped from §1 there is nothing left to weaken, and the
`…Bot` statement is §1 read at a stronger instance. What would be posted is

```lean
theorem ciSup₂_eq_ciSup_diagonal' {α : Type*} {ι : Sort*}
    [ConditionallyCompleteLinearOrderBot α] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  ciSup₂_eq_ciSup_diagonal f hf h
```

i.e. a lemma whose proof is its own general case. Say this in the PR description; do not add the
declaration. (The `example` immediately below is the machine check that the specialisation really
is definitionally the same statement, so the claim in the PR text is verified rather than
asserted.)

**(b) `iSup₂_eq_iSup_diagonal` and the `ENat`/`ENNReal` callers.** PR 1.

**(c) The `IsCofinalFor` equality lemmas** (`sSup_eq_sSup_of_isCofinalFor` and its indexed and
dual forms). PR 3: they are about a different predicate and are self-justifying as the equality
companions of the existing one-sided `sSup_le_sSup_of_isCofinalFor`.

**(d) An `iInf₂` dual of §1.** `@[to_dual]` does not apply here (the `BddAbove` hypothesis and the
`ciSup` API are not yet dual-linked in the conditionally complete files), and there is no caller
for the infimum form. Adding it by hand is independently justifiable, hence a separate PR at most.
-/

/-- Check for §4(a): the `ConditionallyCompleteLinearOrderBot` reading of §1 is the same statement,
so it needs no separate declaration. -/
example {α : Type*} {ι : Sort*} [ConditionallyCompleteLinearOrderBot α] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  ciSup₂_eq_ciSup_diagonal f hf h

end PR2
