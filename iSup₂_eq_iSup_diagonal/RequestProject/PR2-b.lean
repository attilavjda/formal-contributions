import Mathlib

/-!
# PR 2, in its smallest defensible form

This file is the *submission copy* of the second upstream pull request, the answer to the
review question left open by PR 1:

> "please also add versions for `ConditionallyCompleteLattice` /
> `ConditionallyCompleteLinearOrderBot`?  See `ciSup_mono_of_forall_exists` and
> `ciSup_mono_of_forall_exists'`."

**Answer: PR 2 is one lemma, plus the caller that motivates it.**

* `ciSup₂_eq_ciSup_diagonal` over `ConditionallyCompleteLattice`, with the argument order of
  `ciSup_mono_of_forall_exists` — family first, then the `BddAbove` side condition, then the
  cofinality hypothesis — and **no** `[Nonempty ι]`: for empty `ι` both sides are `sSup ∅`,
  so the statement is true (and needed, since `iSup₂_eq_iSup_diagonal` of PR 1 has no such
  hypothesis either).
* `Cardinal.ciSup_add_ciSup_diagonal`, the caller: it collapses the double supremum that the
  existing `Cardinal.ciSup_add_ciSup` produces.  Without a caller the lemma has no business
  being upstreamed, so it ships in the same PR.

**Not shipped: a `ConditionallyCompleteLinearOrderBot` duplicate.**  The relation between
`ciSup_mono_of_forall_exists` and `ciSup_mono_of_forall_exists'` is that the primed version
drops `[Nonempty ι]`, which the unprimed one needs.  Here the unprimed version already has no
`[Nonempty ι]`, so the primed analogue would be *literally the same statement* at a stronger
typeclass — i.e. a strict specialisation, deprecated on arrival.  That is a sentence for the PR
text, not a declaration in the diff; the `PrimedVersion` section below compiles the would-be
primed statement and closes it by `exact`ing the general lemma, so the claim is checked rather
than asserted.  (`Cardinal` is itself a `ConditionallyCompleteLinearOrderBot`, so the caller is
already an instance of the primed use case.)

Also deliberately out of PR 2, each for its own reason:

* the boundedness helpers (`IsCofinalFor.bddAbove` and friends) — the one boundedness fact this
  PR needs is three lines, used once, and is inlined in the caller;
* `ciSup_prod` / the currying route — a different lemma with a different review argument;
* `Cardinal.ciSup_mul_ciSup_diagonal` and the `_of_monotone` corollaries — no caller pressure,
  so they belong to a later PR (see PR 3) or to nothing at all.

Everything below compiles against the pinned Mathlib with no `sorry`.  The enclosing
`namespace PR2` is dropped when copying into Mathlib.

Note on names: the pinned Mathlib of this project still calls the two monotonicity lemmas
`ciSup_mono'`; `ciSup_mono_of_forall_exists`(`'`) is the name used in the review.  Only the
argument *order* matters for this file, and that is the same under either name.
-/

namespace PR2

open Set

/-! ## The new lemma

Insertion point: `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`, in the
`ConditionallyCompleteLattice` section, next to `ciSup_mono` / `ciSup_mono_of_forall_exists`.

Scope notes for the PR body:

* No `[Nonempty ι]`.  The empty case is not vacuous and not junk-value abuse: both sides
  unfold to `sSup (∅ : Set α)`, so `iSup_of_empty'` closes it definitionally.
* The `BddAbove` hypothesis is only about the *diagonal*.  Boundedness of the rows and of the
  family of row-suprema is *derived* from it together with the cofinality hypothesis — that is
  exactly the work that the complete-lattice statement of PR 1 does not have to do.
-/

/-- A doubly indexed supremum equals the supremum along its diagonal when the diagonal is
cofinal, i.e. when every entry `f i j` is dominated by some diagonal entry `f k k`.

Conditionally complete version of `iSup₂_eq_iSup_diagonal`: the diagonal is assumed to be
bounded above, and boundedness of the rows follows.  No `Nonempty ι` is needed: for empty `ι`
both sides are `sSup ∅`. -/
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (hf : BddAbove (range fun k => f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  obtain ⟨b, hb⟩ := hf
  have hfb : ∀ i j, f i j ≤ b := fun i j => (h i j).elim fun k hk => hk.trans (hb ⟨k, rfl⟩)
  have hrow : ∀ i, BddAbove (range (f i)) := fun i => ⟨b, forall_mem_range.2 (hfb i)⟩
  have hcol : BddAbove (range fun i => ⨆ j, f i j) :=
    ⟨b, forall_mem_range.2 fun i => ciSup_le (hfb i)⟩
  refine le_antisymm (ciSup_le fun i => ciSup_le fun j => ?_) (ciSup_le fun k => ?_)
  · exact (h i j).elim fun k hk => hk.trans (le_ciSup ⟨b, hb⟩ k)
  · exact (le_ciSup (hrow k) k).trans (le_ciSup hcol k)

/-! ## The caller

Insertion point: `Mathlib/SetTheory/Cardinal/Arithmetic.lean`, immediately after
`Cardinal.ciSup_add_ciSup`, inside the same `section add` (whose variables already supply
`[Nonempty ι]`).

`Cardinal.ciSup_add_ciSup` turns `(⨆ i, f i) + ⨆ j, g j` into the doubly indexed
`⨆ i, ⨆ j, f i + g j`; the diagonal hypothesis is what lets that be read back as a single
supremum, which is the form every use site wants.  The only boundedness fact needed is that
`fun k => f k + g k` is bounded above, which is three lines from `hf` and `hg`. -/

section Caller

universe u v

open Cardinal

/-- Diagonal form of `Cardinal.ciSup_add_ciSup`: if every `f i + g j` is dominated by some
`f k + g k`, the double supremum collapses onto the diagonal. -/
protected theorem Cardinal.ciSup_add_ciSup_diagonal {ι : Type u} [Nonempty ι]
    (f g : ι → Cardinal.{v}) (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have hd : BddAbove (range fun k => f k + g k) :=
    ⟨a + b, forall_mem_range.2 fun k => add_le_add (ha ⟨k, rfl⟩) (hb ⟨k, rfl⟩)⟩
  rw [Cardinal.ciSup_add_ciSup f ⟨a, ha⟩ g ⟨b, hb⟩]
  exact ciSup₂_eq_ciSup_diagonal _ hd h

end Caller

/-! ## Not in the diff — the `ConditionallyCompleteLinearOrderBot` question

This section is the machine-checked backing for the PR sentence

> the `ConditionallyCompleteLinearOrderBot` version is the same statement, so there is nothing
> to add.

The would-be primed lemma is stated here verbatim — same binders, same hypotheses, same
conclusion, only the typeclass strengthened — and its proof is a single application of the
general lemma, with no argument massaged.  Shipping it would therefore add a declaration that
`exact ciSup₂_eq_ciSup_diagonal ..` already provides. -/

section PrimedVersion

/-- The `ConditionallyCompleteLinearOrderBot` "primed" analogue, *not* proposed for inclusion:
it is the same statement at a stronger typeclass. -/
example {α : Type*} {ι : Sort*} [ConditionallyCompleteLinearOrderBot α] (f : ι → ι → α)
    (hf : BddAbove (range fun k => f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  ciSup₂_eq_ciSup_diagonal f hf h

/-- The empty case, which is why no `[Nonempty ι]` appears: both sides are `⊥` here, and
`sSup ∅` in a bare `ConditionallyCompleteLattice`. -/
example {α : Type*} {ι : Sort*} [ConditionallyCompleteLinearOrderBot α] [IsEmpty ι]
    (f : ι → ι → α) : ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by simp

end PrimedVersion

/-! ## The short answer, for pasting into the review thread

> PR 2: one lemma only.
>
> `ciSup₂_eq_ciSup_diagonal (f) (hf : BddAbove (range fun k ↦ f k k))`
> `(h : ∀ i j, ∃ k, f i j ≤ f k k)` over `ConditionallyCompleteLattice`, argument order
> matching `ciSup_mono_of_forall_exists`, no `Nonempty ι` (empty case: `sSup ∅` both sides),
> plus the `Cardinal.ciSup_add_ciSup_diagonal` caller.
>
> The `…LinearOrderBot` primed version — the analogue of `ciSup_mono_of_forall_exists'` — is
> then literally the same statement, so state that in the PR text instead of shipping a
> duplicate.
-/

end PR2
