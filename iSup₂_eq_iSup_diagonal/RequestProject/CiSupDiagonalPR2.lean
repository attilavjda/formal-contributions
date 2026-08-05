import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Real.Archimedean

/-!
# `ciSup₂_eq_ciSup_diagonal` — submitted proof, refactor, tests, annotated walkthrough

This file is self-contained and holds four things, in order:

1. **§1 As submitted** (`AsSubmitted.ciSup₂_eq_ciSup_diagonal`): the proof exactly as it was
   handed in, compiled unchanged so that the starting point is on record.
2. **§2 Refactored for upstream** (`ciSup₂_eq_ciSup_diagonal`): the version proposed for PR 2 to
   `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`.
3. **§3 Tests**: the edge cases and intended use sites, all machine-checked.
4. **§4 Annotated** (`Annotated.ciSup₂_eq_ciSup_diagonal`): the same proof with the goal state
   `⊢ …` written out after every step.

The refactor changes the proof, never the statement: §1, §2 and §4 all prove literally the same
proposition, and `§2 ↔ §1 ↔ §4` is checked in §3 by `exact`-ing each against the others.
-/

open Set

set_option autoImplicit false

namespace CiSupDiagonal

/-! ## §1 The proof as submitted

Reproduced verbatim, with only the namespace added. -/

namespace AsSubmitted

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

end AsSubmitted

/-! ## §2 Refactored, upstream form

Three changes, none of them to the statement.

* **No `obtain ⟨b, hb⟩`.** The submitted proof extracts *some* upper bound `b` of the diagonal and
  bounds everything by it. But the diagonal supremum `⨆ k, f k k` — the right-hand side, which is
  in the goal anyway — is already such a bound, and it is the *least* one. Using it turns the two
  hypotheses `hf`, `h` into a single reusable fact `hle : ∀ i j, f i j ≤ ⨆ k, f k k`, from which
  the two `BddAbove` side conditions and the `≤` half of the goal all read off directly. This
  removes `hfb`, one `elim`, and the re-packaged `⟨b, hb⟩` at the end (which was `hf` again).
* **One `≤` per bullet.** With `hle` in hand, `le_antisymm` takes both arguments as terms, so the
  `refine … ?_ … ?_` with two bullets collapses to a single `exact`.
* **Mathlib style.** `fun … ↦`, `obtain`-free, hypotheses used where they are introduced. The
  hypothesis names follow the pattern of the surrounding file (`hf` for the boundedness of the
  family, `h` for the pointwise hypothesis).

Placement: the `ConditionallyCompleteLattice` section of
`Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`, next to `ciSup_le`/`le_ciSup`, whose
argument convention (family, then `BddAbove`, then pointwise data) the statement follows.

There is deliberately no `[Nonempty ι]`: for empty `ι` both sides are `sSup ∅`, which the first
branch discharges (checked in §3). -/

/-- A doubly indexed supremum in a conditionally complete lattice collapses to the supremum along
its diagonal, provided the diagonal is bounded above and cofinal in the family: every entry
`f i j` is dominated by some diagonal entry `f k k`. -/
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  -- The central fact: every entry is below the diagonal supremum, `f i j ≤ ⨆ k, f k k`. It gives
  -- the bounds `hrow`, `hcol` and both halves of the antisymmetry.
  have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
    let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hf k)
  have hrow : ∀ i, BddAbove (range (f i)) := fun i ↦ ⟨_, forall_mem_range.2 (hle i)⟩
  have hcol : BddAbove (range fun i ↦ ⨆ j, f i j) :=
    ⟨_, forall_mem_range.2 fun i ↦ ciSup_le (hle i)⟩
  exact le_antisymm (ciSup_le fun i ↦ ciSup_le (hle i))
    (ciSup_le fun k ↦ (le_ciSup (hrow k) k).trans (le_ciSup hcol k))

/-! ## §3 Tests -/

section Tests

/-- The refactor proves exactly the submitted statement, and conversely. -/
example : @ciSup₂_eq_ciSup_diagonal = @AsSubmitted.ciSup₂_eq_ciSup_diagonal := rfl

example {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  AsSubmitted.ciSup₂_eq_ciSup_diagonal f hf h

/-- Empty index type: no `[Nonempty ι]` is needed, both sides are `sSup ∅`. -/
example (f : Empty → Empty → ℝ) : ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  ciSup₂_eq_ciSup_diagonal f ⟨0, by rintro _ ⟨k, rfl⟩; exact k.elim⟩ fun i _ ↦ i.elim

/-- Empty `Sort`-valued index (a `Prop`), to exercise the `Sort*` generality. -/
example (f : False → False → ℝ) : ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  ciSup₂_eq_ciSup_diagonal f ⟨0, by rintro _ ⟨k, rfl⟩; exact k.elim⟩ fun i _ ↦ i.elim

/-- A monotone family over a directed order meets the cofinality hypothesis via `k = max i j`. -/
example (f : ℕ → ℕ → ℝ) (hmono : ∀ i j i' j', i ≤ i' → j ≤ j' → f i j ≤ f i' j')
    (hf : BddAbove (range fun k ↦ f k k)) : ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  ciSup₂_eq_ciSup_diagonal f hf fun i j ↦
    ⟨max i j, hmono _ _ _ _ (le_max_left i j) (le_max_right i j)⟩

/-- Constant family: the diagonal already carries everything. -/
example (c : ℝ) : ⨆ _ : ℕ, ⨆ _ : ℕ, c = ⨆ _ : ℕ, c :=
  ciSup₂_eq_ciSup_diagonal (fun _ _ ↦ c) (by simp) fun _ _ ↦ ⟨0, le_rfl⟩

/-- The intended caller: `Cardinal` is a `ConditionallyCompleteLinearOrderBot`, not a complete
lattice, so a complete-lattice diagonal lemma cannot serve it. Companion of
`Cardinal.ciSup_add_ciSup`. -/
theorem _root_.Cardinal.ciSup_add_ciSup_diagonal {ι : Type*} (f g : ι → Cardinal.{_})
    (hf : BddAbove (range fun k ↦ f k + g k)) (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    ⨆ i, ⨆ j, (f i + g j) = ⨆ k, (f k + g k) :=
  ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j) hf h

/-- A fully concrete instance on `ℝ`: an unbounded family truncated at `5`, so that the diagonal
really is bounded above and the lemma applies as stated. -/
example : ⨆ i : ℕ, ⨆ j : ℕ, ((i + j : ℕ) : ℝ) ⊓ 5 = ⨆ k : ℕ, ((k + k : ℕ) : ℝ) ⊓ 5 :=
  ciSup₂_eq_ciSup_diagonal (fun i j ↦ ((i + j : ℕ) : ℝ) ⊓ 5)
    ⟨5, by rintro _ ⟨k, rfl⟩; exact inf_le_right⟩
    fun i j ↦ ⟨max i j, inf_le_inf_right _ (by
      exact_mod_cast add_le_add (le_max_left i j) (le_max_right i j))⟩

end Tests

/-! ## §4 The same proof, annotated

Every line is followed by the goal state it leaves behind, written `⊢ …`, together with the
context entry it adds. The statement and the tactic script are identical to §2; only comments were
added. -/

namespace Annotated

/-- Annotated copy of `ciSup₂_eq_ciSup_diagonal`; see §2 for the unannotated proof. -/
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  -- Initial goal, with `f`, `hf : BddAbove (range fun k ↦ f k k)` and
  -- `h : ∀ (i j : ι), ∃ k, f i j ≤ f k k` in context:
  --   ⊢ ⨆ i, ⨆ j, f i j = ⨆ k, f k k
  --
  -- `ciSup` unfolds to `sSup (range …)`, and in a *conditionally* complete lattice `sSup` of an
  -- unbounded or empty set is junk, so the empty case must be split off: there is no `Nonempty ι`
  -- hypothesis to lean on.
  cases isEmpty_or_nonempty ι
  -- Two goals, with the same statement but different instances in context.
  -- Case 1, `h✝ : IsEmpty ι`:
  --   ⊢ ⨆ i, ⨆ j, f i j = ⨆ k, f k k
  -- Both sides are suprema over an empty index type, i.e. `sSup ∅`, hence literally the same term.
  -- `iSup_of_empty' : ⨆ i, f i = sSup ∅` fires first on the outermost supremum of the left-hand
  -- side (taking the inner one with it) and then on the right-hand side, closing the goal by
  -- `rfl`:
  --   ⊢ sSup ∅ = sSup ∅   ⇝   no goals
  · rw [iSup_of_empty', iSup_of_empty']
  -- Case 2, `h✝ : Nonempty ι`:
  --   ⊢ ⨆ i, ⨆ j, f i j = ⨆ k, f k k
  --
  -- The whole proof turns on one fact: the right-hand side is itself an upper bound for *every*
  -- entry of the square family. Indeed `h i j` produces a diagonal entry `f k k` above `f i j`,
  -- and `le_ciSup hf k : f k k ≤ ⨆ k, f k k` — this is where `hf` (boundedness of the diagonal) is
  -- used, and it is the only place it is needed.
  --   `let ⟨k, hk⟩ := h i j`  gives  `hk : f i j ≤ f k k`
  --   `hk.trans (le_ciSup hf k) : f i j ≤ ⨆ k, f k k`
  have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
    let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hf k)
  -- Context gains `hle : ∀ (i j : ι), f i j ≤ ⨆ k, f k k`; goal unchanged:
  --   ⊢ ⨆ i, ⨆ j, f i j = ⨆ k, f k k
  --
  -- `hle i` says the `i`-th row `f i : ι → α` is bounded above by `⨆ k, f k k`, i.e. every element
  -- of `range (f i)` is `≤` it (`forall_mem_range.2` converts the pointwise statement into the
  -- membership statement `∀ y ∈ range (f i), y ≤ _` that `BddAbove` unfolds to). The `_` is the
  -- witness `⨆ k, f k k`, inferred from `hle i`.
  have hrow : ∀ i, BddAbove (range (f i)) := fun i ↦ ⟨_, forall_mem_range.2 (hle i)⟩
  -- Context gains `hrow : ∀ (i : ι), BddAbove (range (f i))`; goal unchanged:
  --   ⊢ ⨆ i, ⨆ j, f i j = ⨆ k, f k k
  --
  -- The same bound works one level up: each row supremum `⨆ j, f i j` is `≤ ⨆ k, f k k` by
  -- `ciSup_le (hle i)`, so the family of row suprema is bounded above too.
  have hcol : BddAbove (range fun i ↦ ⨆ j, f i j) :=
    ⟨_, forall_mem_range.2 fun i ↦ ciSup_le (hle i)⟩
  -- Context gains `hcol : BddAbove (range fun i ↦ ⨆ j, f i j)`; goal unchanged:
  --   ⊢ ⨆ i, ⨆ j, f i j = ⨆ k, f k k
  --
  -- `le_antisymm` splits the equality into the two inequalities
  --   ⊢ ⨆ i, ⨆ j, f i j ≤ ⨆ k, f k k    and    ⊢ ⨆ k, f k k ≤ ⨆ i, ⨆ j, f i j
  -- both of which are now one-liners.
  --
  -- `≤`: peel the two suprema with `ciSup_le` twice — `ciSup_le : (∀ i, f i ≤ a) → ⨆ i, f i ≤ a`
  --   ⊢ ⨆ i, ⨆ j, f i j ≤ ⨆ k, f k k
  --   ⇝ (fix `i`)  ⊢ ⨆ j, f i j ≤ ⨆ k, f k k
  --   ⇝ (fix `j`)  ⊢ f i j ≤ ⨆ k, f k k          -- exactly `hle i j`
  --
  -- `≥`: bound the diagonal entry `f k k` by climbing the two suprema, using `le_ciSup`, which
  -- needs the boundedness facts just established — `le_ciSup (hrow k) k : f k k ≤ ⨆ j, f k j`
  -- (the `k`-th entry of the `k`-th row) and `le_ciSup hcol k : (⨆ j, f k j) ≤ ⨆ i, ⨆ j, f i j`
  -- (the `k`-th row supremum among all row suprema); `Trans` chains them:
  --   ⊢ ⨆ k, f k k ≤ ⨆ i, ⨆ j, f i j
  --   ⇝ (fix `k`)  ⊢ f k k ≤ ⨆ i, ⨆ j, f i j
  --   ⇝ f k k ≤ ⨆ j, f k j ≤ ⨆ i, ⨆ j, f i j
  exact le_antisymm (ciSup_le fun i ↦ ciSup_le (hle i))
    (ciSup_le fun k ↦ (le_ciSup (hrow k) k).trans (le_ciSup hcol k))
  -- no goals

end Annotated

end CiSupDiagonal
