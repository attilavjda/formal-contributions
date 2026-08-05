import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ENat.Lattice

/-!
# What the reviewer is asking for

The review comment is

> could you please also add versions for `ConditionallyCompleteLattice` /
> `ConditionallyCompleteLinearOrderBot`? See `ciSup_mono_of_forall_exists` and
> `ciSup_mono_of_forall_exists'`.

Reading:

* **"versions"** = the same diagonal-collapse statement that the PR extracts from the duplicated
  `ENat.iSup_add_iSup` / `ENNReal.iSup_add_iSup` proofs, but stated for *conditionally* complete
  orders instead of complete lattices. `ℕ∞` and `ℝ≥0∞` are complete lattices, so the PR as posted
  serves only them; the same argument is used for orders that have no top (`Cardinal`, `ℝ≥0`, `ℝ`
  on bounded families), and there the complete-lattice lemma does not apply.
* **the two typeclasses** = the standard Mathlib pair. The unprimed lemma lives in the
  `ConditionallyCompleteLattice` section and needs `[Nonempty ι]` and `BddAbove` side conditions;
  the primed one lives in the `ConditionallyCompleteLinearOrderBot` section, where `⨆` over an
  empty index is `⊥`, so `[Nonempty ι]` can be dropped and `ciSup_le'` replaces `ciSup_le`.
* **`ciSup_mono_of_forall_exists` / `ciSup_mono_of_forall_exists'`** = the template to copy: same
  file (`Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`), same naming convention (`'` for
  the `…Bot` copy), same hypothesis shape `(hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k)`
  — which is literally the `≤` half of the diagonal lemma. (In the Mathlib pinned by this project
  the `…Bot` member of that pair still carries its old name `ciSup_mono'`; §0 below reproduces both
  members under the names the reviewer used.)

Everything below compiles, so the reading is checked rather than asserted.

Result: §1 writes the two requested versions exactly as the reviewer describes them, §2 shows that
the `[Nonempty ι]` hypothesis is unnecessary for *this* statement (unlike for the template pair),
so the primed version is then literally a specialisation of the unprimed one, and §3 exhibits the
callers on the conditionally complete side.
-/

open Set

set_option autoImplicit false

namespace ReviewerCCLRequest

universe u v

variable {α : Type u} {ι : Sort v}

/-! ## §0 The template pair the reviewer points at

These are the two lemmas cited in the review, restated here so the file is self-contained against
the Mathlib version pinned by this project (which has the second one under its former name
`ciSup_mono'`, and does not yet have the first). They are *not* part of the proposed patch.

The pair is exactly the pattern to imitate: one statement, two typeclass settings, `'` marking the
`ConditionallyCompleteLinearOrderBot` copy, whose only difference is `ciSup_le'` in place of
`ciSup_le` and the absence of `[Nonempty ι]`.
-/

private theorem ciSup_mono_of_forall_exists {κ : Sort*} [ConditionallyCompleteLattice α]
    [Nonempty ι] {f : ι → α} {g : κ → α} (hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k) :
    ⨆ i, f i ≤ ⨆ k, g k :=
  ciSup_le fun i ↦ Exists.elim (h i) (le_ciSup_of_le hg)

private theorem ciSup_mono_of_forall_exists' {κ : Sort*} [ConditionallyCompleteLinearOrderBot α]
    {f : ι → α} {g : κ → α} (hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k) :
    ⨆ i, f i ≤ ⨆ k, g k :=
  ciSup_le' fun i ↦ Exists.elim (h i) (le_ciSup_of_le hg)

/-- The primed shim is the pinned Mathlib lemma `ciSup_mono'`, renamed. -/
example {κ : Sort*} [ConditionallyCompleteLinearOrderBot α] {f : ι → α} {g : κ → α}
    (hg : BddAbove (range g)) (h : ∀ i, ∃ k, f i ≤ g k) :
    ciSup_mono_of_forall_exists' hg h = ciSup_mono' hg h := rfl

/-! ## §1 The two requested versions

Written the way the review asks for them: the unprimed one in the `ConditionallyCompleteLattice`
section with `[Nonempty ι]`, the primed one in the `ConditionallyCompleteLinearOrderBot` section
without it, each proved through the corresponding member of the template pair.

Only the *diagonal* is assumed bounded above: cofinality then bounds every row, and the row suprema,
so no further `BddAbove` hypothesis is needed.
-/

section CCL

variable [ConditionallyCompleteLattice α]

/-- If every `f i j` is below some diagonal entry `f k k`, the doubly indexed supremum collapses
onto the diagonal. `ConditionallyCompleteLattice` version, cf. `ciSup_mono_of_forall_exists`. -/
theorem ciSup₂_eq_ciSup_diagonal_of_nonempty [Nonempty ι] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  -- The central fact: every entry lies below the diagonal supremum, `f i j ≤ ⨆ k, f k k`.
  -- It bounds each row (`hrow`), the family of row suprema (`hcol`), and hence both halves of the
  -- antisymmetry.
  have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
    let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hf k)
  have hrow : ∀ i, BddAbove (range (f i)) := fun i ↦ ⟨_, forall_mem_range.2 (hle i)⟩
  have hcol : BddAbove (range fun i ↦ ⨆ j, f i j) :=
    ⟨_, forall_mem_range.2 fun i ↦ ciSup_le (hle i)⟩
  exact le_antisymm (ciSup_le fun i ↦ ciSup_mono_of_forall_exists hf (h i))
    (ciSup_le fun k ↦ le_ciSup_of_le hcol k (le_ciSup (hrow k) k))

end CCL

section CCLOB

variable [ConditionallyCompleteLinearOrderBot α]

/-- If every `f i j` is below some diagonal entry `f k k`, the doubly indexed supremum collapses
onto the diagonal. `ConditionallyCompleteLinearOrderBot` version, cf.
`ciSup_mono_of_forall_exists'`: no `[Nonempty ι]` is needed, since a supremum over an empty index
is `⊥`. -/
theorem ciSup₂_eq_ciSup_diagonal' (f : ι → ι → α) (hf : BddAbove (range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) : ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  -- Same central fact as in the unprimed version: every entry is below the diagonal supremum.
  have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
    let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hf k)
  have hrow : ∀ i, BddAbove (range (f i)) := fun i ↦ ⟨_, forall_mem_range.2 (hle i)⟩
  have hcol : BddAbove (range fun i ↦ ⨆ j, f i j) :=
    ⟨_, forall_mem_range.2 fun i ↦ ciSup_le' (hle i)⟩
  exact le_antisymm (ciSup_le' fun i ↦ ciSup_mono_of_forall_exists' hf (h i))
    (ciSup_le' fun k ↦ le_ciSup_of_le hcol k (le_ciSup (hrow k) k))

end CCLOB

/-! ## §2 One thing to tell the reviewer: `[Nonempty ι]` is not needed here

For the template pair the `'` version is a genuinely stronger statement: `ciSup_mono_of_forall_exists`
compares two *different* families, and with `ι` empty its left-hand side is the junk value `sSup ∅`,
which need not be below `⨆ k, g k`. That is why the `…Bot` copy exists.

For the diagonal collapse the two sides are `sSup ∅` *simultaneously* when `ι` is empty, so the
`ConditionallyCompleteLattice` version holds with no `[Nonempty ι]` at all: -/

theorem ciSup₂_eq_ciSup_diagonal [ConditionallyCompleteLattice α] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact ciSup₂_eq_ciSup_diagonal_of_nonempty f hf h

/-- The empty index case, machine-checked: both sides are `sSup ∅`. -/
example : (⨆ _ : PEmpty.{1}, ⨆ _ : PEmpty.{1}, (0 : ℝ)) = ⨆ _ : PEmpty.{1}, (0 : ℝ) :=
  ciSup₂_eq_ciSup_diagonal (fun _ _ ↦ 0) ⟨0, by rintro _ ⟨⟨⟩, _⟩⟩ (by rintro ⟨⟩)

/-- Consequently the requested `'` version is not an independent lemma: it is the unprimed one
specialised along `ConditionallyCompleteLinearOrderBot → ConditionallyCompleteLattice`, with the
same hypotheses. -/
example {α : Type u} [ConditionallyCompleteLinearOrderBot α] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  ciSup₂_eq_ciSup_diagonal f hf h

/-- …and the two statements are definitionally the same statement, once instantiated. -/
example {α : Type u} [ConditionallyCompleteLinearOrderBot α] (f : ι → ι → α)
    (hf : BddAbove (range fun k ↦ f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ciSup₂_eq_ciSup_diagonal' f hf h = ciSup₂_eq_ciSup_diagonal f hf h := rfl

/-! ## §3 Callers on the conditionally complete side

These are what the review is really after: statements that the complete-lattice lemma of the PR
cannot serve.
-/

/-- `Cardinal` is a `ConditionallyCompleteLinearOrderBot` and *not* a complete lattice for its
order (there is no largest cardinal), so this caller needs the conditionally complete version. It
is the `Cardinal` analogue of `ENNReal.iSup_add_iSup`. -/
theorem Cardinal.ciSup_add_ciSup_diagonal {ι : Type u} (f g : ι → Cardinal.{max u v})
    (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + ⨆ j, g j = ⨆ k, (f k + g k) := by
  cases isEmpty_or_nonempty ι
  · simp
  · obtain ⟨a, ha⟩ := id hf
    obtain ⟨b, hb⟩ := id hg
    rw [Cardinal.ciSup_add_ciSup _ hf _ hg]
    exact ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j)
      ⟨a + b, forall_mem_range.2 fun k ↦ add_le_add (ha ⟨k, rfl⟩) (hb ⟨k, rfl⟩)⟩ h

/-- There is no greatest cardinal: the formal reason the PR's complete-lattice lemma cannot serve
the caller above. -/
theorem cardinal_no_greatest : ¬ ∃ t : Cardinal.{u}, ∀ c : Cardinal.{u}, c ≤ t := by
  rintro ⟨t, ht⟩
  exact (Order.lt_succ t).not_ge (ht _)

/-- A `ℝ≥0` instance of the `…Bot` version: monotone families meet the cofinality hypothesis with
`k = max i j`. -/
example (f : ℕ → ℕ → NNReal) (hmono : ∀ i j i' j', i ≤ i' → j ≤ j' → f i j ≤ f i' j')
    (hf : BddAbove (range fun k ↦ f k k)) : ⨆ i, ⨆ j, f i j = ⨆ k, f k k :=
  ciSup₂_eq_ciSup_diagonal' f hf fun i j ↦
    ⟨max i j, hmono i j _ _ (le_max_left i j) (le_max_right i j)⟩

/-- The two lemmas of the original PR remain the right tool for `ℕ∞` and `ℝ≥0∞`: those are complete
lattices, so no boundedness hypothesis is needed there. This is the existing Mathlib statement,
re-proved through the conditionally complete lemma only to show that it also covers them (with
`OrderTop.bddAbove` discharging the side condition). -/
example {ι : Sort*} (f g : ι → ENat) (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + ⨆ j, g j = ⨆ k, (f k + g k) := by
  cases isEmpty_or_nonempty ι
  · simp
  · rw [ENat.iSup_add, ← ciSup₂_eq_ciSup_diagonal (fun i j ↦ f i + g j) (OrderTop.bddAbove _) h]
    exact iSup_congr fun i ↦ ENat.add_iSup _

end ReviewerCCLRequest
