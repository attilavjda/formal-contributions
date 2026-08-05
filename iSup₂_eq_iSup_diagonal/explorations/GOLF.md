# Golfing the diagonal-supremum patch

This note answers the question *"can the `ciSup` lemmas be factored out or reused?"*.
Short answer: **yes — the two conditionally complete lemmas are the same lemma**, and one half of
the remaining proof is an existing Mathlib lemma.

Everything quoted below is machine-checked in this project
(`RequestProject/NextPR.lean`, `RequestProject/Diagonal.lean`, `Main.lean`); the whole project
builds with no `sorry`/`admit`. The ready-to-apply upstream diff is `GOLF.patch`.

## 1. `ciSup₂_eq_ciSup_diagonal'` is not a second lemma

The proposal contained two lemmas whose proofs were copies of each other, differing only by
`ciSup_le` ↔ `ciSup_le'` and `ciSup_mono_of_forall_exists` ↔ `ciSup_mono_of_forall_exists'`:

* `ciSup₂_eq_ciSup_diagonal`  — `[ConditionallyCompleteLattice α] [Nonempty ι]`
* `ciSup₂_eq_ciSup_diagonal'` — `[ConditionallyCompleteLinearOrderBot α]`, no `Nonempty ι`

The reason for the split was the empty index. But `[Nonempty ι]` is not needed in the general
statement either: if `ι` is empty, *both* sides are `sSup ∅`, so

```lean
cases isEmpty_or_nonempty ι
· rw [iSup_of_empty', iSup_of_empty']
```

closes that case in a conditionally complete lattice — no `⊥` required. With `[Nonempty ι]`
dropped, the primed lemma becomes *literally the same statement* (a
`ConditionallyCompleteLinearOrderBot` is a `ConditionallyCompleteLattice`), so it can be deleted:

```lean
theorem ciSup₂_eq_ciSup_diagonal' … := ciSup₂_eq_ciSup_diagonal f h hb   -- redundant
```

(It is kept in `RequestProject/NextPR.lean` only as a one-line record of this fact; the upstream
patch omits it.) Two ~24-line proofs plus a duplicated API family thus collapse to one ~10-line
proof, and the `Cardinal` caller uses the general lemma directly.

## 2. Reuse inside the surviving proof

* The two `BddAbove` side conditions (bound for a row `range (f i)`, bound for the family of row
  suprema) both follow from the single fact `∀ i j, f i j ≤ ⨆ k, f k k`: every entry is below the
  diagonal supremum. Proving that once (`hle`) removes the repetition, and taking the diagonal
  supremum itself as the bound avoids naming an anonymous upper bound `b`.
* The first half of the antisymmetry, `⨆ i, ⨆ j, f i j ≤ ⨆ k, f k k`, is exactly the neighbouring
  Mathlib lemma `ciSup_mono_of_forall_exists` applied row-wise:
  `ciSup_le fun i ↦ ciSup_mono_of_forall_exists hb (h i)`.

Result (upstream form, `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`):

```lean
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) (hb : BddAbove (range fun k ↦ f k k)) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
      let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hb k)
    have hrow : ∀ i, BddAbove (range (f i)) := fun i ↦ ⟨_, forall_mem_range.2 (hle i)⟩
    have hcol : BddAbove (range fun i ↦ ⨆ j, f i j) :=
      ⟨_, forall_mem_range.2 fun i ↦ ciSup_le (hle i)⟩
    exact le_antisymm (ciSup_le fun i ↦ ciSup_mono_of_forall_exists hb (h i))
      (ciSup_le fun k ↦ le_ciSup_of_le hcol k (le_ciSup (hrow k) k))
```

Note the argument order `(f) (h) (hb)` is kept from the original proposal.

## 3. The complete-lattice lemma

`iSup₂_eq_iSup_diagonal` can lose five lines by opening both antisymmetry branches at once:

```lean
@[to_dual]
theorem iSup₂_eq_iSup_diagonal (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    ⨆ i, ⨆ j, f i j = ⨆ k, f k k := by
  refine le_antisymm (sSup_le ?_) (sSup_le ?_) <;> rintro _ ⟨i, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j
    exact hk.trans (le_sSup ⟨k, rfl⟩)
  · exact (le_sSup (s := range (f i)) ⟨i, rfl⟩).trans (le_sSup ⟨i, rfl⟩)
```

The second `(s := …)` ascription of the original is unnecessary; the first one is still needed to
pin down the inner range. Two cautions, both checked here:

* the proof must stay on the `sSup_le`/`le_sSup` API — the shorter `iSup_le`/`le_iSup` version
  fails to dualise (`@[to_dual]` reports *"The translated value is not type correct"*, keeping a
  `SupSet` projection where an `InfSet` one is required);
* the weaker `[CompleteSemilatticeSup α]` assumption suffices (as in the already-reviewed
  `UPSTREAM.patch`), and the generated dual then lands in `CompleteSemilatticeInf`.

## 4. The `ENat` / `ENNReal` callers

Those hunks are already minimal. The only nit: the empty branch

```lean
· simp only [iSup_of_empty, bot_eq_zero, zero_add]
```

can be plain `simp` in both files (checked here for `ENat` and `ENNReal`).

## Net effect on the proposed diff

| | proposal | golfed |
|---|---|---|
| new conditionally complete lemmas | 2 (26 + 26 lines) | 1 (10 lines) |
| `Nonempty ι` hypothesis | required in the general version | not needed |
| `Cardinal` caller | uses the `…Bot` variant | uses the general lemma |
| complete-lattice lemma | 16 lines | 9 lines |
