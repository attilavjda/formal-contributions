import Mathlib
import RequestProject.Diagonal
open Set
open scoped ENNReal
set_option relaxedAutoImplicit false
set_option autoImplicit false
/-!
# Stylistic variations on the diagonal-supremum lemmas
This file is a companion to `RequestProject.Diagonal`. It does **not** introduce new
mathematics: every theorem here re-proves (a version of) a lemma that already lives in
`Diagonal.lean`. The point is entirely *stylistic* — to exhibit the same handful of order-theoretic
facts written in as many different ways as the three proof-writing guides describe, moving
deliberately along the axes of the "Proof Design Space":
```
Style:         term ←————————→ tactic ←————————→ structured (calc/have/suffices)
Automation:    manual (le_sSup) ←————————→ automated (simp/gcongr/aesop)
Direction:     forward (obtain … ; exact) ←————————→ backward (refine … ?_)
Granularity:   one-liner ←————————→ many-line with named steps
Generality:    CompleteLattice ←————————→ CompleteSemilatticeSup ←————————→ CondCompleteLattice
Decomposition: monolithic ←————————→ reduced to a reusable core lemma
Combination:   pointful (fun x => …) ←————————→ point-free (∘, .antisymm, combinators)
```
Everything is placed in `namespace DiagonalVariations` so the names never clash with the canonical
lemmas in `Diagonal.lean` (which are `open`-imported and reused by some of the callers below).
The five subjects, each treated in several styles:
* `§1` mutual-cofinality equality of two indexed suprema;
* `§2` the diagonal collapse of a doubly-indexed supremum;
* `§3` the conditionally-complete variants (bounded, and `…Bot`);
* `§4` the `iSup`/`iInf` `+` callers (`ENat`, `ENNReal`, `Cardinal`);
* `§5` the set-level `IsCofinalFor` form and its dual.
-/
namespace DiagonalVariations
/-! ## §1. Mutual cofinality ⇒ equal suprema
`Diagonal.iSup_eq_iSup_of_forall_exists_le` proves this over `CompleteSemilatticeSup` with the
`sSup`/`le_sSup` API. Over a full `CompleteLattice` the indexed `iSup` API (`iSup_le`, `le_iSup`,
`iSup_mono'`) is available and gives shorter proofs; the variants below range from a one-liner to a
fully spelled-out `calc`. -/
section CofinalitySup
variable {α : Type*} {ι ι' : Sort*}
/-- **Maximally golfed, term mode, `CompleteLattice`.** `iSup_mono'` *is* exactly the "for every `i`
there is an `i'` dominating it" monotonicity, so each half of the antisymmetry is one word. This is
the shortest honest proof of the fact. -/
theorem cofinal_iSup_eq_golf [CompleteLattice α] {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i' :=
  le_antisymm (iSup_mono' h₁) (iSup_mono' h₂)
/-- **Term mode, low automation, using `Classical.choose`.** Instead of destructuring the
existentials with a tactic, we feed the chosen witness and its spec straight into `le_iSup`. Same
proof, no tactic block. -/
theorem cofinal_iSup_eq_term [CompleteLattice α] {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i' :=
  le_antisymm
    (iSup_le fun i => (h₁ i).choose_spec.trans (le_iSup g _))
    (iSup_le fun i' => (h₂ i').choose_spec.trans (le_iSup f _))
/-- **Backward tactic mode.** `refine` opens both antisymmetry goals and both `iSup_le` goals at
once, leaving two focused `?_`s that forward reasoning (`obtain … ; exact`) then closes. -/
theorem cofinal_iSup_eq_backward [CompleteLattice α] {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i' := by
  refine le_antisymm (iSup_le fun i => ?_) (iSup_le fun i' => ?_)
  · obtain ⟨i', hi'⟩ := h₁ i; exact hi'.trans (le_iSup g i')
  · obtain ⟨i, hi⟩ := h₂ i'; exact hi.trans (le_iSup f i)
/-- **Structured `calc` mode, textbook-like.** The chain of inequalities is written out
explicitly, so the reader sees exactly `f i ≤ g i' ≤ ⨆ i', g i'`. Most verbose, most legible. -/
theorem cofinal_iSup_eq_calc [CompleteLattice α] {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i' := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    obtain ⟨i', hi'⟩ := h₁ i
    calc f i ≤ g i'        := hi'
      _      ≤ ⨆ i', g i'  := le_iSup g i'
  · refine iSup_le fun i' => ?_
    obtain ⟨i, hi⟩ := h₂ i'
    calc g i' ≤ f i        := hi
      _       ≤ ⨆ i, f i   := le_iSup f i
/-- **`CompleteSemilatticeSup` generality, `sSup` API, `<;>` combinator.** This is the exact setting
of the canonical lemma, but golfed: the two antisymmetry branches are dispatched together with
`<;>`, then split only for the last `obtain`/`exact` step. Demonstrates the generality axis
(weaker typeclass) together with the automation axis (tactic combinators). -/
theorem cofinal_sSup_eq_combinator [CompleteSemilatticeSup α] {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i' := by
  apply le_antisymm <;> apply sSup_le <;> rintro _ ⟨i, rfl⟩
  · obtain ⟨i', hi'⟩ := h₁ i; exact hi'.trans (le_sSup ⟨i', rfl⟩)
  · obtain ⟨i, hi⟩ := h₂ i; exact hi.trans (le_sSup ⟨i, rfl⟩)
end CofinalitySup
/-! ## §2. The diagonal collapse `⨆ i, ⨆ j, f i j = ⨆ k, f k k`
Same fact, five different derivations: a `sSup`-level tactic proof (weakest typeclass), a golfed
`iSup`-level backward proof, a term-mode proof, a `calc` proof, and a *reductive* proof that does no
order theory itself — it flattens the double `iSup` with `iSup_prod'` and defers to the §1 lemma. -/
section Diagonal
variable {α : Type*}
/-- **`CompleteSemilatticeSup`, `sSup` API, forward tactic.** The canonical proof, kept for
comparison; each `sSup_le` peels one supremum and `le_sSup ⟨k, rfl⟩` re-enters the diagonal. This is
the exact proof of `Diagonal.iSup₂_eq_diagonal`. -/
theorem diag_sSup {ι : Sort*} [CompleteSemilatticeSup α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) : (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · apply sSup_le; rintro _ ⟨i, rfl⟩
    apply sSup_le; rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j
    exact hk.trans (le_sSup ⟨k, rfl⟩)
  · apply sSup_le; rintro _ ⟨k, rfl⟩
    exact (le_sSup (s := range (f k)) ⟨k, rfl⟩).trans (le_sSup ⟨k, rfl⟩)
/-- **`CompleteLattice`, golfed backward tactic.** With the indexed `iSup` API the whole proof is
three `refine`d goals: the `≤` direction chases a witness `k`; the `≥` direction is the diagonal
sitting inside the double supremum, `le_iSup_of_le k (le_iSup (f k) k)`. -/
theorem diag_iSup_backward {ι : Sort*} [CompleteLattice α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) : (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  refine le_antisymm (iSup_le fun i => iSup_le fun j => ?_) (iSup_le fun k => ?_)
  · obtain ⟨k, hk⟩ := h i j; exact hk.trans (le_iSup (fun k => f k k) k)
  · exact le_iSup_of_le k (le_iSup (f k) k)
/-- **`CompleteLattice`, term mode.** The same argument as a single proof term, with the witness
supplied by `Classical.choose`. -/
theorem diag_iSup_term {ι : Sort*} [CompleteLattice α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) : (⨆ i, ⨆ j, f i j) = ⨆ k, f k k :=
  le_antisymm
    (iSup_le fun i => iSup_le fun j =>
      (h i j).choose_spec.trans (le_iSup (fun k => f k k) (h i j).choose))
    (iSup_le fun k => le_iSup_of_le k (le_iSup (f k) k))
/-- **`CompleteLattice`, structured `calc`.** Each direction is a visible inequality chain; the `≥`
direction spells out `f k k ≤ ⨆ j, f k j ≤ ⨆ i, ⨆ j, f i j`, i.e. "the diagonal is below its own
row, which is below the whole double supremum". -/
theorem diag_iSup_calc {ι : Sort*} [CompleteLattice α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) : (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun j => ?_
    obtain ⟨k, hk⟩ := h i j
    calc f i j ≤ f k k        := hk
      _        ≤ ⨆ k, f k k   := le_iSup (fun k => f k k) k
  · refine iSup_le fun k => ?_
    calc f k k ≤ ⨆ j, f k j        := le_iSup (f k) k
      _        ≤ ⨆ i, ⨆ j, f i j   := le_iSup (fun i => ⨆ j, f i j) k
/-- **Reductive proof (maximum decomposition).** No order theory here at all: `iSup_prod'` rewrites
the double supremum as a supremum over `ι × ι`, and then this is literally the §1 lemma with the
diagonal `k ↦ f k k` as the second family (trivially cofinal in itself). This needs `ι : Type*`
(that is where `iSup_prod'` lives). -/
theorem diag_via_cofinal {ι : Type*} [CompleteLattice α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) : (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  rw [iSup_prod' (f := fun i j => f i j)]
  exact cofinal_iSup_eq_golf (fun p => h p.1 p.2) (fun k => ⟨(k, k), le_rfl⟩)
end Diagonal
/-! ## §3. Conditionally-complete variants
Here `iSup` is only well-behaved once we know the diagonal is bounded above; the API changes to
`ciSup_le`/`le_ciSup` (with an explicit `BddAbove` witness) and `ciSup_le'`/`le_ciSup'`. Two
generality points: the bare `ConditionallyCompleteLattice` needs a `Nonempty`/empty split, while a
`ConditionallyCompleteLinearOrderBot` handles the empty index for free (`⨆ = ⊥`). -/
section CondComplete
variable {α : Type*} {ι : Sort*}
/-- **`ConditionallyCompleteLattice`, empty/nonempty split.** The golfed cousin of
`Diagonal.ciSup₂_eq_ciSup_diagonal`: the uniform bound `hbound` is produced in one `fun`-line, and
each half of the antisymmetry is a single `ciSup_le`/`le_ciSup` chase. -/
theorem cdiag_bdd [ConditionallyCompleteLattice α] (f : ι → ι → α)
    (hf : BddAbove (Set.range fun k => f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · obtain ⟨b, hb⟩ := id hf
    have hbound : ∀ i j, f i j ≤ b := fun i j => (h i j).choose_spec.trans (hb ⟨_, rfl⟩)
    refine le_antisymm (ciSup_le fun i => ciSup_le fun j => ?_) (ciSup_le fun k => ?_)
    · obtain ⟨k, hk⟩ := h i j; exact hk.trans (le_ciSup hf k)
    · refine le_ciSup_of_le ⟨b, ?_⟩ k (le_ciSup ⟨b, ?_⟩ k)
      · rintro _ ⟨i, rfl⟩; exact ciSup_le fun j => hbound i j
      · rintro _ ⟨j, rfl⟩; exact hbound k j
/-- **`ConditionallyCompleteLinearOrderBot`, no `Nonempty` needed.** Same shape as `cdiag_bdd` but
with the primed `ciSup_le'` lemmas, which do not require the index to be nonempty (the empty
supremum is `⊥`). This is the golfed form of `Diagonal.ciSup₂_eq_ciSup_diagonal'`. -/
theorem cdiag_bdd_bot [ConditionallyCompleteLinearOrderBot α] (f : ι → ι → α)
    (hf : BddAbove (Set.range fun k => f k k)) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  obtain ⟨b, hb⟩ := id hf
  have hbound : ∀ i j, f i j ≤ b := fun i j => (h i j).choose_spec.trans (hb ⟨_, rfl⟩)
  refine le_antisymm (ciSup_le' fun i => ciSup_le' fun j => ?_) (ciSup_le' fun k => ?_)
  · obtain ⟨k, hk⟩ := h i j; exact hk.trans (le_ciSup hf k)
  · refine le_ciSup_of_le ⟨b, ?_⟩ k (le_ciSup ⟨b, ?_⟩ k)
    · rintro _ ⟨i, rfl⟩; exact ciSup_le' fun j => hbound i j
    · rintro _ ⟨j, rfl⟩; exact hbound k j
end CondComplete
/-! ## §4. The `+` callers
The whole reason the diagonal lemma exists: `iSup f + iSup g` distributes into a double supremum,
which collapses to the diagonal exactly when the sum is cofinal along it. Below, each caller is
shown reusing the *canonical* `Diagonal` lemmas (imported at the top), demonstrating the
decomposition axis — the interesting content is `simp_rw` distributing the `+`, then a one-line
appeal to the reusable core. -/
section Callers
variable {ι : Type*}
/-- **`ENat` caller, `rcases` split.** Distribute with `ENat.iSup_add`/`ENat.add_iSup`, then hand
off to the canonical `iSup₂_eq_diagonal`. -/
theorem enat_add {f g : ι → ENat} (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  rcases isEmpty_or_nonempty ι with _ | _
  · simp
  · simp_rw [ENat.iSup_add, ENat.add_iSup]
    exact iSup₂_eq_diagonal (fun i j => f i + g j) h
/-- **`ENNReal` caller, reusing the local §2 lemma `diag_sSup` instead of the canonical one.**
Shows that the caller does not care *which* proof of the diagonal collapse it invokes. -/
theorem ennreal_add {f g : ι → ENNReal} (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  rcases isEmpty_or_nonempty ι with _ | _
  · simp
  · simp_rw [ENNReal.iSup_add, ENNReal.add_iSup]
    exact diag_sSup (fun i j => f i + g j) h
/-- **`ENNReal` infimum caller (the dual).** Distribute with the `iInf` lemmas and defer to the
`to_dual`-generated `iInf₂_eq_diagonal`. Mirror image of `ennreal_add`. -/
theorem ennreal_iInf_add {f g : ι → ENNReal} (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) :
    iInf f + iInf g = ⨅ i, f i + g i := by
  rcases isEmpty_or_nonempty ι with _ | _
  · simp only [iInf_of_empty, top_add]
  · simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
    exact iInf₂_eq_diagonal (fun i j => f i + g j) h
/-- **`Cardinal` caller, conditionally-complete.** `Cardinal` is a
`ConditionallyCompleteLinearOrderBot`, so this uses the local `cdiag_bdd_bot`; the only real work is
manufacturing the `BddAbove` witness `bf + bg` for the diagonal from the two given bounds. -/
theorem cardinal_add [Nonempty ι] (f g : ι → Cardinal)
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ i, f i + g i := by
  rw [Cardinal.ciSup_add_ciSup f hf g hg]
  refine cdiag_bdd_bot (fun i j => f i + g j) ?_ h
  obtain ⟨bf, hbf⟩ := hf
  obtain ⟨bg, hbg⟩ := hg
  exact ⟨bf + bg, by rintro _ ⟨k, rfl⟩; exact add_le_add (hbf ⟨k, rfl⟩) (hbg ⟨k, rfl⟩)⟩
end Callers
/-! ## §5. The set-level `IsCofinalFor` form
The most structural statement: mutually cofinal *sets* have equal `sSup`. Everything in §1 is a
corollary obtained by transporting the hypotheses to the ranges. Here we show the point-free term
proof, the tactic proof, the dual, and the "§1 as a corollary" reduction. -/
section SetLevel
variable {α : Type*}
/-- **Point-free term proof.** The two `≤`-halves are `sSup_le_sSup_of_isCofinalFor` applied to each
cofinality hypothesis, glued by `.antisymm` — no argument named, no tactic block. This is the
equality companion of Mathlib's existing inequality lemma. -/
theorem sSup_eq_of_cofinal [CompleteSemilatticeSup α] {s t : Set α}
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) : sSup s = sSup t :=
  (sSup_le_sSup_of_isCofinalFor hst).antisymm (sSup_le_sSup_of_isCofinalFor hts)
/-- **Same fact, backward tactic mode.** `apply le_antisymm` then discharge each side with the
inequality lemma — the pointful counterpart of `sSup_eq_of_cofinal`. -/
theorem sSup_eq_of_cofinal_tac [CompleteSemilatticeSup α] {s t : Set α}
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) : sSup s = sSup t := by
  apply le_antisymm
  · exact sSup_le_sSup_of_isCofinalFor hst
  · exact sSup_le_sSup_of_isCofinalFor hts
/-- **The dual, point-free.** `IsCoinitialFor` ⇒ equal `sInf`. Stated manually (the `≤`-half lemmas
are not `to_dual`-linked in Mathlib); note the swapped argument order forced by
`sInf_le_sInf_of_isCoinitialFor`'s direction. -/
theorem sInf_eq_of_coinitial [CompleteSemilatticeInf α] {s t : Set α}
    (hst : IsCoinitialFor s t) (hts : IsCoinitialFor t s) : sInf s = sInf t :=
  (sInf_le_sInf_of_isCoinitialFor hts).antisymm (sInf_le_sInf_of_isCoinitialFor hst)
/-- **§1 recovered as a corollary of §5.** Unfolding `iSup` to `sSup (range …)` turns the indexed
statement into the set-level one; mutual cofinality of the *families* is exactly mutual cofinality
of the *ranges*. This makes precise the claim that the set form is the more structural home. -/
theorem cofinal_iSup_eq_from_sets [CompleteSemilatticeSup α] {ι ι' : Sort*}
    {f : ι → α} {g : ι' → α}
    (h₁ : ∀ i, ∃ i', f i ≤ g i') (h₂ : ∀ i', ∃ i, g i' ≤ f i) :
    ⨆ i, f i = ⨆ i', g i' := by
  rw [iSup, iSup]
  refine sSup_eq_of_cofinal ?_ ?_
  · rintro _ ⟨i, rfl⟩; obtain ⟨i', hi'⟩ := h₁ i; exact ⟨g i', ⟨i', rfl⟩, hi'⟩
  · rintro _ ⟨i', rfl⟩; obtain ⟨i, hi⟩ := h₂ i'; exact ⟨f i, ⟨i, rfl⟩, hi⟩
/-- **A `to_dual`-generated pair.** Writing the `sup` diagonal collapse with `@[to_dual]` makes Lean
synthesize the `inf` version automatically — demonstrating the "one proof, two theorems" attribute
mechanism from the supplement guide. -/
@[to_dual]
theorem sSup_diag_auto {ι : Sort*} [CompleteSemilatticeSup α] (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f i j ≤ f k k) : (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  apply le_antisymm
  · apply sSup_le; rintro _ ⟨i, rfl⟩; apply sSup_le; rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j; exact hk.trans (le_sSup ⟨k, rfl⟩)
  · apply sSup_le; rintro _ ⟨k, rfl⟩
    exact (le_sSup (s := range (f k)) ⟨k, rfl⟩).trans (le_sSup ⟨k, rfl⟩)
end SetLevel
end DiagonalVariations
