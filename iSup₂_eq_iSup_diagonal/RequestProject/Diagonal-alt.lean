import Mathlib

/-!
# Diagonal collapse for iterated suprema and infima

This file isolates the *abstraction* behind statements such as
`ENNReal.iSup_add_iSup` and `Cardinal.ciSup_add_ciSup`: an iterated supremum
`⨆ i, ⨆ j, F i j` collapses to a single supremum `⨆ k, F k k` as soon as every
entry `F i j` is dominated by some diagonal entry `F k k`.

The development is deliberately cut into *one-step* lemmas, each doing a single
algebraic manipulation or logical deduction, so that the whole argument is a small
DAG.  Nodes are tagged:

| Tag           | Meaning                              |
| ------------- | ------------------------------------ |
| 🧩 atomic     | Mathlib or one tactic                |
| 🔁 reducible  | an iso/dual/rewrite collapses it     |
| 🌿 local-glue | small composition                    |
| 🌌 structural | introduces a new invariant           |

The two structural ideas are *currying* (`Golf.iSup_pprod`, `Golf.ciSup_pprod`: the
double index is a single index over a product) and *cofinality*
(`Golf.iSup_eq_iSup_of_cofinal`: mutually cofinal families have equal suprema —
Mathlib's `IsCofinalFor` is exactly this relation).  Everything else is glue or duality.

## Main results

* `Golf.iSup_eq_iSup_of_cofinal` — the engine: mutually cofinal families, equal suprema.
* `Golf.iSup_pprod` — the currying bridge `⨆ i, ⨆ j ↝ ⨆ (i, j)`.
* `Golf.iSup₂_eq_iSup_diagonal` — the diagonal corollary, with its dual
  `Golf.iInf₂_eq_iInf_diagonal`.
* `Golf.iSup_op_iSup_diagonal` — the binary-operation form: no `fun i j ↦ f i + g j`
  lambda has to be written at the call site.
* `Golf.ciSup₂_eq_ciSup_diagonal` — the conditionally complete counterpart, where the
  only extra ingredient is boundedness, and it enters exactly once (in `ciSup_pprod`).

Alternative proofs live in `RequestProject.Variations`; transports of these statements
to other contexts (duals, order isos, adjunctions, colimits) live in
`RequestProject.Bridges`, and the dependency DAG itself is drawn as a graph in
`RequestProject.ProofGraph`.
-/

namespace Golf

open Set

variable {α : Type*} {ι κ ν : Sort*}

/-! ### Cofinality, the Mathlib way

`IsCofinalFor s t` (`∀ a ∈ s, ∃ b ∈ t, a ≤ b`) is Mathlib's name for the relation that
drives every proof below.  Two atoms translate between it and indexed families. -/

section Preorder

variable [Preorder α]

/-- 🧩 Cofinality of ranges is cofinality of families. -/
@[simp]
theorem isCofinalFor_range_iff {f : ι → α} {g : κ → α} :
    IsCofinalFor (range f) (range g) ↔ ∀ i, ∃ j, f i ≤ g j := by
  simp [IsCofinalFor]

/-- 🧩 Boundedness travels down cofinality. -/
theorem IsCofinalFor.bddAbove {s t : Set α} (h : IsCofinalFor s t) (ht : BddAbove t) :
    BddAbove s :=
  ht.imp fun _ hc => upperBounds_mono_of_isCofinalFor h hc

end Preorder

/-! ### Complete lattices -/

section CompleteLattice

variable [CompleteLattice α]

/-- 🌌 **Currying.** A doubly indexed supremum is a supremum over the product index. -/
theorem iSup_pprod (F : ι → κ → α) : ⨆ i, ⨆ j, F i j = ⨆ p : PProd ι κ, F p.1 p.2 :=
  le_antisymm (iSup₂_le fun i j => le_iSup (fun p : PProd ι κ => F p.1 p.2) ⟨i, j⟩)
    (iSup_le fun p => le_iSup₂ (f := F) p.1 p.2)

/-- 🌌 **Cofinality.** Mutually cofinal families have the same supremum. -/
theorem iSup_eq_iSup_of_cofinal {f : ι → α} {g : κ → α} (h₁ : ∀ i, ∃ j, f i ≤ g j)
    (h₂ : ∀ j, ∃ i, g j ≤ f i) : ⨆ i, f i = ⨆ j, g j :=
  le_antisymm (iSup_mono' h₁) (iSup_mono' h₂)

/-- 🌿 The two-index version: curry, then use cofinality. -/
theorem iSup₂_eq_iSup_of_cofinal (F : ι → κ → α) (G : ν → α)
    (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k :=
  (iSup_pprod F).trans <| iSup_eq_iSup_of_cofinal (fun p => hle p.1 p.2)
    fun k => (hge k).elim fun i ⟨j, h⟩ => ⟨⟨i, j⟩, h⟩

/-- 🔁 Dual of `Golf.iSup₂_eq_iSup_of_cofinal`. -/
theorem iInf₂_eq_iInf_of_cofinal (F : ι → κ → α) (G : ν → α)
    (hge : ∀ i j, ∃ k, G k ≤ F i j) (hle : ∀ k, ∃ i j, F i j ≤ G k) :
    ⨅ i, ⨅ j, F i j = ⨅ k, G k :=
  iSup₂_eq_iSup_of_cofinal (α := αᵒᵈ) F G hge hle

/-- 🔁 An iterated supremum collapses onto its diagonal as soon as every entry is
dominated by a diagonal entry: the diagonal is cofinal in the square. -/
theorem iSup₂_eq_iSup_diagonal (F : ι → ι → α) (h : ∀ i j, ∃ k, F i j ≤ F k k) :
    ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  iSup₂_eq_iSup_of_cofinal F _ h fun k => ⟨k, k, le_rfl⟩

/-- 🔁 Dual of `Golf.iSup₂_eq_iSup_diagonal`. -/
theorem iInf₂_eq_iInf_diagonal (F : ι → ι → α) (h : ∀ i j, ∃ k, F k k ≤ F i j) :
    ⨅ i, ⨅ j, F i j = ⨅ k, F k k :=
  iInf₂_eq_iInf_of_cofinal F _ h fun k => ⟨k, k, le_rfl⟩

/-- 🌿 The binary-operation form of `Golf.iSup₂_eq_iSup_diagonal`: if `op` commutes with
suprema in each argument, then `op` of two suprema is the supremum of `op` along the
diagonal. -/
theorem iSup_op_iSup_diagonal {f g : ι → α} (op : α → α → α)
    (hl : ∀ (f : ι → α) (a : α), op (⨆ i, f i) a = ⨆ i, op (f i) a)
    (hr : ∀ (a : α) (g : ι → α), op a (⨆ j, g j) = ⨆ j, op a (g j))
    (h : ∀ i j, ∃ k, op (f i) (g j) ≤ op (f k) (g k)) :
    op (⨆ i, f i) (⨆ j, g j) = ⨆ k, op (f k) (g k) :=
  (hl f _).trans <| (iSup_congr fun i => hr (f i) g).trans <| iSup₂_eq_iSup_diagonal _ h

/-- 🔁 Dual of `Golf.iSup_op_iSup_diagonal`. -/
theorem iInf_op_iInf_diagonal {f g : ι → α} (op : α → α → α)
    (hl : ∀ (f : ι → α) (a : α), op (⨅ i, f i) a = ⨅ i, op (f i) a)
    (hr : ∀ (a : α) (g : ι → α), op a (⨅ j, g j) = ⨅ j, op a (g j))
    (h : ∀ i j, ∃ k, op (f k) (g k) ≤ op (f i) (g j)) :
    op (⨅ i, f i) (⨅ j, g j) = ⨅ k, op (f k) (g k) :=
  iSup_op_iSup_diagonal (α := αᵒᵈ) op hl hr h

end CompleteLattice

/-! ### Conditionally complete lattices

Exactly the same two structural steps — currying and cofinality — with boundedness as
the only extra hypothesis.  It is needed once, in `Golf.ciSup_pprod`; from there on the
argument is verbatim the complete-lattice one. -/

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [Nonempty ι] [Nonempty κ]

/-- 🌿 Cofinality in the conditionally complete world: the same statement as
`Golf.iSup_eq_iSup_of_cofinal`, with the two families assumed bounded. -/
theorem ciSup_eq_ciSup_of_cofinal {f : ι → α} {g : κ → α} (h₁ : ∀ i, ∃ j, f i ≤ g j)
    (h₂ : ∀ j, ∃ i, g j ≤ f i) (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    ⨆ i, f i = ⨆ j, g j :=
  le_antisymm (ciSup_le fun i => (h₁ i).elim fun j hj => hj.trans (le_ciSup hg j))
    (ciSup_le fun j => (h₂ j).elim fun i hi => hi.trans (le_ciSup hf i))

omit [Nonempty ι] [Nonempty κ] in
/-- 🧩 A row of a bounded family is bounded. -/
theorem bddAbove_range_row {F : ι → κ → α}
    (hb : BddAbove (range fun p : PProd ι κ => F p.1 p.2)) (i : ι) : BddAbove (range (F i)) :=
  hb.mono (range_subset_iff.2 fun j => mem_range_self (⟨i, j⟩ : PProd ι κ))

omit [Nonempty ι] in
/-- 🧩 The row suprema of a bounded family are bounded. -/
theorem bddAbove_range_ciSup {F : ι → κ → α}
    (hb : BddAbove (range fun p : PProd ι κ => F p.1 p.2)) :
    BddAbove (range fun i => ⨆ j, F i j) :=
  hb.imp fun _ hc => forall_mem_range.2 fun i =>
    ciSup_le fun j => hc (mem_range_self (⟨i, j⟩ : PProd ι κ))

/-- 🌌 **Currying**, conditionally complete version: the one place where boundedness is
used. -/
theorem ciSup_pprod (F : ι → κ → α) (hb : BddAbove (range fun p : PProd ι κ => F p.1 p.2)) :
    ⨆ i, ⨆ j, F i j = ⨆ p : PProd ι κ, F p.1 p.2 :=
  le_antisymm (ciSup_le fun i => ciSup_le fun j => le_ciSup hb (⟨i, j⟩ : PProd ι κ))
    (ciSup_le fun p =>
      (le_ciSup (bddAbove_range_row hb p.1) p.2).trans (le_ciSup (bddAbove_range_ciSup hb) p.1))

omit [Nonempty ι] [Nonempty κ] in
/-- 🔁 Under the diagonal hypothesis, the whole square is cofinal in the diagonal, hence
bounded as soon as the diagonal is. -/
theorem bddAbove_range_uncurry {F : ι → ι → α} (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) :
    BddAbove (range fun p : PProd ι ι => F p.1 p.2) :=
  IsCofinalFor.bddAbove (isCofinalFor_range_iff.2 fun p => h p.1 p.2) hb

omit [Nonempty κ] in
/-- 🌿 Conditionally complete version of `Golf.iSup₂_eq_iSup_diagonal`: curry, then
collapse the cofinal diagonal. -/
theorem ciSup₂_eq_ciSup_diagonal (F : ι → ι → α) (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) :
    ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  (ciSup_pprod F (bddAbove_range_uncurry h hb)).trans <|
    ciSup_eq_ciSup_of_cofinal (fun p => h p.1 p.2) (fun k => ⟨⟨k, k⟩, le_rfl⟩)
      (bddAbove_range_uncurry h hb) hb

omit [Nonempty κ] in
/-- 🌿 The binary-operation packaging, conditionally complete version: feed it the
distributivity law of the ambient theory (e.g. `Cardinal.ciSup_add_ciSup`) and it
returns the diagonal form. -/
theorem ciSup_op_ciSup_diagonal {f g : ι → α} (op : α → α → α)
    (hdist : op (⨆ i, f i) (⨆ j, g j) = ⨆ i, ⨆ j, op (f i) (g j))
    (h : ∀ i j, ∃ k, op (f i) (g j) ≤ op (f k) (g k))
    (hb : BddAbove (range fun k => op (f k) (g k))) :
    op (⨆ i, f i) (⨆ j, g j) = ⨆ k, op (f k) (g k) :=
  hdist.trans (ciSup₂_eq_ciSup_diagonal _ h hb)

omit [Nonempty κ] in
/-- 🔁 Dual of `Golf.ciSup₂_eq_ciSup_diagonal`. -/
theorem ciInf₂_eq_ciInf_diagonal (F : ι → ι → α) (h : ∀ i j, ∃ k, F k k ≤ F i j)
    (hb : BddBelow (range fun k => F k k)) :
    ⨅ i, ⨅ j, F i j = ⨅ k, F k k :=
  ciSup₂_eq_ciSup_diagonal (α := αᵒᵈ) F h hb

omit [Nonempty ι] [Nonempty κ] in
/-- 🔁 Every row of `F` is bounded above by any bound for the diagonal of `F`. -/
theorem bddAbove_row {F : ι → ι → α} (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) (i : ι) : BddAbove (range (F i)) :=
  bddAbove_range_row (bddAbove_range_uncurry h hb) i

omit [Nonempty κ] in
/-- 🔁 The family of row-suprema of `F` is bounded above by any bound for the diagonal. -/
theorem bddAbove_range_ciSup_row {F : ι → ι → α} (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : BddAbove (range fun i => ⨆ j, F i j) :=
  bddAbove_range_ciSup (bddAbove_range_uncurry h hb)

end ConditionallyCompleteLattice

end Golf
