import RequestProject.Applications

/-!
# Variations: the same theorems, proved many different ways

This file is a catalogue of *alternative proofs* of the results in
`RequestProject.Diagonal` and `RequestProject.Applications`. Each block proves one
statement several times, deliberately moving along the axes of the "proof design
space":

```
Style:         term ←————————→ tactic
Automation:    manual ←————————→ automated
Direction:     forward ←————————→ backward
Granularity:   one-liner ←————————→ several `have`s and a `calc`
Decomposition: monolithic ←————————→ built on named helpers
```

The versions carried in `RequestProject.Diagonal` / `RequestProject.Applications` are
the shortest ones; the variants here document what the other choices look like, and
they are all checked by the compiler.
-/

namespace Golf.Variations

open Set
open scoped ENNReal

variable {α : Type*} {ι κ ν : Sort*}

/-! ## 1. The mutual-cofinality lemma

`⨆ i, ⨆ j, F i j = ⨆ k, G k` when `F` and `G` are mutually cofinal. -/

section Cofinal

variable [CompleteLattice α] (F : ι → κ → α) (G : ν → α)

/-- **v₁ — maximal golf, term mode.** Both halves are a single monotonicity lemma;
this is the version exported as `Golf.iSup₂_eq_iSup_of_cofinal`. -/
theorem cofinal_v₁ (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k :=
  le_antisymm (iSup_le fun i => iSup_mono' (hle i))
    (iSup_mono' fun k => (hge k).imp fun _ ⟨j, h⟩ => h.trans (le_iSup _ j))

/-- **v₂ — term mode, spelled out with `iSup₂_le` / `le_iSup₂`.** Same skeleton, but the
witnesses are extracted by `Exists.elim` instead of being threaded through `iSup_mono'`. -/
theorem cofinal_v₂ (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k :=
  le_antisymm
    (iSup₂_le fun i j => (hle i j).elim fun k hk => hk.trans (le_iSup G k))
    (iSup_le fun k => (hge k).elim fun i ⟨j, hij⟩ => hij.trans (le_iSup₂ (f := F) i j))

/-- **v₃ — backward tactic proof.** `refine` opens the two inequalities, `obtain`
destructs the cofinality witnesses. -/
theorem cofinal_v₃ (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k := by
  refine le_antisymm (iSup₂_le fun i j => ?_) (iSup_le fun k => ?_)
  · obtain ⟨k, hk⟩ := hle i j
    exact hk.trans (le_iSup G k)
  · obtain ⟨i, j, hij⟩ := hge k
    exact le_iSup_of_le i (le_iSup_of_le j hij)

/-- **v₄ — `simp`-normalise the goal first.** `le_antisymm_iff` plus `iSup_le_iff` turn the
equality into a pair of universally quantified inequalities, which are then supplied
as an anonymous constructor. -/
theorem cofinal_v₄ (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k := by
  simp only [le_antisymm_iff, iSup_le_iff]
  exact ⟨fun i j => (hle i j).elim fun k hk => hk.trans (le_iSup G k),
    fun k => (hge k).elim fun i ⟨j, h⟩ => le_iSup_of_le i (le_iSup_of_le j h)⟩

/-- **v₅ — maximally verbose, forward + `calc`.** The two inequalities become named
hypotheses and each chain of `≤` is written out. -/
theorem cofinal_v₅ (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k := by
  have forward : ⨆ i, ⨆ j, F i j ≤ ⨆ k, G k := by
    refine iSup_le fun i => iSup_le fun j => ?_
    rcases hle i j with ⟨k, hk⟩
    calc F i j ≤ G k := hk
      _ ≤ ⨆ k, G k := le_iSup G k
  have backward : ⨆ k, G k ≤ ⨆ i, ⨆ j, F i j := by
    refine iSup_le fun k => ?_
    rcases hge k with ⟨i, j, hij⟩
    calc G k ≤ F i j := hij
      _ ≤ ⨆ j, F i j := le_iSup (F i) j
      _ ≤ ⨆ i, ⨆ j, F i j := le_iSup (fun i => ⨆ j, F i j) i
  exact le_antisymm forward backward

/-- **v₆ — one `apply`, two goals closed by the same combinator.** `<;>` plus a
`first`-style alternation keeps the proof to a single tactic block. -/
theorem cofinal_v₆ (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k := by
  apply le_antisymm <;>
    [exact iSup₂_le fun i j => Exists.elim (hle i j) fun k hk => le_iSup_of_le k hk;
     exact iSup_le fun k => Exists.elim (hge k) fun i hi =>
       Exists.elim hi fun j hj => le_iSup_of_le i (le_iSup_of_le j hj)]

end Cofinal

/-! ## 2. The diagonal corollary -/

section Diagonal

variable [CompleteLattice α] (F : ι → ι → α)

/-- **v₁ — as a corollary.** The diagonal family is cofinal in itself, witnessed by
`⟨k, k, le_rfl⟩`; this is the exported proof. -/
theorem diagonal_v₁ (h : ∀ i j, ∃ k, F i j ≤ F k k) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  Golf.iSup₂_eq_iSup_of_cofinal F _ h fun k => ⟨k, k, le_rfl⟩

/-- **v₂ — standalone, no helper.** Note how much simpler the `≥` half becomes once
`G = fun k => F k k`: the witness is `k` itself. -/
theorem diagonal_v₂ (h : ∀ i j, ∃ k, F i j ≤ F k k) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  le_antisymm (iSup_le fun i => iSup_mono' (h i)) (iSup_mono' fun k => ⟨k, le_iSup (F k) k⟩)

/-- **v₃ — tactic mode with `iSup₂_le`.** -/
theorem diagonal_v₃ (h : ∀ i j, ∃ k, F i j ≤ F k k) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k := by
  refine le_antisymm (iSup₂_le fun i j => ?_) (iSup_le fun k => ?_)
  · obtain ⟨k, hk⟩ := h i j
    exact hk.trans (le_iSup (fun k => F k k) k)
  · exact le_iSup_of_le k (le_iSup (F k) k)

/-- **v₄ — via `rw` on the general lemma.** Sometimes the cheapest golf is not to prove
anything at all, but to rewrite with the abstraction. -/
theorem diagonal_v₄ (h : ∀ i j, ∃ k, F i j ≤ F k k) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k := by
  rw [Golf.iSup₂_eq_iSup_of_cofinal F (fun k => F k k) h fun k => ⟨k, k, le_rfl⟩]

/-- **v₅ — by duality.** The `⨅` statement on `αᵒᵈ` *is* the `⨆` statement, so the dual
lemma proves it verbatim. -/
theorem diagonal_v₅ (h : ∀ i j, ∃ k, F i j ≤ F k k) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  Golf.iInf₂_eq_iInf_diagonal (α := αᵒᵈ) F h

end Diagonal

/-! ## 3. The binary-operation form

Here the golfing consists in *pushing the abstraction one level up*: the operation `op`
and its two distributivity laws are parameters, so no `fun i j ↦ f i + g j` lambda has
to be written by the caller. -/

section Op

variable [CompleteLattice α] {f g : ι → α}

/-- **v₁ — a `trans` chain in term mode** (the exported proof). -/
theorem op_v₁ (op : α → α → α)
    (hl : ∀ (f : ι → α) (a : α), op (⨆ i, f i) a = ⨆ i, op (f i) a)
    (hr : ∀ (a : α) (g : ι → α), op a (⨆ j, g j) = ⨆ j, op a (g j))
    (h : ∀ i j, ∃ k, op (f i) (g j) ≤ op (f k) (g k)) :
    op (⨆ i, f i) (⨆ j, g j) = ⨆ k, op (f k) (g k) :=
  (hl f _).trans <| (iSup_congr fun i => hr (f i) g).trans <| Golf.iSup₂_eq_iSup_diagonal _ h

/-- **v₂ — `rw` then `simp_rw` then one lemma.** The two distributivity laws are used as
rewrite rules; `simp_rw` is needed for the second one because it fires under a binder. -/
theorem op_v₂ (op : α → α → α)
    (hl : ∀ (f : ι → α) (a : α), op (⨆ i, f i) a = ⨆ i, op (f i) a)
    (hr : ∀ (a : α) (g : ι → α), op a (⨆ j, g j) = ⨆ j, op a (g j))
    (h : ∀ i j, ∃ k, op (f i) (g j) ≤ op (f k) (g k)) :
    op (⨆ i, f i) (⨆ j, g j) = ⨆ k, op (f k) (g k) := by
  rw [hl]
  simp_rw [hr]
  exact Golf.iSup₂_eq_iSup_diagonal _ h

/-- **v₃ — a single `simp_rw`.** Both rewrites in one call. -/
theorem op_v₃ (op : α → α → α)
    (hl : ∀ (f : ι → α) (a : α), op (⨆ i, f i) a = ⨆ i, op (f i) a)
    (hr : ∀ (a : α) (g : ι → α), op a (⨆ j, g j) = ⨆ j, op a (g j))
    (h : ∀ i j, ∃ k, op (f i) (g j) ≤ op (f k) (g k)) :
    op (⨆ i, f i) (⨆ j, g j) = ⨆ k, op (f k) (g k) := by
  simp_rw [hl, hr]
  exact Golf.iSup₂_eq_iSup_diagonal _ h

/-- **v₄ — textbook `calc`.** The three steps of the argument, named. -/
theorem op_v₄ (op : α → α → α)
    (hl : ∀ (f : ι → α) (a : α), op (⨆ i, f i) a = ⨆ i, op (f i) a)
    (hr : ∀ (a : α) (g : ι → α), op a (⨆ j, g j) = ⨆ j, op a (g j))
    (h : ∀ i j, ∃ k, op (f i) (g j) ≤ op (f k) (g k)) :
    op (⨆ i, f i) (⨆ j, g j) = ⨆ k, op (f k) (g k) :=
  calc op (⨆ i, f i) (⨆ j, g j)
      = ⨆ i, op (f i) (⨆ j, g j) := hl f _
    _ = ⨆ i, ⨆ j, op (f i) (g j) := iSup_congr fun i => hr (f i) g
    _ = ⨆ k, op (f k) (g k) := Golf.iSup₂_eq_iSup_diagonal _ h

end Op

/-! ## 4. Boundedness helpers (conditionally complete lattices) -/

section Bounded

variable [ConditionallyCompleteLattice α] {F : ι → ι → α}

/-- **v₁ — `BddAbove.imp`, term mode** (the exported proof): a bound for the diagonal *is*
a bound for every row. -/
theorem bddAbove_row_v₁ (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) (i : ι) : BddAbove (range (F i)) :=
  hb.imp fun _ hc =>
    forall_mem_range.2 fun j => (h i j).elim fun k hk => hk.trans (hc (mem_range_self k))

/-- **v₂ — forward tactic proof.** Destruct the bound, then produce it again. -/
theorem bddAbove_row_v₂ (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) (i : ι) : BddAbove (range (F i)) := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨c, ?_⟩
  rintro _ ⟨j, rfl⟩
  obtain ⟨k, hk⟩ := h i j
  exact hk.trans (hc ⟨k, rfl⟩)

/-- **v₃ — same bound, produced by `mem_upperBounds` + `simp`-style automation.** -/
theorem bddAbove_row_v₃ (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) (i : ι) : BddAbove (range (F i)) := by
  obtain ⟨c, hc⟩ := hb
  rw [mem_upperBounds] at hc
  simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hc
  exact ⟨c, by rintro _ ⟨j, rfl⟩; exact ((h i j).elim fun k hk => hk.trans (hc k))⟩

variable [Nonempty ι]

/-- **v₁ — the row-suprema bound, inlined.** -/
theorem bddAbove_ciSup_row_v₁ (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : BddAbove (range fun i => ⨆ j, F i j) :=
  hb.imp fun _ hc =>
    forall_mem_range.2 fun i =>
      ciSup_le fun j => (h i j).elim fun k hk => hk.trans (hc (mem_range_self k))

/-- **v₂ — the same, built on `bddAbove_row_v₁`.** Each row is bounded, so each row
supremum is below the diagonal supremum. -/
theorem bddAbove_ciSup_row_v₂ (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : BddAbove (range fun i => ⨆ j, F i j) := by
  refine ⟨⨆ k, F k k, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact ciSup_le fun j => (h i j).elim fun k hk => hk.trans (le_ciSup hb k)

end Bounded

/-! ## 5. The conditionally complete diagonal collapse -/

section CDiagonal

variable [ConditionallyCompleteLattice α] [Nonempty ι] (F : ι → ι → α)

/-- **v₁ — term mode** (the exported proof), using the two boundedness helpers. -/
theorem cdiagonal_v₁ (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  le_antisymm
    (ciSup_le fun i => ciSup_le fun j => (h i j).elim fun k hk => hk.trans (le_ciSup hb k))
    (ciSup_le fun k =>
      (le_ciSup (Golf.bddAbove_row h hb k) k).trans
        (le_ciSup (Golf.bddAbove_range_ciSup_row h hb) k))

/-- **v₂ — tactic mode with `le_ciSup_of_le`.** -/
theorem cdiagonal_v₂ (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k := by
  refine le_antisymm (ciSup_le fun i => ciSup_le fun j => ?_) (ciSup_le fun k => ?_)
  · obtain ⟨k, hk⟩ := h i j
    exact hk.trans (le_ciSup hb k)
  · exact le_ciSup_of_le (Golf.bddAbove_range_ciSup_row h hb) k
      (le_ciSup (Golf.bddAbove_row h hb k) k)

/-- **v₃ — structured, with the two directions as named `have`s and a `calc`.** -/
theorem cdiagonal_v₃ (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k := by
  have rows : ∀ i, ⨆ j, F i j ≤ ⨆ k, F k k := fun i =>
    ciSup_le fun j => (h i j).elim fun k hk => hk.trans (le_ciSup hb k)
  have diag : ∀ k, F k k ≤ ⨆ i, ⨆ j, F i j := fun k =>
    calc F k k ≤ ⨆ j, F k j := le_ciSup (Golf.bddAbove_row h hb k) k
      _ ≤ ⨆ i, ⨆ j, F i j := le_ciSup (Golf.bddAbove_range_ciSup_row h hb) k
  exact le_antisymm (ciSup_le rows) (ciSup_le diag)

/-- **v₄ — high-automation flavour**: `grw` rewrites along the inequality witness, so no
`trans` has to be named. -/
theorem cdiagonal_v₄ (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k := by
  apply le_antisymm
  · refine ciSup_le fun i => ciSup_le fun j => ?_
    obtain ⟨k, hk⟩ := h i j
    grw [hk]
    exact le_ciSup hb k
  · exact ciSup_le fun k => le_ciSup_of_le (Golf.bddAbove_range_ciSup_row h hb) k
      (le_ciSup (Golf.bddAbove_row h hb k) k)

end CDiagonal

/-! ## 6. Boundedness of a sum of families -/

section BddAdd

variable {β : Type*} {J : Type*} [Preorder β] [Add β]
  [CovariantClass β β (· + ·) (· ≤ ·)] [CovariantClass β β (Function.swap (· + ·)) (· ≤ ·)]
  {f g : J → β}

/-- **v₁ — reuse `BddAbove.add` and `BddAbove.mono`** (the exported proof). -/
theorem bddAbove_add_v₁ (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    BddAbove (range fun k => f k + g k) :=
  hf.add hg |>.mono <| by
    rintro _ ⟨k, rfl⟩
    exact ⟨f k, mem_range_self k, g k, mem_range_self k, rfl⟩

/-- **v₂ — build the bound by hand.** The witness is the sum of the two bounds. -/
theorem bddAbove_add_v₂ (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    BddAbove (range fun k => f k + g k) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact add_le_add (ha (mem_range_self k)) (hb (mem_range_self k))

/-- **v₃ — the same witness, term mode.** -/
theorem bddAbove_add_v₃ (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    BddAbove (range fun k => f k + g k) :=
  hf.elim fun a ha => hg.elim fun b hb =>
    ⟨a + b, forall_mem_range.2 fun k =>
      add_le_add (ha (mem_range_self k)) (hb (mem_range_self k))⟩

end BddAdd

/-! ## 7. `Cardinal`: the payoff

With the abstraction in place, the cardinal statement is a rewrite and one lemma; the
boundedness side condition is discharged by the packaged helper. -/

section Cardinal

universe u v

variable {ι : Type u} [Nonempty ι] {f g : ι → Cardinal.{v}}

/-- **v₁ — `rw` + one lemma** (the exported proof). -/
theorem cardinal_v₁ (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  rw [Cardinal.ciSup_add_ciSup f hf g hg]
  exact Golf.ciSup₂_eq_ciSup_diagonal _ h (Golf.bddAbove_range_add hf hg)

/-- **v₂ — the same as a `trans` in term mode.** -/
theorem cardinal_v₂ (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  (Cardinal.ciSup_add_ciSup f hf g hg).trans <|
    Golf.ciSup₂_eq_ciSup_diagonal _ h (Golf.bddAbove_range_add hf hg)

/-- **v₃ — `simpa … using`,** as suggested by the packaging idea: state the diagonal
collapse for `fun i j ↦ f i + g j` and let `simp` do the bookkeeping. -/
theorem cardinal_v₃ (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  simpa [Cardinal.ciSup_add_ciSup f hf g hg] using
    Golf.ciSup₂_eq_ciSup_diagonal (fun i j => f i + g j) h (Golf.bddAbove_range_add hf hg)

/-- **v₄ — `calc`, for the reader who wants to see the two steps.** -/
theorem cardinal_v₄ (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  calc (⨆ i, f i) + (⨆ j, g j)
      = ⨆ i, ⨆ j, f i + g j := Cardinal.ciSup_add_ciSup f hf g hg
    _ = ⨆ k, f k + g k :=
        Golf.ciSup₂_eq_ciSup_diagonal _ h (Golf.bddAbove_range_add hf hg)

end Cardinal

/-! ## 8. `ℝ≥0∞`: three ways to the same statement -/

section ENNReal

variable {ι : Type*} [Nonempty ι] {f g : ι → ℝ≥0∞}

/-- **v₁ — through the operation-level abstraction**, point-free in the operation:
the lambda `fun i j ↦ f i + g j` never appears. -/
theorem ennreal_v₁ (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  Golf.iSup_op_iSup_diagonal (· + ·) (fun f _ => ENNReal.iSup_add f)
    (fun _ g => ENNReal.add_iSup g) h

/-- **v₂ — through the lattice-level abstraction**, distributing by hand first. -/
theorem ennreal_v₂ (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  rw [ENNReal.iSup_add]
  simp_rw [ENNReal.add_iSup]
  exact Golf.iSup₂_eq_iSup_diagonal _ h

/-- **v₃ — no abstraction at all**, the fully unfolded argument. -/
theorem ennreal_v₃ (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  refine le_antisymm ?_ (iSup_le fun k => add_le_add (le_iSup f k) (le_iSup g k))
  rw [ENNReal.iSup_add]
  refine iSup_le fun i => ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun j => ?_
  obtain ⟨k, hk⟩ := h i j
  exact hk.trans (le_iSup (fun k => f k + g k) k)

end ENNReal

/-! ## 9. Point-free flourishes

Where the library lemma already has exactly the shape the abstraction wants, it can be
passed as a value: no `fun` at all. And `Function.swap` turns the abstraction into its
mirror image for free. -/

section PointFree

variable {ι : Type*} {f g : ι → ℝ≥0∞}

/-- `ENNReal.iSup_mul` and `ENNReal.mul_iSup` already *are* the two distributivity
hypotheses, so the proof is an application with no lambdas. -/
theorem ennreal_mul_pointfree (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ k, f k * g k :=
  Golf.iSup_op_iSup_diagonal (· * ·) ENNReal.iSup_mul ENNReal.mul_iSup h

/-- The mirrored statement, obtained by feeding `Function.swap (· * ·)` to the same lemma
with the two distributivity laws exchanged. -/
theorem ennreal_mul_swap (h : ∀ i j, ∃ k, g j * f i ≤ g k * f k) :
    (⨆ j, g j) * (⨆ i, f i) = ⨆ k, g k * f k :=
  Golf.iSup_op_iSup_diagonal (Function.swap (· * ·)) (fun g a => ENNReal.mul_iSup a g)
    (fun a f => ENNReal.iSup_mul f a) h

end PointFree

/-! ## 10. Bridge variations

The same statements again, but now proved by *changing context*: crossing to sets, to a
linear order, to the opposite order, or to the category of a complete lattice.  See
`RequestProject.Bridges` for the bridges themselves. -/

section Bridges

open Golf.Bridge

/-- **v₇ of §1 — the set bridge.** `⨆` is `sSup ∘ range`, so mutual cofinality of the
families is Mathlib's `IsCofinalFor` on their ranges. -/
theorem cofinal_v₇ [CompleteLattice α] (F : ι → κ → α) (G : ν → α)
    (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k :=
  (Golf.iSup_pprod F).trans <| Golf.Bridge.sSup_eq_sSup_of_isCofinalFor
    (Golf.isCofinalFor_range_iff.2 fun p => hle p.1 p.2)
    (Golf.isCofinalFor_range_iff.2 fun k => (hge k).elim fun i ⟨j, h⟩ => ⟨⟨i, j⟩, h⟩)

/-- **v₆ of §2 — currying, then the set bridge.** -/
theorem diagonal_v₆ [CompleteLattice α] (F : ι → ι → α) (h : ∀ i j, ∃ k, F i j ≤ F k k) :
    ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  (Golf.iSup_pprod F).trans <|
    Golf.Bridge.iSup_eq_iSup_of_cofinal' (fun p => h p.1 p.2) fun k => ⟨⟨k, k⟩, le_rfl⟩

/-- **v₅ of §5 — the linear-order bridge.** In a conditionally complete *linear* order
the cofinality half needs no boundedness whatsoever; only the currying step does. -/
theorem cdiagonal_v₅ {α : Type*} [ConditionallyCompleteLinearOrder α] [Nonempty ι]
    (F : ι → ι → α) (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  ciSup₂_eq_ciSup_diagonal_of_linear F h hb

/-- **v₅ of §7 — cardinals through the linear-order bridge.** `Cardinal` is linearly
ordered, so this route is available and avoids one boundedness argument. -/
theorem cardinal_v₅ {ι : Type*} [Nonempty ι] {f g : ι → Cardinal.{0}}
    (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  (Cardinal.ciSup_add_ciSup f hf g hg).trans <|
    ciSup₂_eq_ciSup_diagonal_of_linear _ h (Golf.bddAbove_range_add hf hg)

/-- **v₄ of §8 — the `ℝ≥0∞` statement for monotone families, categorically.** The
diagonal hypothesis is replaced by monotonicity, and the collapse is finality of the
diagonal functor. -/
theorem ennreal_v₄ {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {f g : ι → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  Golf.ennreal_iSup_add_iSup_of_monotone hf hg

/-- **v₅ of §8 — the same, order-theoretically**: directedness supplies the witness. -/
theorem ennreal_v₅ {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {f g : ι → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  Golf.ennreal_iSup_add_iSup fun i j =>
    (exists_ge_ge i j).imp fun _ hk => add_le_add (hf hk.1) (hg hk.2)

/-- **v₆ of §8 — pushed along a non-faithful map.** `ENNReal.ofNNReal`-style transports:
any `sSupHom` carries the collapse forward, injective or not. -/
theorem ennreal_v₆ {β : Type*} [CompleteLattice β] (e : sSupHom ℝ≥0∞ β) {ι : Type*}
    {f g : ι → ℝ≥0∞} (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    ⨆ i, ⨆ j, e (f i + g j) = ⨆ k, e (f k + g k) :=
  sSupHom_iSup₂_eq_iSup_diagonal e (fun i j => f i + g j) h

end Bridges

/-! ## 11. Variations on the two new structural lemmas

Currying and "boundedness travels down cofinality" are the two new atoms of
`RequestProject.Diagonal`; here they are, each proved along a different axis. -/

section Structural

/-- **v₁ — term mode, two monotonicity steps** (the exported proof). -/
theorem pprod_v₁ [CompleteLattice α] (F : ι → κ → α) :
    ⨆ i, ⨆ j, F i j = ⨆ p : PProd ι κ, F p.1 p.2 :=
  le_antisymm (iSup₂_le fun i j => le_iSup (fun p : PProd ι κ => F p.1 p.2) ⟨i, j⟩)
    (iSup_le fun p => le_iSup₂ (f := F) p.1 p.2)

/-- **v₂ — normalisation first**: `simp only [le_antisymm_iff, iSup_le_iff]` turns the
equality into a pair of quantified inequalities, supplied by an anonymous constructor. -/
theorem pprod_v₂ [CompleteLattice α] (F : ι → κ → α) :
    ⨆ i, ⨆ j, F i j = ⨆ p : PProd ι κ, F p.1 p.2 := by
  simp only [le_antisymm_iff, iSup_le_iff]
  exact ⟨fun i j => le_iSup (fun p : PProd ι κ => F p.1 p.2) ⟨i, j⟩,
    fun p => le_iSup₂ (f := F) p.1 p.2⟩

/-- **v₃ — backward, one `refine` and two witnesses.** -/
theorem pprod_v₃ [CompleteLattice α] (F : ι → κ → α) :
    ⨆ i, ⨆ j, F i j = ⨆ p : PProd ι κ, F p.1 p.2 := by
  refine le_antisymm (iSup₂_le fun i j => ?_) (iSup_le fun p => ?_)
  · exact le_iSup (fun p : PProd ι κ => F p.1 p.2) ⟨i, j⟩
  · exact le_iSup_of_le p.1 (le_iSup (F p.1) p.2)

/-- **v₁ — term mode** (the exported proof): a bound for `t` is a bound for `s`. -/
theorem cofinalBdd_v₁ [Preorder α] {s t : Set α} (h : IsCofinalFor s t) (ht : BddAbove t) :
    BddAbove s :=
  ht.imp fun _ hc => upperBounds_mono_of_isCofinalFor h hc

/-- **v₂ — forward, unpacking the bound by hand.** -/
theorem cofinalBdd_v₂ [Preorder α] {s t : Set α} (h : IsCofinalFor s t) (ht : BddAbove t) :
    BddAbove s := by
  obtain ⟨c, hc⟩ := ht
  refine ⟨c, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := h hx
  exact hxy.trans (hc hy)

/-- **v₃ — `gcongr`-flavoured**: monotonicity of `upperBounds` is a `gcongr` lemma, so the
whole content is that one rewrite. -/
theorem cofinalBdd_v₃ [Preorder α] {s t : Set α} (h : IsCofinalFor s t) (ht : BddAbove t) :
    BddAbove s :=
  Set.Nonempty.mono (upperBounds_mono_of_isCofinalFor h) ht

end Structural

end Golf.Variations
