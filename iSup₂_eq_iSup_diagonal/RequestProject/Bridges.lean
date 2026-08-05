import RequestProject.Diagonal

/-!
# Bridges: the same theorem seen in six different contexts

The "diagonal collapse" of `RequestProject.Diagonal` is a statement in the theory of
complete lattices.  This file follows the *bridge* methodology: instead of attacking a
statement in the context where it was posed, one sets up an equivalence (or merely a
functorial map) with another context and proves each ingredient where it is cheapest.

| Bridge                    | Map                                    | What it buys                                     |
| ------------------------- | -------------------------------------- | ------------------------------------------------ |
| duality                   | `α ≃o αᵒᵈ`                             | every `⨅` theorem is a `⨆` theorem, for free      |
| sets ↔ families           | `Set.range` / `sSup = ⨆`               | Mathlib's `IsCofinalFor` API applies verbatim      |
| order isomorphism         | `e : α ≃o β`                           | transport of statements (an equivalence of theories)|
| sup-homomorphism          | `e : sSupHom α β`, *not* injective     | a non-faithful functorial map still transports     |
| adjunction                | `GaloisConnection l u`                 | left adjoints preserve `⨆`, so they transport too  |
| linear order              | `csSup_eq_csSup_of_forall_exists_le`   | boundedness hypotheses disappear                   |
| category theory           | `colimit = ⨆`, `Functor.diag` final    | the collapse *is* finality of the diagonal functor |

Tags: 🧩 atomic, 🔁 reducible (iso/dual/rewrite), 🌿 local-glue, 🌌 structural.
-/

namespace Golf.Bridge

open Set

variable {α β : Type*} {ι κ : Sort*}

/-! ## 1. The duality bridge

`αᵒᵈ` is not merely *similar* to `α`: the `⨅`-statement in `αᵒᵈ` and the `⨆`-statement
in `α` are the *same proposition*, which is why `iInf₂_eq_iInf_diagonal` is proved by
`iSup₂_eq_iSup_diagonal` with no work at all. -/

section Duality

variable [CompleteLattice α]

/-- 🧩 The two theories are definitionally the same one. -/
theorem iSup₂_diagonal_iff_dual (F : ι → ι → α) :
    (⨆ i, ⨆ j, F i j = ⨆ k, F k k) ↔
      (⨅ i, ⨅ j, OrderDual.toDual (F i j) = ⨅ k, OrderDual.toDual (F k k)) :=
  Iff.rfl

end Duality

/-! ## 2. The set bridge

`⨆` is `sSup ∘ Set.range`, so the family-level statement is a set-level statement, and
Mathlib's cofinality API (`IsCofinalFor`, `sSup_le_sSup_of_isCofinalFor`) is available. -/

section Sets

variable [CompleteLattice α]

/-- 🌿 Mutually cofinal sets have equal suprema. -/
theorem sSup_eq_sSup_of_isCofinalFor {s t : Set α} (h₁ : IsCofinalFor s t)
    (h₂ : IsCofinalFor t s) : sSup s = sSup t :=
  le_antisymm (sSup_le_sSup_of_isCofinalFor h₁) (sSup_le_sSup_of_isCofinalFor h₂)

/-- 🔁 The same for families: `⨆` *is* `sSup ∘ Set.range`, so this is the previous lemma
with no work at all. -/
theorem iSup_eq_iSup_of_isCofinalFor {f : ι → α} {g : κ → α}
    (h₁ : IsCofinalFor (range f) (range g)) (h₂ : IsCofinalFor (range g) (range f)) :
    ⨆ i, f i = ⨆ j, g j :=
  sSup_eq_sSup_of_isCofinalFor h₁ h₂

/-- 🔁 The engine of `RequestProject.Diagonal`, crossed over to the set side and back. -/
theorem iSup_eq_iSup_of_cofinal' {f : ι → α} {g : κ → α} (h₁ : ∀ i, ∃ j, f i ≤ g j)
    (h₂ : ∀ j, ∃ i, g j ≤ f i) : ⨆ i, f i = ⨆ j, g j :=
  iSup_eq_iSup_of_isCofinalFor (isCofinalFor_range_iff.2 h₁) (isCofinalFor_range_iff.2 h₂)

end Sets

/-! ## 3. Order isomorphisms: transport of a theorem

An `e : α ≃o β` is an equivalence between the two lattice contexts; both the hypothesis
and the conclusion of the diagonal collapse cross it. -/

section OrderIso

variable [CompleteLattice α] [CompleteLattice β] (e : α ≃o β) (F : ι → ι → α)

/-- 🧩 The diagonal hypothesis is invariant under an order isomorphism. -/
theorem orderIso_diagonal_hyp_iff :
    (∀ i j, ∃ k, e (F i j) ≤ e (F k k)) ↔ ∀ i j, ∃ k, F i j ≤ F k k := by
  simp [e.le_iff_le]

/-- 🔁 …hence so is the conclusion. -/
theorem orderIso_iSup₂_diagonal_iff :
    (⨆ i, ⨆ j, e (F i j) = ⨆ k, e (F k k)) ↔ (⨆ i, ⨆ j, F i j = ⨆ k, F k k) := by
  rw [← e.injective.eq_iff (a := ⨆ i, ⨆ j, F i j), e.map_iSup]
  simp only [e.map_iSup]

/-- 🌿 Transporting the theorem itself. -/
theorem orderIso_iSup₂_eq_iSup_diagonal (h : ∀ i j, ∃ k, e (F i j) ≤ e (F k k)) :
    ⨆ i, ⨆ j, e (F i j) = ⨆ k, e (F k k) :=
  (orderIso_iSup₂_diagonal_iff e F).2 <|
    iSup₂_eq_iSup_diagonal F ((orderIso_diagonal_hyp_iff e F).1 h)

end OrderIso

/-! ## 4. A non-faithful functorial map

An `sSupHom` need not be injective — no equivalence of contexts here, only a functor —
and yet the conclusion still crosses, because all that is used is preservation of `⨆`.
(The hypothesis, of course, only crosses in the direction of the map.) -/

section SupHom

variable [CompleteLattice α] [CompleteLattice β] (e : sSupHom α β) (F : ι → ι → α)

/-- 🧩 A sup-homomorphism is monotone, so it pushes the diagonal hypothesis forward. -/
theorem sSupHom_diagonal_hyp (h : ∀ i j, ∃ k, F i j ≤ F k k) :
    ∀ i j, ∃ k, e (F i j) ≤ e (F k k) :=
  fun i j => (h i j).imp fun _ hk => OrderHomClass.mono e hk

/-- 🔁 Pushing the conclusion forward: no injectivity is needed. -/
theorem sSupHom_iSup₂_eq_iSup_diagonal (h : ∀ i j, ∃ k, F i j ≤ F k k) :
    ⨆ i, ⨆ j, e (F i j) = ⨆ k, e (F k k) := by
  simp only [← map_iSup, iSup₂_eq_iSup_diagonal F h]

end SupHom

/-! ## 5. The adjunction bridge

A left adjoint preserves suprema (`GaloisConnection.l_iSup`); dually, the right adjoint
of a Galois connection preserves cofinal sets (`GaloisConnection.map_cofinal`).  So a
Galois connection is exactly the amount of structure needed to move the collapse. -/

section Galois

variable [CompleteLattice α] [CompleteLattice β] {l : α → β} {u : β → α}

/-- 🔁 The collapse crosses any Galois connection, along the left adjoint. -/
theorem galoisConnection_iSup₂_eq_iSup_diagonal (gc : GaloisConnection l u) (F : ι → ι → α)
    (h : ∀ i j, ∃ k, F i j ≤ F k k) :
    ⨆ i, ⨆ j, l (F i j) = ⨆ k, l (F k k) := by
  simp only [← gc.l_iSup, iSup₂_eq_iSup_diagonal F h]

end Galois

/-! ## 6. The linear-order bridge: boundedness for free

In a conditionally complete *linear* order, `csSup_eq_csSup_of_forall_exists_le` proves
the cofinality collapse with no boundedness and no nonemptiness hypothesis whatsoever
(unbounded suprema are junk values, but *the same* junk value on both sides).  So in the
linear world boundedness is needed only for the currying step. -/

section LinearOrder

variable [ConditionallyCompleteLinearOrder α]

/-- 🌌 Cofinality collapse with no side conditions at all. -/
theorem ciSup_eq_ciSup_of_cofinal_of_linear {f : ι → α} {g : κ → α}
    (h₁ : ∀ i, ∃ j, f i ≤ g j) (h₂ : ∀ j, ∃ i, g j ≤ f i) : ⨆ i, f i = ⨆ j, g j :=
  csSup_eq_csSup_of_forall_exists_le
    (forall_mem_range.2 fun i => (h₁ i).elim fun j hj => ⟨g j, mem_range_self j, hj⟩)
    (forall_mem_range.2 fun j => (h₂ j).elim fun i hi => ⟨f i, mem_range_self i, hi⟩)

variable [Nonempty ι]

/-- 🌿 The diagonal collapse in a conditionally complete linear order: boundedness is
consumed by the currying step only. -/
theorem ciSup₂_eq_ciSup_diagonal_of_linear (F : ι → ι → α) (h : ∀ i j, ∃ k, F i j ≤ F k k)
    (hb : BddAbove (range fun k => F k k)) : ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  (ciSup_pprod F (bddAbove_range_uncurry h hb)).trans <|
    ciSup_eq_ciSup_of_cofinal_of_linear (fun p => h p.1 p.2) fun k => ⟨⟨k, k⟩, le_rfl⟩

end LinearOrder

/-! ## 7. The categorical bridge: the collapse *is* finality of the diagonal

A complete lattice is a category with all colimits, and `colimit F = ⨆ j, F.obj j`
(`CategoryTheory.Limits.CompleteLattice.colimit_eq_iSup`).  A family monotone in each
variable is a functor `ι × ι ⥤ α`, and for a directed (= filtered) index the diagonal
`ι ⥤ ι × ι` is a final functor (`CategoryTheory.Functor.final_diag_of_isFiltered`).
Finality of a functor is precisely invariance of colimits, so the diagonal collapse for
monotone families is *literally* that instance — no order-theoretic argument occurs. -/

section Categorical

open CategoryTheory CategoryTheory.Limits

universe u

variable {α : Type u} [CompleteLattice α] {ι : Type u} [Preorder ι]

/-- 🌌 A family monotone in each variable, read as a functor out of the product
category. -/
@[simps]
def biFunctor (F : ι → ι → α) (h : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → F i j ≤ F i' j') :
    ι × ι ⥤ α where
  obj p := F p.1 p.2
  map f := homOfLE (h (leOfHom f.1) (leOfHom f.2))

/-- 🧩 Suprema are colimits. -/
theorem iSup_eq_colimit (F : ι × ι ⥤ α) : ⨆ p : ι × ι, F.obj p = colimit F :=
  (CompleteLattice.colimit_eq_iSup F).symm

variable [IsDirected ι (· ≤ ·)] [Nonempty ι]

/-- 🌌 Finality of the diagonal functor, transcribed. -/
theorem iSup_prod_eq_iSup_diagonal_functor (F : ι × ι ⥤ α) :
    ⨆ p : ι × ι, F.obj p = ⨆ k, F.obj (k, k) := by
  have h := (Functor.Final.colimitIso (Functor.diag ι) F).to_eq
  rw [CompleteLattice.colimit_eq_iSup, CompleteLattice.colimit_eq_iSup] at h
  exact h.symm

/-- 🌿 The diagonal collapse for a bimonotone family over a directed index, proved
entirely on the categorical side of the bridge. -/
theorem iSup₂_eq_iSup_diagonal_of_bimonotone (F : ι → ι → α)
    (h : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → F i j ≤ F i' j') :
    ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  (iSup_prod' F).trans (iSup_prod_eq_iSup_diagonal_functor (biFunctor F h))

omit [Nonempty ι] in
/-- 🌿 The same statement, proved on the order-theoretic side: directedness *is* the
diagonal hypothesis.  Both routes are one line; the bridge shows they are the same
mathematics. -/
theorem iSup₂_eq_iSup_diagonal_of_bimonotone' (F : ι → ι → α)
    (h : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → F i j ≤ F i' j') :
    ⨆ i, ⨆ j, F i j = ⨆ k, F k k :=
  iSup₂_eq_iSup_diagonal F fun i j =>
    (exists_ge_ge i j).imp fun _ hk => h hk.1 hk.2

end Categorical

end Golf.Bridge
