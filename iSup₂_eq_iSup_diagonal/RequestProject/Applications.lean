import RequestProject.Bridges

/-!
# Applications of the diagonal-collapse abstraction

Everything here is a two-or-three-line consequence of the lemmas in
`RequestProject.Diagonal`:

* in `ℝ≥0∞` and `ℕ∞` (complete lattices) each proof is one application of
  `Golf.iSup_op_iSup_diagonal`, fed with the two distributivity lemmas;
* in `Cardinal` (a conditionally complete lattice) the proof is a rewrite plus
  `Golf.ciSup₂_eq_ciSup_diagonal`, with the boundedness side condition packaged once
  and for all by `Golf.bddAbove_range_add`;
* over a *directed* index the diagonal hypothesis is automatic, and can be obtained
  either from directedness or — crossing the categorical bridge of
  `RequestProject.Bridges` — from finality of the diagonal functor.

Tags: 🧩 atomic, 🔁 reducible, 🌿 local-glue, 🌌 structural.
-/

namespace Golf

open Set
open scoped ENNReal

/-! ### A generic boundedness helper -/

/-- 🧩 Boundedness is the only extra ingredient in the conditionally complete setting, and
it is completely generic: a sum of two bounded families is bounded. -/
theorem bddAbove_range_add {ι β : Type*} [Preorder β] [Add β]
    [CovariantClass β β (· + ·) (· ≤ ·)] [CovariantClass β β (Function.swap (· + ·)) (· ≤ ·)]
    {f g : ι → β} (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    BddAbove (range fun k => f k + g k) :=
  (hf.add hg).mono <| range_subset_iff.2 fun k =>
    Set.add_mem_add (mem_range_self k) (mem_range_self k)

/-! ### `ℝ≥0∞` -/

section ENNReal

variable {ι : Type*} {f g : ι → ℝ≥0∞}

section Nonempty

variable [Nonempty ι]

/-- 🔁 `ENNReal.iSup_add_iSup`, re-derived from `Golf.iSup_op_iSup_diagonal`. -/
theorem ennreal_iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  iSup_op_iSup_diagonal (· + ·) (fun f _ => ENNReal.iSup_add f) (fun _ g => ENNReal.add_iSup g) h

end Nonempty

/-- 🔁 `ENNReal.iInf_add_iInf`, re-derived from `Golf.iInf_op_iInf_diagonal`. -/
theorem ennreal_iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) :
    (⨅ i, f i) + (⨅ j, g j) = ⨅ k, f k + g k :=
  iInf_op_iInf_diagonal (· + ·) (fun _ _ => ENNReal.iInf_add) (fun _ _ => ENNReal.add_iInf) h

/-- 🔁 The multiplicative analogue: no new proof, only new distributivity inputs. -/
theorem ennreal_iSup_mul_iSup (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ k, f k * g k :=
  iSup_op_iSup_diagonal (· * ·) ENNReal.iSup_mul ENNReal.mul_iSup h

/-- 🌿 Over a directed index, monotone families need no diagonal hypothesis at all: the
diagonal is cofinal in the square.  Proved on the categorical side of the bridge, where
this is finality of `CategoryTheory.Functor.diag`. -/
theorem ennreal_iSup_add_iSup_of_monotone {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {f g : ι → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k := by
  rw [ENNReal.iSup_add]
  simp_rw [ENNReal.add_iSup]
  exact Bridge.iSup₂_eq_iSup_diagonal_of_bimonotone _ fun _ _ _ _ hi hj => add_le_add (hf hi) (hg hj)

/-- 🌿 The same fact seen in the topological context: along a monotone sequence the
partial "diagonal" sums converge to the sum of the two suprema.  Crossing to analysis
costs one Mathlib lemma, `tendsto_atTop_iSup`. -/
theorem ennreal_tendsto_add_atTop {f g : ℕ → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    Filter.Tendsto (fun k => f k + g k) Filter.atTop (nhds ((⨆ i, f i) + (⨆ j, g j))) := by
  rw [ennreal_iSup_add_iSup_of_monotone hf hg]
  exact tendsto_atTop_iSup (hf.add hg)

end ENNReal

/-! ### `ℕ∞` -/

section ENat

variable {ι : Type*} [Nonempty ι] {f g : ι → ℕ∞}

/-- 🔁 `ENat.iSup_add_iSup`, re-derived from `Golf.iSup_op_iSup_diagonal`. -/
theorem enat_iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  iSup_op_iSup_diagonal (· + ·) (fun f _ => ENat.iSup_add f) (fun _ g => ENat.add_iSup g) h

end ENat

/-! ### `Cardinal` -/

section Cardinal

universe u v

variable {ι : Type u} [Nonempty ι] {f g : ι → Cardinal.{v}}

/-- 🌿 The diagonal form of `Cardinal.ciSup_add_ciSup`. -/
theorem cardinal_ciSup_add_ciSup_diagonal (hf : BddAbove (range f)) (hg : BddAbove (range g))
    (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  ciSup_op_ciSup_diagonal (· + ·) (Cardinal.ciSup_add_ciSup f hf g hg) h
    (bddAbove_range_add hf hg)

/-- 🌿 Monotone families indexed by a directed order automatically satisfy the diagonal
hypothesis. -/
theorem cardinal_ciSup_add_ciSup_of_monotone {ι : Type u} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {f g : ι → Cardinal.{v}} (hf : BddAbove (range f))
    (hg : BddAbove (range g)) (hmf : Monotone f) (hmg : Monotone g) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ k, f k + g k :=
  cardinal_ciSup_add_ciSup_diagonal hf hg fun i j =>
    (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ => add_le_add (hmf hi) (hmg hj)

end Cardinal

end Golf
