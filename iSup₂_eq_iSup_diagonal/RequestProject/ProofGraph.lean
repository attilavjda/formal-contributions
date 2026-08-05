import RequestProject.Bridges

/-!
# The proof space, drawn as a graph

The spine of `RequestProject.Diagonal`, `RequestProject.Applications` and
`RequestProject.Bridges` — the twenty-five lemmas on the path from Mathlib atoms to the
two headline theorems — is a DAG.  This file *reifies* that DAG: the nodes are the
lemmas, the arrows are "uses", and the structural claims one would
normally make in prose ("every atom is a leaf", "no lemma composes more than three
others", "both headlines are connected to the same core") become theorems closed by
`decide`.

Each node carries one of the four tags

| Tag           | Meaning                              |
| ------------- | ------------------------------------ |
| 🧩 `atomic`    | Mathlib, or one tactic               |
| 🔁 `reducible` | an iso/dual/rewrite collapses it     |
| 🌿 `glue`      | small composition                    |
| 🌌 `structural`| introduces a new invariant           |

and the *rank* is the height in the DAG.  `Golf.Graph.dep_rank_lt` checks that the
"uses" relation strictly decreases the rank, i.e. that the development really is a DAG.
-/

namespace Golf.Graph

/-- The lemmas of the development, one constructor each. -/
inductive Node
  /-- `le_antisymm` (Mathlib). -/
  | leAntisymm
  /-- `iSup_mono'` (Mathlib). -/
  | iSupMono
  /-- `csSup_eq_csSup_of_forall_exists_le` (Mathlib). -/
  | csSupCofinal
  /-- `CategoryTheory.Limits.CompleteLattice.colimit_eq_iSup` (Mathlib). -/
  | colimitEqISup
  /-- `CategoryTheory.Functor.final_diag_of_isFiltered` (Mathlib). -/
  | finalDiag
  /-- `Golf.isCofinalFor_range_iff`. -/
  | cofinalRange
  /-- `Golf.IsCofinalFor.bddAbove`. -/
  | cofinalBddAbove
  /-- `Golf.bddAbove_range_row`. -/
  | bddRow
  /-- `Golf.bddAbove_range_ciSup`. -/
  | bddRowSups
  /-- `Golf.bddAbove_range_add`. -/
  | bddAdd
  /-- `Golf.iSup_pprod` (currying). -/
  | iSupPProd
  /-- `Golf.iSup_eq_iSup_of_cofinal` (cofinality). -/
  | iSupCofinal
  /-- `Golf.ciSup_pprod` (currying, bounded). -/
  | ciSupPProd
  /-- `Golf.ciSup_eq_ciSup_of_cofinal`. -/
  | ciSupCofinal
  /-- `Golf.Bridge.ciSup_eq_ciSup_of_cofinal_of_linear`. -/
  | ciSupCofinalLinear
  /-- `Golf.Bridge.iSup_prod_eq_iSup_diagonal_functor`. -/
  | finalityCollapse
  /-- `Golf.iSup₂_eq_iSup_of_cofinal`. -/
  | iSup2Cofinal
  /-- `Golf.iSup₂_eq_iSup_diagonal`. -/
  | iSup2Diag
  /-- `Golf.iInf₂_eq_iInf_diagonal` (dual). -/
  | iInf2Diag
  /-- `Golf.iSup_op_iSup_diagonal`. -/
  | iSupOpDiag
  /-- `Golf.bddAbove_range_uncurry`. -/
  | bddUncurry
  /-- `Golf.ciSup₂_eq_ciSup_diagonal`. -/
  | ciSup2Diag
  /-- `Golf.Bridge.iSup₂_eq_iSup_diagonal_of_bimonotone`. -/
  | bimonotoneDiag
  /-- `Golf.ennreal_iSup_add_iSup` (headline). -/
  | ennrealAdd
  /-- `Golf.cardinal_ciSup_add_ciSup_diagonal` (headline). -/
  | cardinalAdd
  deriving DecidableEq, Fintype, Repr

/-- The four DAG tags. -/
inductive Tag
  /-- 🧩 Mathlib, or one tactic. -/
  | atomic
  /-- 🔁 an iso/dual/rewrite collapses it. -/
  | reducible
  /-- 🌿 a small composition. -/
  | glue
  /-- 🌌 introduces a new invariant. -/
  | structural
  deriving DecidableEq, Fintype, Repr

open Node Tag

/-- What each lemma is built from. -/
def deps : Node → List Node
  | leAntisymm | iSupMono | csSupCofinal | colimitEqISup | finalDiag => []
  | cofinalRange | cofinalBddAbove | bddRow | bddRowSups | bddAdd => []
  | iSupPProd => [leAntisymm]
  | iSupCofinal => [leAntisymm, iSupMono]
  | ciSupPProd => [leAntisymm, bddRow, bddRowSups]
  | ciSupCofinal => [leAntisymm]
  | ciSupCofinalLinear => [csSupCofinal]
  | finalityCollapse => [colimitEqISup, finalDiag]
  | iSup2Cofinal => [iSupPProd, iSupCofinal]
  | iSup2Diag => [iSup2Cofinal]
  | iInf2Diag => [iSup2Diag]
  | iSupOpDiag => [iSup2Diag]
  | bddUncurry => [cofinalRange, cofinalBddAbove]
  | ciSup2Diag => [ciSupPProd, ciSupCofinal, bddUncurry]
  | bimonotoneDiag => [finalityCollapse]
  | ennrealAdd => [iSupOpDiag]
  | cardinalAdd => [ciSup2Diag, bddAdd]

/-- The tag of each node. -/
def tag : Node → Tag
  | leAntisymm | iSupMono | csSupCofinal | colimitEqISup | finalDiag => atomic
  | cofinalRange | cofinalBddAbove | bddRow | bddRowSups | bddAdd => atomic
  | iSupPProd | iSupCofinal | ciSupPProd | ciSupCofinalLinear | finalityCollapse => structural
  | iSup2Cofinal | ciSupCofinal | ciSup2Diag | iSupOpDiag | bimonotoneDiag => glue
  | iSup2Diag | iInf2Diag | bddUncurry => reducible
  | ennrealAdd | cardinalAdd => glue

/-- The height of a node in the DAG. -/
def rank : Node → ℕ
  | leAntisymm | iSupMono | csSupCofinal | colimitEqISup | finalDiag => 0
  | cofinalRange | cofinalBddAbove | bddRow | bddRowSups | bddAdd => 0
  | iSupPProd | iSupCofinal | ciSupPProd | ciSupCofinal | ciSupCofinalLinear
  | finalityCollapse | bddUncurry => 1
  | iSup2Cofinal | ciSup2Diag | bimonotoneDiag => 2
  | iSup2Diag => 3
  | iInf2Diag | iSupOpDiag => 4
  | ennrealAdd | cardinalAdd => 5

/-- `a` uses `b`. -/
def Uses (a b : Node) : Prop := b ∈ deps a

instance : DecidableRel Uses := fun a b => inferInstanceAs (Decidable (b ∈ deps a))

/-- The proof space as an undirected graph: nodes are lemmas, edges are uses. -/
def G : SimpleGraph Node := SimpleGraph.fromRel Uses

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Bridge links: pairs of nodes that prove *the same statement in different contexts*
(`RequestProject.Bridges`).  These are not uses; they are equivalences of theories. -/
def Bridges (a b : Node) : Prop :=
  (a, b) ∈ [(bimonotoneDiag, iSup2Diag), (ciSupCofinalLinear, ciSupCofinal)]

instance : DecidableRel Bridges := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

/-- The proof space *with* its bridges. -/
def G' : SimpleGraph Node := SimpleGraph.fromRel fun a b => Uses a b ∨ Bridges a b

instance : DecidableRel G'.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-! ### Structural invariants of the development, checked by `decide` -/

/-- 🧩 The development is a DAG: every use strictly decreases the rank. -/
theorem dep_rank_lt : ∀ a b, Uses a b → rank b < rank a := by decide

/-- 🧩 A lemma never uses itself. -/
theorem uses_irrefl : ∀ a, ¬ Uses a a := by decide

/-- 🧩 The atoms are exactly the leaves: a node is tagged 🧩 iff it has no dependencies. -/
theorem atomic_iff_leaf : ∀ a, tag a = atomic ↔ deps a = [] := by decide

/-- 🧩 "Small is beautiful": no lemma composes more than three others. -/
theorem deps_length_le_three : ∀ a, (deps a).length ≤ 3 := by decide

/-- 🧩 Nothing is duplicated: no lemma lists the same dependency twice. -/
theorem deps_nodup : ∀ a, (deps a).Nodup := by decide

/-- 🧩 Ten of the twenty-five nodes are atoms — the development is mostly Mathlib. -/
theorem card_atomic : (Finset.univ.filter fun a => tag a = atomic).card = 10 := by decide

/-- 🧩 Only five nodes introduce a genuinely new invariant. -/
theorem card_structural : (Finset.univ.filter fun a => tag a = structural).card = 5 := by decide

/-- 🧩 Everything that is not an atom sits strictly above rank `0`. -/
theorem rank_pos_of_not_atomic : ∀ a, tag a ≠ atomic → 0 < rank a := by decide

/-- 🧩 The two headline theorems sit at the top of the DAG. -/
theorem rank_headlines : rank ennrealAdd = 5 ∧ rank cardinalAdd = 5 := by decide

/-- 🌿 Each headline hangs on a single collapse lemma (plus, for cardinals, one
boundedness helper). -/
theorem headline_degrees : G.degree ennrealAdd = 1 ∧ G.degree cardinalAdd = 2 := by decide

/-- 🌿 `le_antisymm` is the most reused node of the development. -/
theorem leAntisymm_degree : G.degree leAntisymm = 4 := by decide

/-- 🌿 The graph is sparse: twenty-five nodes, twenty-four use-edges — as sparse as a
spanning forest can be. -/
theorem card_edges : G.edgeFinset.card = 24 := by decide

/-! ### What the picture shows

The use-graph is *disconnected*: the categorical route (`finalityCollapse`,
`bimonotoneDiag`) and the linear-order route (`ciSupCofinalLinear`) reach the same
statements through entirely disjoint material.  Adding the two bridge links — the
formal statements that these are the same theorems in other contexts — connects the
whole proof space.  That is the bridge philosophy, visible in the geometry.

Rather than deciding reachability (exponential for the kernel), each claim is reduced
to a *local* invariant that `decide` checks edge by edge: a three-valued colouring for
the negative results, and a decreasing distance-to-root for the positive one. -/

/-- The connected component of each node in the use-graph, as a colouring. -/
def colour : Node → Fin 3
  | csSupCofinal | ciSupCofinalLinear => 1
  | colimitEqISup | finalDiag | finalityCollapse | bimonotoneDiag => 2
  | _ => 0

/-- 🧩 The colouring is a local invariant of the use-graph. -/
theorem colour_eq_of_adj : ∀ a b, G.Adj a b → colour a = colour b := by decide

/-- 🌌 …hence an invariant of reachability: walks cannot change colour. -/
theorem colour_eq_of_reachable {a b : Node} (h : G.Reachable a b) : colour a = colour b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (colour_eq_of_adj _ _ hadj).trans ih

/-- 🌿 The categorical route shares no material at all with the theorem it re-proves. -/
theorem not_reachable_categorical : ¬ G.Reachable bimonotoneDiag iSup2Diag := fun h =>
  absurd (colour_eq_of_reachable h) (by decide)

/-- 🌿 Without the bridges the proof space falls apart. -/
theorem not_connected : ¬ G.Connected := fun h =>
  not_reachable_categorical (h.preconnected _ _)

/-- One step towards the root `leAntisymm` in the bridged graph. -/
def toRoot : Node → Node
  | leAntisymm => leAntisymm
  | iSupPProd | iSupCofinal | ciSupPProd | ciSupCofinal => leAntisymm
  | iSupMono | iSup2Cofinal => iSupCofinal
  | bddRow | bddRowSups => ciSupPProd
  | ciSupCofinalLinear | ciSup2Diag => ciSupCofinal
  | csSupCofinal => ciSupCofinalLinear
  | cofinalRange | cofinalBddAbove => bddUncurry
  | bddUncurry | cardinalAdd => ciSup2Diag
  | bddAdd => cardinalAdd
  | iSup2Diag => iSup2Cofinal
  | iInf2Diag | iSupOpDiag | bimonotoneDiag => iSup2Diag
  | finalityCollapse => bimonotoneDiag
  | colimitEqISup | finalDiag => finalityCollapse
  | ennrealAdd => iSupOpDiag

/-- The distance to the root in the bridged graph. -/
def depth : Node → ℕ
  | leAntisymm => 0
  | iSupPProd | iSupCofinal | ciSupPProd | ciSupCofinal => 1
  | iSupMono | bddRow | bddRowSups | ciSupCofinalLinear | iSup2Cofinal | ciSup2Diag => 2
  | csSupCofinal | iSup2Diag | bddUncurry | cardinalAdd => 3
  | cofinalRange | cofinalBddAbove | bddAdd | iInf2Diag | iSupOpDiag | bimonotoneDiag => 4
  | finalityCollapse | ennrealAdd => 5
  | colimitEqISup | finalDiag => 6

/-- 🧩 Every node other than the root has a bridged neighbour… -/
theorem adj_toRoot : ∀ a, a ≠ leAntisymm → G'.Adj a (toRoot a) := by decide

/-- 🧩 …strictly closer to the root. -/
theorem depth_toRoot_lt : ∀ a, a ≠ leAntisymm → depth (toRoot a) < depth a := by decide

/-- 🌌 Descending along `toRoot`, every node reaches the root. -/
theorem reachable_root (a : Node) : G'.Reachable a leAntisymm := by
  induction hd : depth a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    rcases eq_or_ne a leAntisymm with rfl | ha
    · rfl
    · exact ((adj_toRoot a ha).reachable).trans (ih _ (hd ▸ depth_toRoot_lt a ha) _ rfl)

/-- 🌿 With the bridges added, the proof space is connected. -/
theorem bridged_connected : G'.Connected :=
  haveI : Nonempty Node := ⟨leAntisymm⟩
  ⟨fun a b => (reachable_root a).trans (reachable_root b).symm⟩

/-- 🌿 The bridges cost exactly two edges. -/
theorem card_bridged_edges : G'.edgeFinset.card = 26 := by decide

end Golf.Graph
