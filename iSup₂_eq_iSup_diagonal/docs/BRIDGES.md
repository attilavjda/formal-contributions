# Map of the development

Four Lean files, one mathematical statement seen from many sides.

## The statement

`⨆ i, ⨆ j, F i j = ⨆ k, F k k` whenever every entry `F i j` is dominated by a diagonal
entry `F k k` — the abstraction behind `ENNReal.iSup_add_iSup`, `ENat.iSup_add_iSup`
and `Cardinal.ciSup_add_ciSup`.

## The files

| File | Role |
| --- | --- |
| `RequestProject/Diagonal.lean` | the core, cut into one-step lemmas: currying + cofinality (+ boundedness in the conditionally complete case) |
| `RequestProject/Applications.lean` | `ℝ≥0∞`, `ℕ∞`, `Cardinal`, and one topological corollary |
| `RequestProject/Bridges.lean` | the same theorem transported to six other contexts |
| `RequestProject/ProofGraph.lean` | the dependency DAG itself, as a `SimpleGraph`, with `decide`-checked invariants |
| `RequestProject/Variations.lean` | ~40 alternative proofs, moved along the style/automation/direction/granularity axes |

## The two structural ideas

* **Currying** (`Golf.iSup_pprod`, `Golf.ciSup_pprod`): a doubly indexed supremum is a
  supremum over the product index.  In the conditionally complete setting this is the
  *only* step that uses boundedness.
* **Cofinality** (`Golf.iSup_eq_iSup_of_cofinal`, `Golf.ciSup_eq_ciSup_of_cofinal`):
  mutually cofinal families have equal suprema.  Mathlib already names this relation:
  `IsCofinalFor`.

Everything else in the core is glue or duality (`αᵒᵈ`).

## The bridges

| Bridge | Map | What it buys |
| --- | --- | --- |
| duality | `α ≃o αᵒᵈ` | every `⨅` theorem is a `⨆` theorem verbatim |
| sets ↔ families | `Set.range`, `sSup = ⨆` | Mathlib's `IsCofinalFor` API applies directly |
| order isomorphism | `e : α ≃o β` | hypothesis *and* conclusion transport (an equivalence of theories) |
| sup-homomorphism | `e : sSupHom α β`, not injective | a non-faithful functorial map still transports the conclusion |
| adjunction | `GaloisConnection l u` | left adjoints preserve `⨆`, so they transport too |
| linear order | `csSup_eq_csSup_of_forall_exists_le` | the cofinality step needs no boundedness at all |
| category theory | `colimit = ⨆`, `Functor.diag` final | for monotone families over a directed index the collapse *is* finality of the diagonal functor |

## What the proof graph shows

`RequestProject/ProofGraph.lean` reifies the spine of the development as a graph on 25
nodes (tagged 🧩 atomic / 🔁 reducible / 🌿 glue / 🌌 structural) and proves, by `decide`
on local invariants:

* the "uses" relation strictly decreases rank — the development is a DAG;
* the atoms are exactly the leaves, and no lemma composes more than three others;
* the use-graph is **disconnected**: the categorical and linear-order routes reach the
  same theorems through disjoint material;
* adding the two bridge links (two edges) makes it connected.

## Pictures

`visuals/proof-visualisations.pdf` (source in `visuals/`) draws all of the above: the
square and its cofinal diagonal, the currying/cofinality factorisation, the boundedness
transport, concrete lattices and a counterexample, the dependency DAG with its
three-colouring and spanning tree, the bridges as commutative diagrams, and the
catalogue of alternative proofs as a Boolean lattice of design choices.
