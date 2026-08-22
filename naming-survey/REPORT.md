# What is actually in a Mathlib lemma name? A measurement

Question asked: *is there a convention that the parts of a lemma's name must be exactly the
names of definitions occurring in its statement?* And: *what are the counterexamples — `self`,
`₂`, `of`, and what else?*

Short answer, measured rather than guessed: **no such rule holds.** Only ~70 % of the
underscore-separated tokens in Mathlib lemma names are the name of a definition occurring in
that lemma's statement, and only **44 %** of lemma names have *all* of their tokens grounded
that way. The remaining tokens fall into a small number of recurring, well-understood families:
connectives (`of`, `iff`, `eq`), shape words (`self`, `same`, `left`, `right`, `comm`, `assoc`),
arity and variant markers (`₂`, `₀`, `'`), contractions (`natCard`, `ciSup`, `setIntegral`,
`notMem`), descriptions of anonymous terms (`diag`, `two`, `half`), and eponyms
(`ruzsa`, `lhopital`, `young`).

Everything below is produced by `naming-survey/Survey.lean` (raw output:
`naming-survey/output.txt`), and every declaration quoted is `#check`ed in
`RequestProject/NamingConventionEvidence.lean`, which compiles against the pinned Mathlib.

---

## 1. Method

* **Vocabulary of definitions.** Take the last name-component of every non-theorem, non-axiom
  constant in the environment (definitions, structures, classes, inductives, projections):
  53 754 distinct lowercased strings.
* **Lemmas.** All 217 726 mathlib theorems, after removing auto-generated declarations
  (instances, `congr`/`match`/equation lemmas) and the tactic/util directories.
* **Tokens.** Split the last component of the lemma name at `_`: 639 560 tokens.
* **Statement vocabulary.** For each lemma, the last name-component of every constant occurring
  in its *type*.
* **Classification of each token** (case-insensitive; also tried after dropping trailing
  `₀…₉ ' ! ?`, and after prefixing `is`):
  * **GROUNDED** — names a definition that occurs in the statement;
  * **ELSEWHERE** — names some definition of Mathlib/core, but not one used here;
  * **FREE** — no definition of that name exists anywhere.

Caveats: matching is on the *last* component only, so `Nat.card` grounds a token `card` but not
`natCard`; and homonyms inflate ELSEWHERE (a token `left` "matches" the unrelated `Tree.left`).
Both effects are discussed where they matter.

## 2. Headline numbers

| | tokens | share |
|---|---:|---:|
| GROUNDED (definition present in the statement) | 451 868 | 70 % |
| — exact match | 445 162 | |
| — only after dropping a subscript/prime (`iSup₂ ↦ iSup`) | 5 046 | |
| — only after adding `Is` (`open ↦ IsOpen`) | 1 660 | |
| ELSEWHERE | 172 316 | 26 % |
| FREE | 15 376 | 2 % |

Name-level: **44 %** of lemma names have every token grounded; 6 % contain at least one token
that is not a definition name anywhere in the library.

So the "only definition names" idea describes a *tendency*, and less than half of the library
follows it strictly.

## 3. Per-area variation (top-level directories, ≥ 300 tokens)

| area | grounded | elsewhere | free |
|---|---:|---:|---:|
| CategoryTheory | 79 % | 18 % | 1 % |
| Algebra/Homology | 80 % | 18 % | 1 % |
| Combinatorics | 76 % | 20 % | 3 % |
| Data/Finset | 78 % | 20 % | 1 % |
| Data/Set | 77 % | 20 % | 1 % |
| Order | 74 % | 23 % | 2 % |
| Topology | 73 % | 23 % | 2 % |
| LinearAlgebra | 72 % | 25 % | 1 % |
| RingTheory | 70 % | 27 % | 1 % |
| MeasureTheory | 67 % | 29 % | 3 % |
| Analysis | 63 % | 32 % | 3 % |
| NumberTheory | 60 % | 34 % | 4 % |
| Algebra/Order | 55 % | 42 % | 2 % |
| Algebra/Divisibility | 43 % | 56 % | 0 % |

The gradient is informative: areas built on *named structures* (categories, homological
algebra, finsets) name lemmas almost entirely out of definitions; areas built on *notation and
shape* (ordered algebra, divisibility, analysis) rely much more on words that are not
definitions — `nonneg`, `nonpos`, `self`, `left`, `right`, `two`, `half`.

## 4. The families of tokens that are *not* definitions in the statement

### 4.1 Connectives and hypothesis markers

| token | occurrences | examples (various areas) |
|---|---:|---|
| `of` | 28 494 | `lt_of_le_of_lt`, `CategoryTheory.mono_of_mono_fac`, `Set.mem_image_of_mem`, `Nat.dvd_of_mem_divisors`, `MeasurableSet.of_compl` |
| `iff`, `eq`, `ne`, `le`, `lt` | — | ubiquitous; `iff` and `eq` do exist as definitions but are used here as connectives |

`of` is the largest single non-grounded token in the library. It happens to collide with
definitions such as `TopCat.of`, which is why it lands in ELSEWHERE rather than FREE; nobody
reads `lt_of_le_of_lt` as mentioning `TopCat.of`.

### 4.2 Shape words: `self`, `same`, `left`, `right`, `comm`, `assoc`, `cancel`

`self` occurs 2 767 times, and in the per-area breakdown of the survey not one bucket is
grounded: there is no definition called `self` in those statements. It means "the same term
appears twice":

* Algebra: `sub_self`, `mul_self_nonneg`, `add_mul_self_eq`
* Order: `min_self`, `max_self`, `le_update_self_iff`
* Topology: `closure_eq_self_union_frontier`, `self_diff_frontier`
* Category theory: `CategoryTheory.Iso.self_symm_id`
* Group theory: `MulAction.mem_orbit_self`, `QuotientGroup.map_mk'_self`
* Measure theory: `MeasurableEquiv.symm_comp_self`
* Number theory: `Nat.mem_divisors_self`

`same` (181 occurrences, also never grounded in the survey) is the sibling used when two *indices* or
*arguments* coincide rather than two terms: `Pi.single_eq_same`, `Matrix.diag_single_same`,
`Finsupp.erase_same`, `gcd_same`, `lcm_same`, `List.forall₂_same`, `Set.Ioo_eq_Icc_same_iff`,
`segment_same`, `Polynomial.coeff_monomial_same`, `DirectSum.of_eq_same`.

`left`/`right` (5 191 / 5 177), `comm` (958), `assoc` (3 985), `cancel` (653) similarly describe
the syntactic shape: `inv_mul_cancel_left`, `mul_mul_mul_comm`, `add_neg_cancel_comm_assoc`.

### 4.3 Arity and variant markers — including `₂`

Subscripts are *not* definitions. The clearest case, and the one relevant to `iSup₂`:

| token | occurrences | is there a definition of that name? | examples |
|---|---:|---|---|
| `iSup₂` | 42 | **no** | `iSup₂_le`, `le_iSup₂`, `iSup₂_mono`, `OrderIso.map_iSup₂` |
| `iInf₂` | 40 | **no** | `iInf₂_comm`, `iInf₂_eq_top` |
| `iUnion₂` | 71 | **no** | `Set.mem_iUnion₂`, `Set.iUnion₂_subset_iff` |
| `iInter₂` | 57 | **no** | `Set.compl_iInter₂`, `Set.iInter₂_eq_empty_iff` |
| `map₂`, `image2`, `eval₂` | 325 / 96 / 191 | yes | `Quotient.map₂`, `Polynomial.eval₂` |

So `⨆ i, ⨆ j, f i j` is named `iSup₂` even though no constant `iSup₂` exists: the token is
`iSup` plus a **shape marker** saying "doubly indexed". This is precedent for naming a *pattern*
rather than a *definition*.

Related variant markers, all describing the lemma rather than naming a constant in it:

* `₀` = the `GroupWithZero` variant: `inv_lt_inv₀`, `div_le_div₀`, `Commute.inv_right_iff₀` (72 `inv₀`, 93 `iff₀`).
* `'` = "primed variant of the neighbouring lemma": 544 `mk'`, 395 `iff'`, 223 `eq'`, e.g. `dite_eq_iff'`, `Quotient.out_eq'`, `Nat.one_le_pow'`.
* `aux`, `aux₁`, `aux₂` for auxiliary steps: `Equiv.Perm.isCycle_swap_mul_aux₁`, `CategoryTheory.braiding_leftUnitor_aux₂`, `ProbabilityTheory.strong_law_aux1`.

### 4.4 Contractions of `Namespace.name` or of a phrase

A large share of "FREE" tokens are compressions, not violations:

| token | means | examples |
|---|---|---|
| `natCard` (44) | `Nat.card` | `Set.natCard_pos`, `pow_mod_natCard`, `Module.natCard_eq_pow_finrank` |
| `cardinalMk` (115) | `Cardinal.mk` | `Set.toENat_cardinalMk`, `Matroid.IsBasis.cardinalMk_eq_cRk` |
| `setIntegral` (205), `setLIntegral` (127) | `∫ x in s, …` | `MeasureTheory.setIntegral_const`, `ProbabilityTheory.Kernel.setLIntegral_deterministic` |
| `measureReal` (108) | `Measure.real` | `MeasureTheory.measureReal_def` |
| `notMem` (719) | `¬ x ∈ s` | `Set.notMem_empty`, `Finset.notMem_mono`, `Cardinal.exists_notMem_of_length_lt` |
| `ciSup`, `csSup`, `ciInf`, `csInf` (423) | `iSup` in a conditionally complete lattice | `ciSup_le_iff`, `ConditionallyCompleteLattice.le_csSup` |
| `biSup`, `biInf`, `biInter` (314) | the `⨆ i ∈ s` shape | `Set.mem_biInter`, `biInf_prod'`, `Subgroup.mem_biSup_of_directedOn` |
| `mclosure` (21) | `Submonoid.closure` | `MonoidHom.map_mclosure` |
| `opNNNorm` (47), `SpecMap` (54) | `‖·‖₊` of an operator; `Spec.map` | `ContinuousLinearMap.opNNNorm_le_bound`, `AlgebraicGeometry.SpecMap_preimage_basicOpen` |

Note that `ciSup`/`biSup` are exactly the same device as `iSup₂`: a definition name decorated
with a one-letter or one-symbol marker describing the *context or shape*.

### 4.5 Words for terms that appear anonymously in the statement

This is the family the user's `diag` belongs to. The statement contains no constant of that
name; the token describes a term written out inline.

* `Filter.tendsto_diag : Tendsto (fun i => (i, i)) f (f ×ˢ f)` — `diag` names `fun i => (i,i)`.
* `Set.range_diag : (range fun x => (x, x)) = Set.diagonal α`
* `Set.diag_image : (fun x => (x, x)) '' s = Set.diagonal α ∩ s ×ˢ s`
* `Matrix.IsAdjMatrix.apply_diag : A i i = 0` — `diag` names the entries `A i i`.
* `Finset.prod_range_diag_flip` — `diag` describes the triangular shape of a double product.
* `Filter.Eventually.diag_of_prod_left`, `Set.toFinset_off_diag`, `Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag`.

Number words are the same phenomenon: `two` (1 578!), `three` (247), `four` (171), `five`,
`half` (115) name numerals or expressions, not definitions —
`Nat.cast_four`, `Fin.sum_univ_five`, `half_le_self : 0 ≤ a → a / 2 ≤ a`, `two_add_two_eq_four`,
`InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`, `Cardinal.lift_two_power`.

Other area-specific "picture" words, all FREE:
`pointwise` (176, Algebra/RingTheory), `fiberwise` (32, Finset), `tower` (86, Ring/FieldTheory),
`anti` (95), `dominated` (38, `tendsto_lintegral_of_dominated_convergence`), `stopping` (17),
`chart` (34, Geometry), `vectorField` (50), `unitality`/`unitor`/`hexagon`/`distinguished`
(CategoryTheory), `preserves`/`reflects` (137/71, CategoryTheory), `jointly` (26),
`intermediate` (25, `intermediate_value_Ico`), `simply` (`simply_connected_iff_…`),
`squared` (`d_squared`), `strong` (`Nat.strong_induction_on`), `bisim` (`Stream'.eq_of_bisim`).

### 4.6 Eponyms

Free tokens naming people or classical theorems, across many files:
`ruzsa` (36) and `pluennecke` (10) in additive combinatorics, `hahn`/`banach` (22)
in functional analysis, `young_inequality` (50), `lhopital` (26), `leibniz` (24),
`lebesgue` (21, `lebesgue_number_lemma_nhds`), `ax_grothendieck` (FieldTheory),
`gold`/`goldConj` (NumberTheory), `euler_product`, `behrend`.

### 4.7 `Is`-dropping: predicates named without their `Is`

1 660 tokens only ground after adding an `Is` prefix — i.e. the statement uses `IsOpen` and the
name says `open`:

* `open` (130): `Dense.exists_mem_open`, `isOpen_iff_forall_mem_open`
* `closed` (93): `isCompact_of_finite_subfamily_closed`
* `iso` (120): `CategoryTheory.isIso_of_reflects_iso`
* `compact` (66), `maximal` (54), `prime` (38), `coprime` (19), `nilpotent` (29),
  `solvable` (25), `noetherian` (11), `clopen` (12), `bounded` (22)

The modern style keeps the `is`: `IsCompact.of_isClosed_subset`, `sSup_le_sSup_of_isCofinalFor`,
`IsCofinal.of_not_bddAbove`, `not_bddAbove_iff_isCofinal`. Both spellings are present; the
`is`-ful one is what new code is expected to use.

## 5. What this means for a `_diag` / `_of_cofinal` suffix on an `iSup₂` lemma

The data support the following reading, which is stronger than "it looks fine":

1. **A name token need not be a definition, and need not occur in the statement.** 30 % of all
   tokens are not, and 56 % of names contain at least one such token. The relevant question is
   whether the token is *predictable and searchable*, not whether it is a constant.
2. **`iSup₂` itself is such a token** — it names the shape `⨆ i, ⨆ j`, not a constant. A lemma
   named with `iSup₂` is already naming a pattern; adding another pattern word is consistent.
3. **`diag` has both usages in Mathlib.** Grounded (`Finset.diag`, `Matrix.diag`,
   `CategoryTheory.Functor.diag`, `OrderHom.diag`/`OrderHom.onDiag`) and ungrounded, where it
   describes `fun i => (i,i)` or the entries `f i i` (`Filter.tendsto_diag`, `Set.range_diag`,
   `Matrix.IsAdjMatrix.apply_diag`). Both are established, in Order, Topology, Data and Matrix
   files alike, so `_diag`/`_diagonal` for "restrict to `f k k`" is squarely within precedent.
   Best of all is what the current `DiagCofinal` development does: make the statement itself
   mention `Functor.diag` / `Set.diagonal`, which turns the token from ungrounded into grounded.
4. **`_self` and `_same` are the competing spellings** and both are real conventions:
   `_self` for a repeated *term* (`sub_self`, `min_self`), `_same` for coinciding *indices*
   (`Pi.single_eq_same`, `Matrix.diag_single_same`, `gcd_same`). For `⨆ i, ⨆ j, f i j = ⨆ k, f k k`
   the repeated thing is the index, so `_diag` (picture) and `_same` (index) are both defensible;
   `_diag` additionally matches the existing `Finset.sum_diag` / `OrderHom.onDiag` vocabulary.
5. **For the hypothesis suffix, prefer the `is`-ful spelling.** Mathlib's own cofinality lemmas
   are `sSup_le_sSup_of_isCofinalFor`, `IsCofinal.of_not_bddAbove`, `not_bddAbove_iff_isCofinal`.
   So `…_of_isCofinal` is the spelling that matches current practice; `…_of_cofinal` follows the
   older `of_open`/`of_closed`/`of_compact` family, which still has 1 660 occurrences but is not
   what new lemmas are named.

## 6. Reproducing

```
lake env lean naming-survey/Survey.lean > naming-survey/output.txt
lake build RequestProject.NamingConventionEvidence
```

`output.txt` additionally contains: the top 120 FREE and top 80 ELSEWHERE tokens with examples,
the per-area token tables, per-area FREE/ELSEWHERE examples, and a per-area breakdown for 37
watched tokens (`self`, `of`, `diag`, `diagonal`, `cofinal`, `aux`, `comm`, `tfae`, …) split by
whether the token is realised in the statement.
