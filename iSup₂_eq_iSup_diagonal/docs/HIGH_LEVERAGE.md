# High-leverage contribution opportunities in Mathlib / Lean core

Scope of this scan: the Mathlib checkout vendored in this project,
`leanprover-community/mathlib4` at `8f9d9cff` (tag `v4.28.0`), Lean `v4.28.0`.
Every "exists / does not exist" claim below was checked with `ripgrep` against that
exact tree, so the findings are pinned to a specific commit and may drift as Mathlib
evolves — re-run the queries in the *Methodology* section before acting.

The guiding metric is **leverage = (reuse breadth) × (difficulty of doing without it)**.
A cofinality convenience lemma scores low on both; the candidates below are ordered so
that the ones with the best leverage-to-effort ratio come first *within* each category.

---

## Category 5 — Generalize / complete a widely-used lemma (highest ratio, lowest risk)

This is the single best category to *start* in: the reuse is immediate, the risk is
low, and a reviewer can check the whole change at a glance. Two concrete, verified,
machine-checked instances:

### 5a. `ciInf_mono'` — missing dual of `ciSup_mono'`  ✅ proved here
- **Evidence.** `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean:523` defines
  `ciSup_mono'`; a grep of that file (and of all of `Order/`) finds **no** `ciInf_mono'`.
- **Why it is missing.** It is *not* a mechanical `@[to_dual]`: the sup version lives in
  the `ConditionallyCompleteLinearOrderBot` section, and Mathlib has no
  `ConditionallyCompleteLinearOrderTop` class to host the literal dual.
- **The fix (verified in `RequestProject/HighLeverage.lean`).** State it over a plain
  `ConditionallyCompleteLattice` with the honest side conditions — `[Nonempty ι']` and
  `BddBelow (range f)` — and it discharges dually to `ciSup_mono'`:
  ```lean
  theorem ciInf_mono' [ConditionallyCompleteLattice α] {f : ι → α} {g : ι' → α}
      [Nonempty ι'] (hf : BddBelow (Set.range f)) (h : ∀ i', ∃ i, f i ≤ g i') :
      iInf f ≤ iInf g :=
    le_ciInf fun i' => Exists.elim (h i') (ciInf_le_of_le hf)
  ```
- **Leverage.** Small, but this is exactly the "add the missing dual next to the existing
  lemma" shape upstream loves, and it removes a real asymmetry in a core order file.
  It is the natural companion to the diagonal/cofinality work already in this project
  (`RequestProject/Diagonal.lean`), and was flagged as a Tier-B gap in `SECOND_REVIEW.md`.

### 5b. Systematic `@[to_dual]` / `@[to_additive]` audit
Several files carry explicit notes that a dual/additive twin is missing or was skipped:
- `Mathlib/Algebra/Group/Submonoid/Pointwise.lean:208` — `-- todo: add \`to_additive\`?`
- `Mathlib/GroupTheory/FreeGroup/Reduce.lean:287` — `@[to_additive] doesn't succeed, possibly due to a bug`
- `Mathlib/Analysis/Normed/Group/Seminorm.lean:421` — a block that "ought to be automated using `to_additive`".

Each such note is a candidate: either supply the missing twin by hand (as in 5a) or fix
the `to_additive`/`to_dual` invocation. Leverage scales with how widely the base lemma is
used; grep the base name's call sites first to prioritize.

---

## Category 1 — Missing infrastructure that many files reimplement ad hoc

Leverage here = number of downstream files that currently do the thing by hand.

### 1a. The cofinal-diagonal collapse (already scoped in this project)
The prior work in this repo (`RequestProject/Diagonal.lean`, `PR_PLAN.md`) is a clean
example of this category: `iSup₂_eq_diagonal` + `@[to_dual]`, collapsing the
hand-rolled diagonal arguments in `ENat.iSup_add_iSup`, `ENNReal.iSup_add_iSup`, and
`ENNReal.iInf_add_iInf`. It is ready to ship; see `PR_PLAN.md`/`UPSTREAM_REVIEW.md`.

### 1b. "Should be generalized to `PiLp`" — a recurring, blocked generalization
Two analysis files explicitly duplicate work that belongs on `PiLp`:
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:264` — `-- TODO : This should be generalized to \`PiLp\`.`
- `Mathlib/Analysis/InnerProductSpace/Calculus.lean:28` — "The last part of the file should be generalized to `PiLp`."

This is genuine missing infrastructure (a real `PiLp` API for the constructions currently
done only for `EuclideanSpace`). Higher effort than a single lemma, but the leverage is
the whole tail of both files plus future `PiLp` users.

### 1c. Other source-confirmed "should be generalized" anchors
`rg -n "should be generaliz" Mathlib` returns exactly 7 hits at this commit; besides the
two `PiLp` ones, the tractable-looking ones are
`Mathlib/RingTheory/DedekindDomain/Dvr.lean:65` (generalize to preserving any Krull
dimension) and `Mathlib/ModelTheory/Order.lean:411` (blocked on a missing
`OrderEmbeddingClass`/`RelEmbeddingClass`). Each is a self-documenting starting point.

---

## Category 2 — A theorem that seeds a whole area

Highest ceiling, highest effort. The honest way to source these is the community's own
"missing results" tracking rather than guessing; treat the following as *method*, not a
verified gap list, because these lists move quickly:
- Work from the leanprover-community "undergraduate/graduate math not yet in Mathlib"
  lists and the `100.yaml` / `1000.yaml` theorem-coverage files shipped in the repo
  (`docs/`), which are the canonical, maintained record of what is present vs. absent.
- Pick a result that is a *prerequisite* for a cluster of corollaries (so one hard proof
  unlocks many easy ones), not an isolated trophy theorem.
Because a single session cannot honestly certify "Mathlib lacks theorem X" across the
whole library, this category is documented as a directed search rather than a concrete
claim; the machine-checked artifacts in this repo are confined to Categories 5 and 1.

---

## Category 3 — Decidability / computability bridges

These let `decide`/`native_decide` (or plain compilation) close goals that are currently
manual or `noncomputable`. Source-confirmed anchors:

### 3a. `Decidable (IsMulCentral a)` — the Center TODO  ✅ proved here
- **Evidence.** `Mathlib/Algebra/Group/Center.lean:213` — `-- TODO Add instance : Decidable (IsMulCentral a)`.
  A grep of `Mathlib/` at this commit finds **no** `Decidable (Commute _ _)`, **no**
  `Decidable (IsMulCentral _)`, and **no** `Fintype`-based `DecidablePred (· ∈ Set.center M)`.
- **The fix (verified in `RequestProject/DecidableCenter.lean`).** Provide
  `Decidable (Commute a b)` from `DecidableEq`, then `Decidable (IsMulCentral z)` from
  `Fintype`+`DecidableEq` via the `mk_iff` lemma `isMulCentral_iff`, and as the downstream
  payoff a `Fintype`-only `DecidablePred (· ∈ Set.center M)` that drops the bespoke
  decidability hypothesis on the existing `decidableMemCenter`. Each carries an
  auto-generated `to_additive` twin, and `example : IsMulCentral (1 : Multiplicative (ZMod 3)) := by decide`
  confirms the instance actually computes. Depends only on `propext`/`Quot.sound`.

### Other source-confirmed anchors
- `Mathlib/Order/SupIndep.lean:75` — TODO to speed up the `SupIndep` decidability
  instance and **drop the `[DecidableEq ι]` assumption**; weakening an instance's
  hypotheses is exactly a computability bridge with library-wide reach.
- `Mathlib/Combinatorics/SimpleGraph/Coloring.lean:126` — `-- TODO make this computable`.
- `Mathlib/Data/SetLike/Fintype.lean:23` — a computable version "should be possible for
  most" `SetLike` fintypes.
Leverage = every downstream `decide`/`Fintype`/instance-synthesis site that currently
fails or must go `noncomputable`. Start with the ones phrased as "drop the
`Decidable*`/`DecidableEq` assumption", since those strictly widen applicability.

---

## Category 4 — Automation (tactics / `simp` / `norm_num` / `gcongr` extensions)

Leverage scales with *every future user*, not just current callers — the highest ceiling
of the "small change" categories. Source-confirmed anchors:
- `Mathlib/Algebra/Order/Ring/Basic.lean:118` — `-- TODO: Use \`gcongr\`, \`positivity\`, \`ring\` once those tactics are made available here`:
  a concrete place where extending tactic availability removes hand proofs.
- `Mathlib/Algebra/GCDMonoid/Multiset.lean:23` and `.../Finset.lean:24` — both ask to
  "simplify with a tactic"; a small `gcd`/`lcm`-aware `simp` set or extension would clear
  both.
- `Mathlib/CategoryTheory/Slice.lean:24` — invitation to generalize the `slice` tactic to
  other associative structures.
- `Mathlib/Tactic/ExtractGoal.lean:31` (code actions) and `Mathlib/Tactic/Hint.lean:101`
  (run candidate tactics in parallel) are UX/automation TODOs on the tactic framework
  itself.
A `simp`/`gcongr` extension is usually a better first automation PR than a brand-new
tactic: it plugs into existing machinery, so review cost is low and it composes with
everything downstream.

---

## How impact was estimated

For each candidate: **reuse breadth** ≈ number of current call sites the change touches
plus the size of the API surface it opens (`rg` the base declaration name across
`Mathlib/`); **difficulty of doing without it** ≈ how awkward the current workaround is
(a hand-rolled diagonal argument or a `noncomputable`/manual `decide` scores high; a
one-liner people can inline scores low). The ranking prefers `breadth × difficulty`, and
within a tie prefers the smaller, more self-contained change (mathlib rewards small,
discoverable, framework-free lemmas over clever abstractions).

## Methodology — reproducible `ripgrep` queries

Run from the Mathlib source root. These are the exact queries used for this scan:

```bash
# Category 5: missing duals / additive twins (inspect base-name call sites to rank)
rg -n "@\[to_additive\].*TODO|TODO.*to_additive|todo: add .to_additive" Mathlib
rg -n "theorem ciSup_mono'|theorem ciInf_mono'" Mathlib/Order   # confirms 5a gap

# Category 1: infrastructure others reimplement / explicit generalization notes
rg -in "should be generaliz" Mathlib
rg -in "ad hoc|by hand|reimplement" Mathlib

# Category 2: maintained coverage lists (method, not a single grep)
rg -l "" Mathlib/../docs 2>/dev/null; ls docs/*.yaml   # 100.yaml / 1000.yaml etc.

# Category 3: decidability / computability bridges
rg -in "TODO.*(decidab|computab)|drop the \[Decidable|make this computable" Mathlib

# Category 4: tactic / simp / norm_num automation
rg -in "TODO.*tactic|simplify with a tactic|once those tactics are made available" Mathlib
```

## What is machine-checked in this repo

- `RequestProject/HighLeverage.lean` — `ciInf_mono'` (Category 5a) with a sanity check
  against `ciSup_mono'`. Builds with no `sorry`/`admit`.
- `RequestProject/DecidableCenter.lean` — `Decidable (Commute _ _)`,
  `Decidable (IsMulCentral _)`, and a `Fintype`-only `DecidablePred (· ∈ Set.center M)`
  (Category 3a), each with a `to_additive` twin and a `by decide` sanity check. Builds
  with no `sorry`/`admit`.
- `RequestProject/Diagonal.lean`, `RequestProject/DiagonalVariations.lean` — the
  Category 1a cofinal-diagonal family from prior runs (see `PR_PLAN.md`).

The remaining candidates are, by nature (missing theories, tactics, whole-library
decidability audits), not single lemmas; they are documented above with pinned source
line references rather than proved here, to keep every claim in this file honest about
whether it is *checked* or *scoped*.
