# Summary of changes for run d0d65e98-3fe3-49ce-b75c-3e9b08c2d61b
Added `RequestProject/NextPR.lean` as a focused, ready-to-adapt Lean proposal containing:

- `ciSup₂_eq_ciSup_diagonal` with the requested `ConditionallyCompleteLattice` and `Nonempty` assumptions.
- `ciSup₂_eq_ciSup_diagonal'` for `ConditionallyCompleteLinearOrderBot`, without requiring a nonempty index.
- Proofs using `ciSup_mono_of_forall_exists` and its primed variant in both inequality directions. The proofs derive boundedness of the inner and outer families from diagonal boundedness and cofinality.
- A concrete `Cardinal.ciSup_add_ciSup_diagonal` caller that strengthens `Cardinal.ciSup_add_ciSup` by collapsing its double supremum to the diagonal.
- No complete-lattice mutual-cofinality additions, keeping the proposed change within the requested scope.

The project’s pinned Mathlib predates the two requested helper names, so the file includes private compatibility versions with the intended signatures; these are clearly marked as scaffolding rather than proposed upstream declarations.

Verified the full project builds successfully. The new file contains no `sorry`, `admit`, new axioms, or `implemented_by`, and all three public theorems use only standard permitted axioms.

# Summary of changes for run f36499cf-5d19-48b1-9b42-cd004b4678a7
Created `RequestProject/MutualCofinalityPR.lean`, a standalone Lean file containing only the proposed follow-up PR material:

- `sSup_eq_sSup_of_isCofinalFor`
- `sInf_eq_sInf_of_isCoinitialFor`
- `iSup_eq_iSup_of_forall_exists_le`, derived via the set-level theorem on ranges
- `iInf_eq_iInf_of_forall_exists_le`, derived dually
- Replacement proofs for `iSup_eq_iSup_subseq_of_monotone`
- Replacement proofs for `iSup_eq_iSup_subseq_of_antitone`

The file notes that the two existing `iInf` subsequence results benefit transitively and need no direct rewrite. The complete project builds successfully, the file contains no `sorry`/`admit`, and all four named lemmas were verified to have no axiomatic dependencies.

# Summary of changes for run 413cfb46-8f82-4a78-80ef-fe9e447b32ff
Yes—a subsequent PR can coherently center on mutual cofinality, but I would keep its contents evidence-driven:

1. Add
```lean
theorem sSup_eq_sSup_of_isCofinalFor
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) :
    sSup s = sSup t
```
and the `sInf`/`IsCoinitialFor` dual.

2. Derive the indexed mutual-cofinality corollary `iSup_eq_iSup_of_forall_exists_le` (and its `iInf` dual) by applying the set theorem to the two ranges.

3. Refactor `iSup_eq_iSup_subseq_of_monotone` and `iSup_eq_iSup_subseq_of_antitone`. Their two `iInf` counterparts already delegate to these, so they benefit transitively without separate proof rewrites.

I would not promise three direct refactors merely to increase the count. `Monotone.iSup_comp_eq` is a valid third specialization but its existing proof is already very short; `iSup_ne_bot_subtype` only partly simplifies. Nor should the diagonal theorem be rederived through this chain in the PR: the range/product route weakens its index generality from `Sort*` to `Type*`, and the diagonal PR already has its own three concrete callers.

Thus the strongest follow-up shape is: **set-level equality pair → indexed corollary pair → two clean subsequence refactors (plus two transitive dual benefits)**. The subset-specific wrapper can wait for a concrete caller or reviewer request.

# Summary of changes for run 439fbfcc-9655-45f8-abe5-7665165e555c
Scanned all 7,648 pinned Mathlib Lean files using exact API, multiline proof-shape, reindexing/range/subtype, subsequence, and dual-pattern searches.

Found a genuine chain:

`cofinal-subset sSup equality → indexed cofinal reindexing → diagonal + monotone/antitone subsequence lemmas + Monotone.iSup_comp_eq + iSup_ne_bot_subtype`.

The best intermediate lemma has at least four natural specializations; the two subsequence theorems are the cleanest existing refactors. The diagonal derivation has a `Type*` versus `Sort*` generality caveat, while `Monotone.iSup_comp_eq` is already concise.

Added:
- `SUBSET_TRANSITIVE_CALLERS.md`: detailed findings, caller assessment, risks, and recommendation.
- `RequestProject/SubsetTransitiveCallers.lean`: machine-checked versions of the subset lemma, intermediate reindexing lemmas, and five caller refactors.

The full project builds successfully with no `sorry`/`admit`; checked declarations use only accepted standard axioms. Recommendation: the chain is credible as a coherent cofinal-reindexing API PR, but the earlier diagonal-only PR remains the smaller, lower-risk first contribution.

# Summary of changes for run 9096fe9f-fbe8-495f-8cf1-52f5aecba08e
Expanded the visual guide into a polished 6-page A4 document:

- `contribution-patterns.tex` — editable LaTeX/TikZ source.
- `contribution-patterns.pdf` — compiled PDF.

The four new pages add:
- the big idea that duplicate proofs indicate a missing common factor;
- an abstraction ladder from concrete `ENat`/`ENNReal` callers to indexed and set-level cofinality;
- the “cofinal diagonal as lossless compression” insight;
- skyline, express-train, and synchronised-clock analogies;
- a category-theoretic dictionary: preorders as thin categories, suprema as colimits, cofinal maps as final functors, and order duality as passage to the opposite category;
- the diagonal map `Δ : I → I × I` and its relation to directedness;
- a clarification that the Lean theorem uses weaker value-level cofinality rather than requiring ordered indices;
- structural API lessons about universal properties, minimal typeclass assumptions, duality, and refactoring evidence;
- visual extraction and review checklists.

The PDF was compiled successfully, checked page-by-page, and confirmed as a 6-page A4 document.

# Summary of changes for run f0db91c4-ae11-49c1-af5f-2fc60db7ee73
I searched all 7,648 Lean files in the checked-out Mathlib source and documented the results in `COFINAL_CALLERS_AND_PR.md`.

Main findings:

- `sSup_le_sSup_of_isCofinalFor` has only one direct downstream use, in `RingTheory/Filtration.lean`, and that use needs only an inequality—not either proposed equality.
- No existing complete-lattice proof directly matches `subset + reverse cofinality`, so `sSup_eq_sSup_of_subset_of_isCofinalFor` currently has no demonstrated caller.
- The foundational mutual-cofinality theorem has strong precedent in the conditionally complete API: `csSup_eq_csSup_of_forall_exists_le`, its infimum dual, and specialized subset/cofinality image lemmas.
- The indexed mutual-cofinality theorem has two especially clean prospective callers: `iSup_eq_iSup_subseq_of_monotone` and `iSup_eq_iSup_subseq_of_antitone` in `Topology/Order/MonotoneConvergence.lean`.
- The diagonal pair has three direct duplicate callers:
  1. `ENat.iSup_add_iSup`;
  2. `ENNReal.iSup_add_iSup`;
  3. `ENNReal.iInf_add_iInf`.

Recommended split:

1. **PR 1:** `iSup₂_eq_diagonal` / `iInf₂_eq_diagonal`, simplifying those three duplicate callers. This has the clearest immediate reuse.
2. **PR 2:** `sSup_eq_sSup_of_isCofinalFor` / `sInf_eq_sInf_of_isCoinitialFor`, optionally with the indexed mutual-cofinality pair and the two subsequence simplifications.
3. Defer `sSup_eq_sSup_of_subset_of_isCofinalFor` until a concrete caller or reviewer request appears. It is a valid one-line convenience corollary, but currently lacks reuse evidence.

I added that subset theorem to `Main.lean` as a checked demonstration using `hst.isCofinalFor`. It compiles without `sorry` or `admit`, uses no axioms, and the full project build succeeds. All work was committed and pushed.

# Summary of changes for run 6893c4cb-7397-4a7f-9e97-5ceaaba7da54
Ho creato i due file richiesti in italiano:

- `visualizzazione-pattern-pr-it.tex` — sorgente LaTeX/TikZ modificabile;
- `visualizzazione-pattern-pr-it.pdf` — PDF A4 compilato di 3 pagine.

Il documento visualizza:
- il passaggio dalle prove duplicate al lemma riusabile;
- la diagonale cofinale nella famiglia doppiamente indicizzata;
- i tre livelli di generalità, incluso il possibile lemma più generale su `sSup` e `IsCofinalFor`;
- i tre chiamanti semplificati (`ENat.iSup_add_iSup`, `ENNReal.iSup_add_iSup`, `ENNReal.iInf_add_iInf`);
- cosa includere e cosa rinviare nella PR;
- un diagramma decisionale su come migliorare o lasciare focalizzata la PR.

La raccomandazione esposta è di mantenere la prima PR concentrata su `iSup₂_eq_diagonal`, sul duale `iInf₂_eq_diagonal` e sui tre riusi esistenti. Il wrapper più generale su `sSup` va lasciato a un seguito, salvo un ulteriore uso indipendente o una richiesta del reviewer.

Il PDF è stato compilato e controllato: formato A4, 3 pagine, senza errori o avvisi di impaginazione.

# Summary of changes for run c7986ff5-1f4f-432b-9c52-7c5c483977bc
Ho scritto l’analisi in italiano in `RISPOSTA_ITALIANO.md`.

Il collegamento principale è questo:

- `hst : s ⊆ t` dà `sSup s ≤ sSup t` tramite `sSup_le_sSup`;
- `hts : IsCofinalFor t s` significa che ogni elemento di `t` è dominato da un elemento di `s`, e dà `sSup t ≤ sSup s` tramite `sSup_le_sSup_of_isCofinalFor`;
- le due disuguaglianze producono l’uguaglianza per antisimmetria.

Ho inoltre distinto queste correzioni matematiche/API dai messaggi CI dello screenshot: il problema su `rw` è un errore a cascata, il warning di `to_dual` richiede i nomi simmetrici `iSup₂_eq_diagonal` / `iInf₂_eq_diagonal`, la riga lunga è un problema stilistico e l’avviso Node.js non appartiene alla PR matematica.

La raccomandazione finale è di mantenere la PR focalizzata sul lemma diagonale e sui tre chiamanti già individuati (`ENat.iSup_add_iSup`, `ENNReal.iSup_add_iSup`, `ENNReal.iInf_add_iInf`). Il lemma generale su `sSup`, pur corretto e naturale, per ora combina due disuguaglianze esistenti e ha un solo chiamante noto; conviene rinviarlo finché non emerga un ulteriore riuso indipendente o una richiesta esplicita del reviewer.

# Summary of changes for run 2a414f6d-25bc-4fca-bdbc-bf5a5214f6f0
Recommended PR refactor: keep the diagonal lemma plus its three demonstrated callers; do **not** add the thin set-level equality helper yet unless you find another independent caller.

Two API corrections to the proposed helper:
- `IsCofinalFor` already fixes the relation, so with `s ⊆ t` and every `y ∈ t` dominated by some `x ∈ s`, the hypothesis is `IsCofinalFor t s`.
- The subset lemma in this Mathlib version is `sSup_le_sSup`, not `sSup_mono`.

The valid helper would therefore be:
```lean
theorem sSup_eq_sSup_of_subset_of_isCofinalFor
    [CompleteSemilatticeSup α] {s t : Set α}
    (hst : s ⊆ t) (hts : IsCofinalFor t s) : sSup s = sSup t := by
  apply le_antisymm
  · exact sSup_le_sSup hst
  · exact sSup_le_sSup_of_isCofinalFor hts
```
It is mathematically natural but currently just packages two one-line inequalities, with only the diagonal result as a known caller. That makes it less compelling than the focused diagonal PR.

I corrected `UPSTREAM.patch` and the supporting files:
- Renamed the pair to `iSup₂_eq_diagonal` / `iInf₂_eq_diagonal`. The former name did not automatically dualize as intended, while explicitly supplying the predicted target caused the CI linter warning.
- Kept the three caller refactors: `ENat.iSup_add_iSup`, `ENNReal.iSup_add_iSup`, and `ENNReal.iInf_add_iInf`.
- Split the long `ENNReal.iInf_add_iInf` declaration line.
- Added `CI_FIX.md` explaining the recommended scope and every CI annotation.

The “Unknown identifier `rw`” was downstream fallout from the failed declaration processing, not a missing tactic import. The Node.js warning belongs to repository workflow maintenance and should not be addressed in this mathematical PR.

Verified: the corrected patch applies cleanly; all three affected Mathlib modules build; style lint passes; the updated Lean demonstrations compile without `sorry` or `admit`. Changes were committed and pushed.

# Summary of changes for run ee7f11e2-e9a0-46de-8093-87b1a419220a
Submit the three caller replacements together with the generic diagonal lemma and its generated dual. The complete apply-ready diff is in `UPSTREAM.patch`; the individual snippets and explanation are in `SUBMISSION_CODE.md`.

For `ENat.iSup_add_iSup`:
```lean
lemma iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · simp_rw [ENat.iSup_add, ENat.add_iSup]
    exact iSup₂_eq_iSup_diagonal (fun i j ↦ f i + g j) h
```

For `ENNReal.iSup_add_iSup`, use the same proof with `ENNReal.iSup_add` and `ENNReal.add_iSup`.

Also replace `ENNReal.iInf_add_iInf`:
```lean
theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) :
    iInf f + iInf g = ⨅ a, f a + g a := by
  cases isEmpty_or_nonempty ι
  · simp only [iInf_of_empty, top_add]
  · simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
    exact iInf₂_eq_iInf_diagonal (fun i j ↦ f i + g j) h
```

There is no corresponding ENat infimum caller. I updated `UPSTREAM.patch` to include all three replacements, plus `iSup₂_eq_iSup_diagonal` and `@[to_dual iInf₂_eq_iInf_diagonal]`. The resulting affected Mathlib files compile successfully without `sorry` or `admit`, and the patch applies cleanly to the matching source snapshot.

# Summary of changes for run 4295fb5c-4fed-441d-bc27-0d6d3a6eb3b8
Yes — your submitted diff addresses **all items in the minimal meaningful first PR** exactly:

1. It adds the single generic lemma `iSup₂_eq_iSup_diagonal` in `Order/CompleteLattice/Basic.lean`, in the `CompleteSemilatticeSup` section.
2. `@[to_dual iInf₂_eq_iInf_diagonal]` generates the required infimum dual.
3. It simplifies all three demonstrated duplicate callers:
   - `ENat.iSup_add_iSup`
   - `ENNReal.iSup_add_iSup`
   - `ENNReal.iInf_add_iInf`

So nothing from that checklist is missing. This is the intended small, self-contained PR: one reusable theorem, its automatic dual, and three concrete refactors.

The `IsCofinalFor` proposal is more general, but it is **additional scope**, not something required to complete this minimal PR. It handles arbitrary mutually cofinal sets/families, whereas your theorem handles the specific cofinal-diagonal pattern. Unless a reviewer asks to generalize the current PR around `IsCofinalFor`, I would keep the submitted PR focused as it is and treat the set-level equality as a possible follow-up.

I added `ISCOFINAL_COMPARISON.md` documenting the exact scope comparison and recommendation.

# Summary of changes for run a9a31505-b13d-4d02-befd-8ad5ffa994bd
Explored the stabilizer TODO and produced a machine-checked unification proposal.

### Proposed generic lemma
Added `MulAction.stabilizer_eq_of_smul_mem_iff` in `RequestProject/StabilizerUnification.lean`. It identifies `stabilizer G s` with a candidate subgroup `H` when:

1. membership in `H` is detected at one point: `a • b ∈ s ↔ a ∈ H`; and
2. every `a ∈ H` maps members of `s` back into `s`.

The second condition is intentionally one-sided: subgroup closure under inverses supplies the reverse implication required for stabilization. A separate assumption `b ∈ s` is unnecessary because it follows by specializing the detector condition to `1`.

The lemma carries `@[to_additive]`, successfully generating the corresponding additive result `AddAction.stabilizer_eq_of_vadd_mem_iff`.

### Three simplified callers
The same file proves versions of all three existing results through this criterion:

- `stabilizer_subgroup_via_smul_mem_iff`
- `stabilizer_op_subgroup_via_smul_mem_iff`
- `stabilizer_subgroup_op_via_smul_mem_iff`

Their remaining proofs only specify the detector `1` and whether subgroup closure is used as `a * x` or `x * a`, cleanly accounting for the two opposite-group cases.

### Write-up
Added `STABILIZER_UNIFICATION.md` with:

- the proposed upstream statement and proof idea;
- before/after-style code for all three callers;
- naming and placement recommendations;
- discussion of the maintainership tradeoff: this resolves the explicit TODO and removes duplicated cancellation logic, although the line-count saving across only three callers is modest.

### Verification
`RequestProject/StabilizerUnification.lean` builds without `sorry` or `admit`. The generic theorem, generated additive theorem, and all three callers are kernel-checked and use only accepted standard axioms (`propext`, `Classical.choice`, and `Quot.sound`). All changes are committed and pushed.

# Summary of changes for run 277e94df-c141-4853-9d60-1198f2708737
I picked up the high-leverage contribution scan and moved another candidate from "documented" to "machine-checked."

What I added this session:
- `RequestProject/DecidableCenter.lean` — a machine-checked Category 3 (decidability/computability bridge) contribution that discharges the explicit TODO at `Mathlib/Algebra/Group/Center.lean:213` (`-- TODO Add instance : Decidable (IsMulCentral a)`). It provides:
  - `Decidable (Commute a b)` from `DecidableEq`,
  - `Decidable (IsMulCentral z)` from `Fintype`+`DecidableEq` (via the `mk_iff` lemma `isMulCentral_iff`), and
  - as the downstream payoff, a `Fintype`-only `DecidablePred (· ∈ Set.center M)` that drops the bespoke decidability hypothesis carried by the current `decidableMemCenter`.
  Each declaration carries an auto-generated `to_additive` twin (so the `AddCommute`/`IsAddCentral`/`addCenter` side comes for free), the file builds with no `sorry`/`admit`, the instances depend only on standard axioms (`propext`, `Quot.sound`), and a `by decide` example confirms the instance actually computes. I confirmed by grep that none of these instances exist in the vendored Mathlib (`8f9d9cff`, tag v4.28.0).
- Updated `HIGH_LEVERAGE.md` to record this as verified Category 3a and to list the new file in the "What is machine-checked" section.

This complements the previously machine-checked candidates (`ciInf_mono'`, Category 5a; the cofinal-diagonal family, Category 1a): the report now backs Categories 1, 3, and 5 with compiling Lean rather than only pinned source references. The full project builds successfully. All work is committed and pushed.

On the underlying question of where high-leverage effort pays off: the best effort-to-impact starts are (5) completing/generalizing widely-used lemmas by supplying missing duals/twins, and (3) decidability bridges that let `decide`/instance synthesis close goals that currently need hand-supplied hypotheses — both are small, low-risk, and immediately reusable. The `Decidable (IsMulCentral)` instance added here is a concrete example: `IsMulCentral`/`Commute` are foundational predicates, so a `Decidable` instance from `Fintype`+`DecidableEq` alone widens applicability across the group/ring/centralizer APIs. Higher-ceiling but higher-effort categories (missing infrastructure reimplemented ad hoc, seed theorems, and tactic/`simp`/`gcongr` automation) are documented in `HIGH_LEVERAGE.md` with pinned source anchors and reproducible ripgrep queries.

# Summary of changes for run 388c549a-dceb-48a2-ac9f-9123658025ff
I scanned the Mathlib checkout vendored in this project (`leanprover-community/mathlib4` at `8f9d9cff`, tag `v4.28.0`) for high-leverage contribution opportunities, organized around the five framings you gave (missing infrastructure, seed theorems, decidability/computability bridges, automation, and generalizations). Deliverables:

- `HIGH_LEVERAGE.md` — the report. It ranks candidates by leverage = (reuse breadth) × (difficulty of doing without it), and every "exists / doesn't exist" claim is pinned to specific source line references in that exact commit and verified with ripgrep. It also includes the reproducible ripgrep queries used, so the scan can be re-run as Mathlib drifts.

- `RequestProject/HighLeverage.lean` — machine-checked backing for the one candidate small enough to discharge here: `ciInf_mono'`, the missing dual of `ciSup_mono'` in `Order/ConditionallyCompleteLattice/Indexed.lean`. Confirmed absent by grep; it is not a mechanical `@[to_dual]` (no `ConditionallyCompleteLinearOrderTop` class), so it is stated over a plain `ConditionallyCompleteLattice` with honest side conditions (`[Nonempty ι']`, `BddBelow (range f)`) and proved dually. The file builds with no `sorry`/`admit` and the theorem depends only on standard axioms (`propext`, `Quot.sound`).

Highlights of the report's findings (all with source line references):
- Category 5 (generalize/complete a widely-used lemma) is the best effort-to-impact starting point: `ciInf_mono'` (proved here) plus a `@[to_dual]`/`@[to_additive]` audit of files that explicitly note a missing twin.
- Category 1 (infrastructure reimplemented ad hoc): the cofinal-diagonal collapse already scoped in this repo, plus the recurring "should be generalized to `PiLp`" duplication in two InnerProductSpace files.
- Category 3 (decidability/computability): concrete anchors such as dropping `[DecidableEq ι]` from the `SupIndep` decidability instance and adding `Decidable (IsMulCentral a)`.
- Category 4 (automation): places where a `gcongr`/`simp` extension would remove hand proofs (e.g. GCDMonoid Multiset/Finset, Order/Ring/Basic).
- Category 2 (seed theorems): documented as a directed search against the maintained coverage lists rather than a single-session "Mathlib lacks X" claim, since that cannot be honestly certified library-wide in one pass.

The full project still builds. All work is committed and pushed. Note: I confined machine-checked claims to Categories 1 and 5; the larger candidates (missing theories, tactics, whole-library decidability audits) are, by nature, not single lemmas and are documented with pinned references rather than proved.

# Summary of changes for run 36830ce8-4230-44c9-b137-7374c611a5dd
Short answer: yes — provided you treat the second PR as the *complement* of whatever went into the first. The two passages describe two different framings of the **first/main** PR, and the second PR is simply whatever that first PR deferred. They are consistent as long as you don't ship the same lemma twice.

Reconciling the two:

- The "minimal first PR" framing (from the earlier summary) puts only `iSup₂_eq_iSup_diagonal` (+ its `@[to_dual]` dual) and the three simplified callers (`ENat.iSup_add_iSup`, `ENNReal.iSup_add_iSup`, `ENNReal.iInf_add_iInf`) in PR 1. Under that framing, PR 2 = the reviewer-requested conditionally-complete family plus the `IsCofinalFor` equality companions.

- The SECOND_REVIEW §4 framing you quoted folds more into PR 1: it *reframes* the first PR around `IsCofinalFor`, leading with `sSup_eq_sSup_of_isCofinalFor` / `sInf_eq_sInf_of_isCoinitialFor` (as equality companions of the existing `≤` lemmas), keeps `iSup_eq_iSup_of_forall_exists_le` and `iSup₂_eq_iSup_diagonal` (+ duals) as corollaries, and simplifies all three callers — in one PR.

So under the SECOND_REVIEW framing, the `IsCofinalFor` companions and all three callers are *already in PR 1*, and the second PR should therefore contain exactly the items §4 explicitly defers, namely the Tier-B gaps:
1. the conditionally-complete diagonal lemmas `ciSup₂_eq_ciSup_diagonal` and `ciSup₂_eq_ciSup_diagonal'` (the versions the reviewer asked for on Zulip), with the `Cardinal.ciSup_add_ciSup` collapse as a demonstrated caller (checked as `cardinal_ciSup_add_ciSup_via_diagonal`) — `Cardinal` is `ConditionallyCompleteLinearOrderBot`, so this needs the CC version and can't ride on PR 1;
2. `ciInf_mono'` (the missing dual of `ciSup_mono'`; not a mechanical `@[to_dual]` because there is no `ConditionallyCompleteLinearOrderTop` class), and the `iInf` duals of the CC diagonal lemmas;
3. the conditionally-complete cofinal set-level family `csSup_..._of_isCofinalFor` (+ equality + duals), which needs `BddAbove` side conditions and is currently absent entirely.

The one inconsistency to avoid: do NOT put the `IsCofinalFor` equality companions (`sSup_eq_sSup_of_isCofinalFor` / `sInf_eq_sInf_of_isCoinitialFor`) or the three complete-lattice callers in PR 2 if you followed §4 and already shipped them in PR 1 — that would be a double-submission. Conversely, if PR 1 was the minimal diagonal-only version, then those `IsCofinalFor` companions belong in PR 2 alongside the CC family.

Recommended concrete second PR (assuming PR 1 followed the §4 reframe): "Order: conditionally-complete diagonal/cofinality lemmas" — add `ciSup₂_eq_ciSup_diagonal` / `ciSup₂_eq_ciSup_diagonal'` next to `ciSup_mono'` in `Order/ConditionallyCompleteLattice/Indexed.lean`, add the `Cardinal` caller simplification as the demonstrated reuse, and mention `ciInf_mono'` and the `csSup..._of_isCofinalFor` family as the natural next follow-up. All of these lemmas are already machine-checked in `Main.lean` / `RequestProject/Diagonal.lean` (builds with no `sorry`/`admit`). PR_PLAN.md and SECOND_REVIEW.md contain the fuller write-up. No project files were changed in this turn.

# Summary of changes for run bb4861db-db47-4e4e-a64e-a4fa6e6fba33
I integrated the companion file you supplied and answered your question, backing the recommendation with a build that compiles cleanly.

## What I added to the project
- `RequestProject/Diagonal.lean` — the canonical diagonal/cofinality lemmas (the `import RequestProject.Diagonal` your companion file requires previously had no file to resolve to).
- `RequestProject/DiagonalVariations.lean` — your companion file, verbatim. It builds with no `sorry`/`admit`; the `@[to_dual]` on `sSup_diag_auto` correctly synthesizes `sInf_diag_auto`, and spot-checked axioms are the standard ones only.
- `PR_FORM.md` — the full write-up of the answer below.

Both new modules build (verified via `lean_build`); all work is committed and pushed.

## Which form to submit
Use the **tactic-mode `sSup`/`le_sSup` proof over the weakest typeclass `CompleteSemilatticeSup`, carrying `@[to_dual]`** — i.e. the `diag_sSup` / `sSup_diag_auto` form, which is exactly the canonical `iSup₂_eq_iSup_diagonal` in `RequestProject/Diagonal.lean`. Rationale along the design axes:
- Generality: state over `CompleteSemilatticeSup`, not `CompleteLattice` — nothing is lost and it is the most general home.
- Automation: avoid the shorter `iSup_mono'`/`CompleteLattice` golf and the term-mode `Classical.choose` proofs. The one-word golf breaks `@[to_dual]` (the generated infimum keeps a `SupSet` projection); the `sSup_le`/`le_sSup` argument dualizes cleanly, so one proof yields both the sup and inf lemmas.
- Style/direction: a short forward tactic block, not term mode and not `calc` (legible but too verbose for upstream).

So: not the `CompleteLattice` golf, not term-mode, not `calc`, not the conditionally-complete variants.

## Minimal meaningful first PR
Ship the smallest self-contained unit with demonstrated callers:
1. One new lemma `iSup₂_eq_iSup_diagonal` with `@[to_dual iInf₂_eq_iInf_diagonal]`, placed next to `iSup_mono'`/`iSup₂_mono'` in `Order/CompleteLattice/Basic.lean`.
2. Simplify the three duplicate callers it collapses: `ENat.iSup_add_iSup`, `ENNReal.iSup_add_iSup`, and `ENNReal.iInf_add_iInf` (via the generated dual).

That is the canonical "new lemma → replace duplicates → CI green" shape: one general, discoverable lemma, no new framework, immediate reuse.

Deliberately keep out of the first PR (each is its own follow-up): the `IsCofinalFor` equality companions (`sSup_eq_sSup_of_isCofinalFor` / `sInf_eq_sInf_of_isCoinitialFor`), the conditionally-complete variants plus the `Cardinal` caller, and the remaining Tier-B gaps noted in `SECOND_REVIEW.md`.

# Summary of changes for run 05e6a4a0-7f3d-4436-9bee-64e0f651c567
I explored Mathlib further for the same "cofinal ⇒ equal extremal bound" pattern and answered the follow-up questions, backing every claim with a machine-checked lemma in `Main.lean` (builds cleanly, no `sorry`/`admit`). New write-up in `SECOND_REVIEW.md`.

**Are the two callers exhaustive? No — there is a third.** `ENNReal.iInf_add_iInf` (`Data/ENNReal/Operations.lean:564`) is the infimum dual repeating the identical diagonal argument; it is simplified by the already-generated dual lemma `iInf₂_eq_iInf_diagonal`. Verified as `ennreal_iInf_add_iInf_via_diagonal`. Note the asymmetry: there is no `ENat.iInf_add_iInf`, so the honest count is three callers (two sup, one inf). The `*_of_monotone` and `BigOperators` variants are derived from these bases and benefit transitively (not separate callers).

**The most structural home already exists — this corrects the earlier recommendation.** The first round advised against a cofinality predicate as "new framework," but Mathlib already has `IsCofinalFor` (`Order/Bounds/Defs.lean`) with a full API (`.of_subset`, `.rfl`, `.trans`, and the `to_dual` dual `IsCoinitialFor`), plus the `≤`-half lemmas `sSup_le_sSup_of_isCofinalFor` / `sInf_le_sInf_of_isCoinitialFor`. Only the mutual-cofinality *equality* is missing. I added and checked `sSup_eq_sSup_of_isCofinalFor` and `sInf_eq_sInf_of_isCoinitialFor`, and showed the indexed `iSup_eq_iSup_of_forall_exists_le` is a one-line corollary of the set-level lemma. This is the ideal "add the equality next to the existing inequality" shape.

**What a third reviewer would suggest (tiers, source-confirmed):**
- Tier A (in-scope): the two auto-generated `iInf` duals, the two new `IsCofinalFor` equality lemmas, and the third caller.
- Tier B (genuine gaps, small follow-ups): `ciInf_mono'` is missing (dual of `ciSup_mono'`; not mechanical because Mathlib has no `ConditionallyCompleteLinearOrderTop`); the `iInf` duals of the conditionally-complete diagonal lemmas; and a conditionally-complete `csSup..._of_isCofinalFor` family (entirely absent, needs `BddAbove`).
- Tier C (already covered — nothing to add): the cofinal *reindexing* equality already exists as `Monotone.iSup_comp_eq` / `Monotone.iInf_comp_eq`, alongside `iSup_comp_le`, `Function.Surjective.iSup_comp`, `Equiv.iSup_comp`, and the `iSup_prod'`/`iSup_sigma'` reshapers. So the "closest genuine relative" the first round flagged is in fact already present.
- Tier D (conceptual home, not a small lemma): multiplicative `iSup_mul_iSup` equalities are absent (only `_le` halves; out of scope); Heyting/frames/topoi are complete lattices so the lemma already applies unchanged; and the categorical generalization (`CategoryTheory.Functor.Final`/`Initial`, final functors inducing isomorphic colimits) — of which the Caramello "bridge"/Morita idea is the right philosophical framing (cofinality as a presentation-invariant of the colimit) — should be cited as lineage in a docstring, not imported as machinery.

**Recommendation:** reframe the PR around `IsCofinalFor` (equality companions next to the existing `≤` lemmas), keep the indexed/diagonal lemmas as corollaries, simplify all three callers rather than two, and defer the Tier-B gaps to a small follow-up. All changes are committed and pushed.

# Summary of changes for run 596bd78d-6ccd-43b9-8709-d908f5071190
I addressed the reviewer's Zulip requests and expanded the contribution into a small, focused, well-motivated family of lemmas. All additions are machine-checked in `Main.lean` (compiles with no `sorry`/`admit`; the new lemmas depend only on standard axioms).

**Requested conditionally complete versions (the core of the new ask):**
- `ciSup₂_eq_ciSup_diagonal` — the diagonal collapse `(⨆ i, ⨆ j, f i j) = ⨆ k, f k k` over `ConditionallyCompleteLattice`, under a cofinality hypothesis plus a single `BddAbove` hypothesis on the diagonal (which, via cofinality, automatically bounds the whole family — no extra boundedness hypotheses needed).
- `ciSup₂_eq_ciSup_diagonal'` — the `ConditionallyCompleteLinearOrderBot` version, which drops the `Nonempty` hypothesis (empty index collapses to `⊥`), mirroring the `ciSup_mono` / `ciSup_mono'` pair the reviewer pointed to.

**More general form (the genuinely reusable core the reviewer hinted at):**
- `iSup_eq_iSup_of_forall_exists_le` with `@[to_dual]` (auto-generating `iInf_eq_iInf_of_forall_exists_le`): two suprema agree when the index families are mutually cofinal. This is `iSup_mono'` applied in both directions packaged as an equality; stated over the weakest class `CompleteSemilatticeSup`. A checked `example` derives the diagonal lemma from it (via `iSup_prod'`), showing the structural relationship; the diagonal lemma is kept stated directly so it still works for `ι : Sort*`.

**Verified callers and downstream exploration:**
- Confirmed the two genuine duplicate proofs this simplifies: `ENat.iSup_add_iSup` (`Data/ENat/Lattice.lean`) and `ENNReal.iSup_add_iSup` (`Data/ENNReal/Operations.lean`); checked replacement proofs are `enat_iSup_add_iSup_via_diagonal` / `ennreal_iSup_add_iSup_via_diagonal`.
- Searched Mathlib for further leads: multiplicative `iSup_mul_iSup` *equalities* do not exist (only `_le` halves), so there is no multiplicative duplicate to collapse. `lintegral`/measure results route through `ENNReal.iSup_add_iSup` and benefit transitively.
- Found a concrete new caller specifically enabled by the conditionally complete version: `Cardinal.ciSup_add_ciSup` / `ciSup_mul_ciSup` currently return an uncollapsed double supremum, and `Cardinal` is a `ConditionallyCompleteLinearOrderBot` (not a `CompleteLattice`). The diagonal version follows immediately — checked as `cardinal_ciSup_add_ciSup_via_diagonal` — giving direct evidence that the requested conditionally complete lemmas have real use.

**Documentation:** `PR_PLAN.md` lays out exactly what to add, what to change, suggested upstream placement (near `iSup_mono'`/`iSup₂_mono'` in `Order/CompleteLattice/Basic.lean` and near `ciSup_mono'` in `Order/ConditionallyCompleteLattice/Indexed.lean`), the verified-vs-ruled-out downstream leads, and a caution against over-abstracting (no new typeclass/framework), matching mathlib's preference for small discoverable lemmas with demonstrated callers.

All changes are committed and pushed.

# Summary of changes for run ff019c76-50d8-48b4-8afa-e9f550f22820
Created a concise, visual two-page A4 guide:

- `contribution-patterns.tex` — editable LaTeX source with TikZ diagrams and styled Lean snippets.
- `contribution-patterns.pdf` — compiled two-page PDF.

It illustrates the duplicated ENat/ENNReal proof pattern, extraction of `iSup₂_eq_iSup_diagonal`, the cofinal-diagonal idea, the Lean proof steps, before/after caller simplification, and an upstream-review checklist. The PDF compiles cleanly, and the existing Lean project still builds without `sorry` or `admit`.

# Summary of changes for run e3d50108-2f35-4ae9-b556-371bc6d728f2
Reviewed and corrected the proposed upstream change.

Key findings:
- The original generic proof had one extra `le_iSup_of_le` in its first inequality.
- Simply removing that extra application still does not work with `@[to_dual]`; the generated infimum proof retains a supremum-side projection.
- Replaced the proof with a dualization-safe `sSup_le`/`le_sSup` argument.
- Generalized the theorem from `CompleteLattice` to the weaker `CompleteSemilatticeSup` assumption.
- Moved its recommended location to the existing `CompleteSemilatticeSup` section and added a public docstring.
- Retained the concise ENat and ENNReal caller simplifications.

Deliverables:
- `UPSTREAM.patch`: complete corrected three-file patch.
- `UPSTREAM_REVIEW.md`: explanation of required changes, placement, generality, and checks.
- `RequestProject/Main.lean`: synchronized checked demonstration.

Verification completed:
- The patch applies cleanly to the matching mathlib checkout.
- All three affected mathlib modules build successfully.
- Style linting passes for all three modules.
- The generated supremum and infimum theorems have no axiomatic dependencies.
- No `sorry` or `admit` was introduced.

# Summary of changes for run 18a56eba-8537-4b03-9eee-23249a284006
Not exactly. There are two issues:

1. In the first inequality, the diagonal supremum has only one binder, so this term has one `le_iSup_of_le` too many:
   ```lean
   le_iSup_of_le k (le_iSup_of_le k le_rfl)
   ```
   It should be:
   ```lean
   le_iSup_of_le k le_rfl
   ```
   The nested form is correct in the second inequality because its target is the doubly indexed supremum.

2. Even after that correction, `@[to_dual]` fails with the stated `[CompleteLattice α]` proof because generated terms can retain the wrong `SupSet` projection when translated to `InfSet`.

I updated `RequestProject/Main.lean` with a working, slightly more general version using `[CompleteSemilatticeSup α]` and a `to_dual`-compatible proof via `sSup_le`/`le_sSup`. It successfully generates:

```lean
iInf₂_eq_iInf_diagonal
    (f : ι → ι → α)
    (h : ∀ i j, ∃ k, f k k ≤ f i j) :
    (⨅ i, ⨅ j, f i j) = ⨅ k, f k k
```

If you do not need `@[to_dual]`, your concise proof works after changing only the first branch to:

```lean
obtain ⟨k, hk⟩ := h i j
exact hk.trans (le_iSup_of_le k le_rfl)
```

The full project builds successfully, contains no `sorry` or `admit`, and both the supremum theorem and generated infimum theorem have no axiomatic dependencies.

# Summary of changes for run 2eae7e4c-7e36-49a9-802d-ac1ab3c7c44f
That’s mathlib’s PR template. Enter a short title in GitHub’s **Title** field, e.g.:

`Order: add diagonal cofinality lemma for indexed suprema`

Above `---`, write:

`Add iSup₂_eq_iSup_diagonal, a generic lemma identifying a doubly indexed supremum with a cofinal diagonal. Use it to simplify the duplicated proofs of ENat.iSup_add_iSup and ENNReal.iSup_add_iSup.`

Leave the template below `---` unchanged, then create the PR.

# Summary of changes for run ab80fe3d-fa1e-4e07-b0cf-284b1003713e
Fork mathlib, create a branch, and add `iSup₂_eq_iSup_diagonal` in the most appropriate order/lattice file. Replace the duplicated `ENat.iSup_add_iSup` and `ENNReal.iSup_add_iSup` proofs with the new lemma. Run `lake exe cache get`, build the affected files, and run linters. Commit, push, then open a PR explaining the duplicated pattern, the generic lemma, and the two simplified callers. Follow `CONTRIBUTING.md` and keep the PR focused.

# Summary of changes for run 81f601db-36e0-49e4-994a-8f04d6ef77da
Identified and formalized a reusable duplicated-proof opportunity for indexed suprema.

- Added the generic theorem `iSup₂_eq_iSup_diagonal`, stating that a doubly indexed supremum equals its diagonal supremum when the diagonal is cofinal.
- Demonstrated two concrete simplifications of existing mathlib proofs:
  - `ENat.iSup_add_iSup` from `Mathlib/Data/ENat/Lattice.lean`
  - `ENNReal.iSup_add_iSup` from `Mathlib/Data/ENNReal/Operations.lean`
- The generic result only assumes `CompleteLattice`; it introduces no addition-specific or extended-number-specific framework.
- Documented the candidate, original duplicated proof, replacement proofs, naming rationale, and suggested upstream location in `FINDINGS.md`.
- Added machine-checked implementations of the generic lemma and both simplified callers in `RequestProject/Main.lean`.

The project builds successfully, contains no `sorry` or `admit`, and the proofs use only accepted standard axioms.