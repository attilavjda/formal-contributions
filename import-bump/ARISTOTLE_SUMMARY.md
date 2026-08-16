# Summary of changes for run bf9b1800-ec7f-4c4e-a137-de0d0048e46e
## Import bump retested against online Mathlib master

I cloned `leanprover-community/mathlib4` **master** (commit `97b6a17d7e93a942ab7f7f777bb8fac2af129040`, 15 Aug 2026, toolchain v4.34.0-rc1), fetched the public olean cache, applied the move of `smul_eq_self_of_mem_zpowers` into the stabilizer file `Mathlib/GroupTheory/GroupAction/Basic.lean`, and re-ran the whole measurement and compile chain there. The checkout was restored afterwards and is byte-identical (`git status` empty).

**The claim still holds on master.**

| host file | closure on the pinned Mathlib | closure on master | modules added | downstream files that grow |
|---|---|---|---|---|
| `GroupTheory/GroupAction/Basic.lean` | 522 → 523 | 533 → 534 | **1** | 13 of 2850 dependants, +1 each |
| `GroupTheory/GroupAction/FixedPoints.lean` | 483 → 491 | 497 → 505 | **8** | 3 of 1719 dependants, ≤ +8 |

Only the absolute sizes and dependant counts have grown since the pinned revision; `LinearAlgebra.Alternating.DomCoprod` has dropped off the list of files that would grow.

**What was actually run** (logged in `contribution/master-import-bump.txt`):
* `lake env lean Mathlib/GroupTheory/GroupAction/Basic.lean` with the extra `public import` and the rerouted `@[to_additive]` lemma — exit 0, no errors or warnings; deleting the added import again makes the same file fail with `Unknown constant Subgroup.zpowers`, so exactly that one import is what the move needs;
* `lake env lean Mathlib/GroupTheory/OrderOfElement.lean` with the 13 lines removed — exit 0;
* **a whole-library `lake build` of patched master: `Build completed successfully (8724 jobs)`**, no error or warning in the log (~70 min on 8 cores);
* `contribution/check_import_bump.lean`: the pre-move multiplicative *and* additive statements typecheck against the moved lemma and the `@[to_additive]`-generated twin. The only change is binder order (`{α}` now precedes `{x y : G}`, since the host file has `G`, `α` as section variables); the two names occur in no other Mathlib file and are only applied positionally, and the full build confirms nothing breaks.

**New files:** `REPRODUCE-IMPORT-BUMP.md` — a step-by-step VS Code walkthrough (extension/toolchain setup, `lake exe cache get` before opening any Mathlib file, running the import-closure measurement, exactly where to type the two edits, the "Restart File" pitfall when an import block changes, why the language server reads imports from built oleans and not from your editor, per-file and whole-library checks, the statement check in the InfoView, restoring the checkout, and a troubleshooting list); `contribution/master-import-bump-stabilizer.patch` (+8 / −13 over two files); `contribution/master-import-bump.txt`; `contribution/check_import_bump.lean`. `CONTRIBUTION.md` gained a "Retest of the import bump against online Mathlib master" section and `scripts/README.md` an "Import costs" section.

Caveat kept from before: the move is not needed for the −12/+3 simplification itself (`OrderOfElement.lean` already imports everything required), so it buys placement only, at this small but nonzero import cost.

The Lean project itself is unchanged and still builds with no `sorry`. Everything is committed and pushed; `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run 5354d20c-2d3d-4cf9-87e5-0973f286060e
I re-measured the import cost of that placement claim, and it checks out on both counts.

**Numbers (measured against the Mathlib this project pins, commit `8f9d9cf`, toolchain v4.28.0):**

| host file | import closure now | extra import | closure after | modules added |
|---|---|---|---|---|
| `Mathlib/GroupTheory/GroupAction/Basic.lean` (stabilizer file) | 522 | `Mathlib.Algebra.Group.Subgroup.ZPowers.Basic` | 523 | **1** |
| `Mathlib/GroupTheory/GroupAction/FixedPoints.lean` | 483 | same | 491 | **8** |

Why the asymmetry: `ZPowers/Basic.lean` directly imports `Algebra.Divisibility.Basic`, `Algebra.Group.Subgroup.Map` and `Algebra.Group.Int.Defs`. The stabilizer file already imports `Subgroup.Map` (it needs `Subgroup` to state `MulAction.stabilizer`), so only `ZPowers/Basic` itself is new. `FixedPoints.lean` does not, so it additionally pulls in `Subsemigroup.Basic`, `Submonoid.Basic`, `Submonoid.Operations`, `Subgroup.Lattice`, `Subgroup.Map`, `Algebra.Group.Pi.Lemmas` and `Data.Set.Piecewise`.

**Downstream blast radius (not in the original claim):** 2500 modules import `GroupAction/Basic.lean` transitively, but 2486 already have `ZPowers/Basic` in their closure — only 14 grow, by exactly one module each (the `CategoryTheory/Galois` and `CategoryTheory/Action` files, `GroupAction.CardCommute`, `GroupAction.Quotient`, `GroupAction.SubMulAction.OfStabilizer`, `Perm.ClosureSwap`, `LinearAlgebra.Alternating.DomCoprod`). Through `FixedPoints.lean` fewer files are affected (195 dependants, 3 of which grow) but at up to 8 modules each.

**Compile checks actually run** (the Mathlib checkout was edited, compiled, then restored byte-identically — verified clean afterwards): the stabilizer file with the extra `public import` and the `@[to_additive]`-tagged lemma appended compiles with no errors or warnings; `OrderOfElement.lean` with the lemma, its hand-written twin `vadd_eq_self_of_mem_zmultiples` and the `attribute [to_additive existing]` line removed also compiles clean; and no other Mathlib file mentions either name, so nothing can break (and `OrderOfElement` imports `GroupAction/Basic` transitively regardless).

One caveat worth stating: the move is not needed for the −12/+3 simplification itself — `OrderOfElement.lean` already has everything required — so the move buys placement only, at this nonzero import cost.

**What I added to the project:** `scripts/import_closure.py`, a dependency-free tool that computes transitive import closures for any Lean 4 library (it understands the module-system `public`/`private`/`meta`/`import all` forms) and answers "what would this extra import cost?", with a `--downstream` mode that reports every module in the library whose own closure would grow and by how much. Raw measurement and compile logs are in `contribution/import-bump-stabilizer-file.txt`; the write-up is a new section of `CONTRIBUTION.md`, and `scripts/README.md` documents the tool. The Lean project still builds with no `sorry`; `ARISTOTLE_SUMMARY.md` was left untouched. All work is committed and pushed.

# Summary of changes for run fc34934f-f803-44ad-9b95-c2f55c76192c
## Another search, another tiny bridge contribution

I ran a **new** search against today's Mathlib master (`b5fdb9f8…`, 14 Aug 2026, toolchain v4.34.0-rc1, built from the public cache) and it found a category the earlier searches structurally could not see, plus a small, fully verified contribution ready to file.

**The blind spot.** The earlier scanner looks for additive declarations that carry *no* `to_additive` link. The complementary case is a pair that *is* linked — by `attribute [to_additive existing] …` or by `@[to_additive existing]` — but whose additive side is still written out and maintained by hand. Two new tools cover it:

* `scripts/scan_to_additive_existing.lean` — walks the environment's translation table and reports the pairs whose additive side is hand-written, using a property of `to_additive` itself: a declaration it generates gets a source position *inside* the declaration it came from. 168 candidates on master, in ~20 seconds (`contribution/master-scan-existing.txt`).
* `scripts/to_additive_existing.py` — the decider: it moves the attribute onto the multiplicative declaration as a plain `@[to_additive …]`, drops the name from the glue command (deleting it when empty), deletes the hand-written declaration, rebuilds, and requires that an appended `example : <the old statement> := @Ns.name` typechecks. The file is always restored; sites in one file are chained; `--patch` emits the composed diff. `scripts/to_additive_twins.py` gained the shared parsing this needed (named `instance`s, `alias`, and `set_option … in` lines).

**The contribution (−60 / +8, 7 files):** eight sites where `@[to_additive]` regenerates exactly the hand-written declaration — `Pi.single_induction`, `AddCommGrpCat.forget_preservesLimits`, `AddCommMonCat.forget_preservesLimits`, `negSucc_zsmul`, `SymAlg.sym_neg`, `SymAlg.unsym_neg`, `AddAction.stabilizerEquivStabilizer_compTriple`, `AddSubgroup.upperCentralSeries_one`. Patch `contribution/master-to_additive-existing.patch`, PR text `contribution/PR-to_additive-existing.md`; the self-contained single-file hunk (`Mathlib/GroupTheory/Nilpotent.lean`, −11 / +1) is also split out. Notable: `Pi.single_induction` exists only as a workaround for a naming issue that `to_additive` now handles itself, and the `Symmetrized` sites need `(attr := simp)` so the generated lemmas stay simp lemmas — checked, not assumed.

**Verification actually performed:** every site decided by the compiler as above; a full `lake build` of master with the patch applied succeeds (8721 jobs, no error, `contribution/master-patched-build-existing.txt`); and `RequestProject/MathlibContributionExisting.lean` re-derives four of the eight against the Mathlib this project pins, asserting `@generated = @Mathlib.name := rfl` (these elaborate only if the statements are literally identical). The project builds with no `sorry`, on standard axioms only.

**A second, lower-value batch:** 15 deprecated-`alias` pairs collapse to one `@[to_additive (attr := deprecated …)] alias` each (−86 / +15, `contribution/master-to_additive-existing-aliases.patch`); `(attr := deprecated …)` was checked to deprecate both sides. A full build with *both* patches applied also succeeds.

The remaining 160 candidates are documented with the reason each was rejected (17 rejected by the compiler — including the two known genuine translation gaps, which the new scanner rediscovers independently; 84 whose additive side is machine-generated by `mk_iff`/`irreducible_def`/`simps`; the rest other declaration forms). Everything is written up in `CONTRIBUTION.md`, section *Hand-maintained `to_additive existing` bridges*, and `scripts/README.md`; `ARISTOTLE_SUMMARY.md` was left untouched. All work is committed and pushed.

# Summary of changes for run 9e8a21df-9d5c-44c1-b7a4-7589d29e2c93
Mathlib/GroupTheory/GroupAction/Basic.lean — the stabilizer file. Checked: it needs only one extra import (Algebra/Group/Subgroup/ZPowers/Basic), which adds exactly 1 module to its import closure; with the import and the lemma appended, that file compiles clean, and OrderOfElement already imports it transitively, so no call site breaks. FixedPoints.lean also fits thematically but costs 8 new imports.

# Summary of changes for run ebfcaed9-6a06-4524-b5c1-a31ebf1b90ed
## What I did

I redid the "bridges" search against the **latest Mathlib** (`mathlib4` master, commit `5b8fb9a`, toolchain v4.34.0-rc1, built from the public cache), and produced one small, fully verified contribution plus a documented list of further opportunities. Everything new is written up in `CONTRIBUTION.md`, section *Bridges scope on current Mathlib master*, with logs and patches under `contribution/`.

**The tiny contribution (−12 / +3 lines, no API change).** In `Mathlib/GroupTheory/OrderOfElement.lean`, `smul_eq_self_of_mem_zpowers` is proved through `MulAction.toPermHom` (a hom into `Equiv.Perm α`), which `to_additive` cannot translate — so the additive version is written out by hand and attached with `attribute [to_additive existing]`. Routing the proof through the stabilizer subgroup (`zpowers y ≤ stabilizer G a`) makes it translatable, so a plain `@[to_additive]` generates the additive lemma itself. The hand-written twin, the glue line and a leftover porting workaround are all deleted. Verified: the patched file compiles warning-free; a **full `lake build` of master with the patch succeeded** (8716 jobs, no errors); and `RequestProject/MathlibContributionBridges.lean` proves, against unmodified Mathlib, that both the multiplicative and generated additive statements are literally the existing Mathlib ones. Patch: `contribution/master-smul_eq_self_of_mem_zpowers.patch`; ready-to-file PR text: `contribution/PR-smul_eq_self_of_mem_zpowers.md`.

**Refreshed library-wide scan.** I ported the environment scanner to master's new `Mathlib.Tactic.Translate` framework (`scripts/scan_to_additive_master.lean`) and fixed two blind spots in the source-level finder. On master it reports 412 candidates; 15 are confirmed by the compiler as hand-written twins that `@[to_additive]` regenerates, in 7 files (−41 / +16 lines), including one lemma introduced upstream only recently. A full master build with that patch applied on top also succeeded.

**Other findings.** The two lemmas of the earlier proposal have meanwhile been fixed upstream. I also documented the genuine translation gaps the compiler rejected — notably Cauchy's theorem, where the auxiliary definition `vectorsProdEqOne` blocks translation — plus the remaining `attribute [to_additive existing]` glue sites, why the categorical (`GrpCat`/`AddGrpCat`) pairs offer nothing mechanical to delete, and a new candidate generator `scripts/dual_gaps.py` for missing order duals (693 unverified `sSup`/`sInf`, `iSup`/`iInf` candidates, clearly marked as a place to look rather than results).

The project itself builds cleanly with no `sorry`; `ARISTOTLE_SUMMARY.md` was left untouched.


# Summary of changes for run 220a915d-0bd5-419e-a853-220c4a429ea8
Extended the search for hand-written `to_additive` twins in Mathlib, using and improving the scripts in `scripts/`.

**New tooling.** `scripts/scan_to_additive.lean` is an environment-level scanner (run with `lake env lean scripts/scan_to_additive.lean`, output in `contribution/scan-env.txt`). For every untagged, non-generated theorem it computes the name and statement that `to_additive` would generate and looks for a same-module hand-written theorem with that statement, up to reducible defeq. It produced 334 candidate pairs. `scripts/to_additive_twins.py` gained a `--scan` mode that turns those candidates into source edits, plus several correctness fixes to declaration-span detection (multi-line docstrings/attribute blocks, indented bodies), stricter name resolution, a refusal to delete over-wide spans, and inline/multi-line attribute merging with a 100-column rule.

**Results.** Of the 334 candidates, 31 resolve to hand-written source declarations; the compiler accepts 16 of them (`contribution/verify-env.txt`) — the 4 lemmas of the original proposal plus **12 new twins**: `Finset.expect_neg_index`, `translate_sum_right`, `AddAction.toPerm_zero`, `AddMonoidAlgebra.fg_of_finiteType`, `AddMonoidAlgebra.finiteType_iff_group_fg`, and the seven congruence lemmas of `Mathlib/Tactic/LinearCombination'.lean` (`pf_add_c`, `c_add_pf`, `add_pf`, `pf_sub_c`, `c_sub_pf`, `sub_pf`, `neg_pf`). The generated patch `contribution/to_additive-env-generated.patch` (−45/+17 lines over 7 files) applies cleanly; with it applied, a build of the patched modules and their dependants succeeded (1521 jobs, `contribution/patched-build.txt`) and ten further files mentioning the deleted names compile (`contribution/downstream-check.txt`). The Mathlib checkout was restored afterwards and is byte-identical to the pinned revision. The 15 rejections and their compiler-reported reasons are recorded in `CONTRIBUTION.md`.

**Independent Lean evidence.** `RequestProject/MathlibContributionEnv.lean` re-checks ten of the new twins without the scripts: each multiplicative lemma is copied verbatim, tagged `@[to_additive]`, and the generated declaration is asserted equal to the Mathlib one by `rfl` (which only typechecks if the types are literally the same). It builds with no `sorry` (`lake build RequestProject.MathlibContributionEnv`), as does the whole project.

`CONTRIBUTION.md` and `scripts/README.md` were updated to describe the two-tool workflow, the results table and the limitations. Everything is committed and pushed.

# Summary of changes for run 7c41ebd0-3957-43d5-93bc-aa4ecbcc0b0f
I factored the "additive" (new-code) half of the earlier contribution — the twin scan plus the delete-rebuild-compare loop — out into a single, dependency-free, reusable module: `scripts/to_additive_twins.py`, documented in `scripts/README.md`.

**What it does.** It targets one pattern in formal-maths libraries: a hand-written `to_additive` twin, i.e. an additive lemma whose entire proof is a call to its multiplicative partner through `Multiplicative`, which a `@[to_additive]` tag would generate for free.

- `find PATH...` — scans any mix of `.lean` files/directories for such pairs (only when the partner is in the same file, so the fix is a self-contained diff).
- `verify PATH... [--twin NAME] [--patch out.patch]` — decides each candidate with the compiler rather than with regexes: compile the file unchanged and record the twin's pretty-printed type; rewrite it (`@[to_additive]` onto the partner, merged into any existing attribute list since Lean forbids stacked `@[...]`, explicit target name added only if the naming heuristic needs it; twin deleted with its docstring and attributes); compile again, requiring both that the file builds and that the *old* statement still typechecks against the new declaration via an appended `example : <old type> := @Ns.name`; then restore the file — always, including on failure. Multiple twins in one file are chained, and `--patch` emits a unified diff with paths relative to the innermost lake package, ready for `git apply`.

It is usable as a library too: `find_twins(paths)` and `verify_twin(twin)`. Works on any `lake`-managed Lean 4 project, including a dependency under `.lake/packages`. `deletion_scout.py scan-twins` now delegates to it instead of keeping its own copy of the heuristic.

**Exercised end to end on the Mathlib pinned by this project.** `find` over all of Mathlib returns 7 candidates in seconds; `verify` settles them in about two minutes: 4 PASS (`Finset.sum_Ico_reflect`, `Finset.sum_range_reflect`, `Finset.Nat.sum_antidiagonal_succ`, `Finset.Nat.sum_antidiagonal_succ'`) and 3 FAIL, rejected by the compiler because there the hand-written twin is the multiplicative one, a direction `to_additive` does not generate. So the tool re-derives the previous contribution unaided; the generated diff is `contribution/to_additive-twins-generated.patch` (checked to apply cleanly with `git apply`), the full log is `contribution/verify-twins.txt`, and the tool additionally reports the section variable `N` becoming unused. The Mathlib checkout was left byte-identical after every run.

`CONTRIBUTION.md` gained a short section pointing at the module; `ARISTOTLE_SUMMARY.md` was left untouched. The Lean side is unchanged and still builds with no `sorry`. Everything is committed and pushed.

# Summary of changes for run 8cf316bd-2369-4c77-94bf-fe72ff2a9e6a
## One tiny, pure-deletion Mathlib contribution in the scope of Exercises 1.1–1.19

I read the uploaded exercise sheet (`kalkulus_gyakorlo.pdf`, sheet 1: sets, bounds/suprema, |x|, inequalities, induction sums, geometric sum, factorials, binomial identities), mapped those exercises onto the Mathlib files that host them, and searched there for changes whose diff only *removes* things. Everything is on the Mathlib version pinned by this project (toolchain 4.28.0).

**The contribution** (in `CONTRIBUTION.md`, patch in `contribution/to_additive-reflect.patch`):

In `Mathlib/Algebra/BigOperators/Intervals.lean`, `prod_Ico_reflect` and `prod_range_reflect` are not tagged `@[to_additive]`; instead their additive versions are written out by hand and proved by transporting through `Multiplicative`. Tagging the multiplicative lemmas and deleting the two hand-written ones removes 8 lines and adds 2, with no API change. This is squarely in the exercise scope: `Finset.sum_range_reflect` is the lemma used two declarations further down in the same file to prove Gauss' summation formula `Finset.sum_range_id_mul_two` (Exercise 1.14 a), and `Finset.sum_Ico_reflect` is used in `Nat.sum_range_choose_halfway` in the binomial-coefficient file (Exercise 1.19).

Verification actually performed (not argued):
* `RequestProject/MathlibContribution.lean` re-derives both lemmas with `@[to_additive]` and proves `@sum_Ico_reflect' = @Finset.sum_Ico_reflect` and `@sum_range_reflect' = @Finset.sum_range_reflect` by `rfl` — these only typecheck if the generated statements are literally the current ones. The file builds against unmodified Mathlib, with no `sorry`.
* The patched file and all 7 call sites of the two lemmas were rebuilt successfully.

The same anomaly appears in `Mathlib/Algebra/BigOperators/NatAntidiagonal.lean` (`sum_antidiagonal_succ`, `sum_antidiagonal_succ'`), where the neighbouring lemmas already use `@[to_additive]`; deleting them also makes the section variables `N`/`[AddCommMonoid N]` dead. That hunk is verified the same way and is included in the patch (total: −17/+5 lines). It can be shipped as one small PR or split.

**The reusable artifact**: `scripts/deletion_scout.py`, a single-file, dependency-free tool for any `lake`-managed Lean 4 library, with `scan-twins` (hand-written to_additive twins), `scan-dupes` (identical statements), `scan-hyps` (hypotheses used nowhere), `verify` (delete a line range, rebuild, restore, report) and `prune-simp` (drop each `simp` argument in turn and rebuild). The scans only propose; `verify`/`prune-simp` decide by really editing and calling `lake env lean`, always restoring the file. All five sub-commands were exercised here; `scan-twins` output on this tree is saved in `contribution/scan-twins.txt` (11 candidates, 4 of them in exercise scope — the ones the patch handles).

`CONTRIBUTION.md` also records candidates that looked free and were rejected after checking, notably an "unused import" suggestion in the Dirichlet-approximation file (Exercise 1.10) that turns out to break the build, plus negative results for redundant `simp` arguments, no-op tactics and dead hypotheses in the exercise-scope files, and duplicate-lemma pairs near the absolute-value exercises that are deprecation-cycle refactors rather than tiny deletions.
