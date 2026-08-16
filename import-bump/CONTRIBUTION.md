# One tiny, pure-deletion Mathlib contribution around Exercises 1.1–1.19

Source of the exercises: `kalkulus_gyakorlo.pdf`, sheet 1 (sets, bounds/suprema, `|x|`,
inequalities, induction sums, geometric sum, factorials, binomial identities).

The search was restricted to the Mathlib files those exercises actually live in
(`Mathlib/Algebra/BigOperators/…`, `Mathlib/Data/Nat/Choose/…`,
`Mathlib/Data/Nat/Factorial/…`, `…/GeomSum.lean`, `Mathlib/NumberTheory/Real/Irrational.lean`,
`Mathlib/NumberTheory/DiophantineApproximation/…`, `Mathlib/Order/Bounds/…`,
`Mathlib/Algebra/Order/AbsoluteValue/…`), and to changes whose diff only *removes*
things, with no loss of API.

Mathlib version: the tree pinned by this project (`lean-toolchain` = 4.28.0,
`lake-manifest.json`), i.e. the version available on 9 Aug 2026.

---

## The contribution

**Delete the two hand-written additive twins of the `Finset` reflection lemmas and
generate them with `@[to_additive]` instead** — in
`Mathlib/Algebra/BigOperators/Intervals.lean`.

Current state of that file: `prod_Ico_reflect` and `prod_range_reflect` are *not*
tagged `@[to_additive]`; instead their additive versions are written out by hand and
proved by transporting through `Multiplicative`:

```lean
theorem sum_Ico_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ n + 1) : (∑ j ∈ Ico k m, f (n - j)) = ∑ j ∈ Ico (n + 1 - m) (n + 1 - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h

theorem sum_range_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (n : ℕ) :
    (∑ j ∈ range n, f (n - 1 - j)) = ∑ j ∈ range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n
```

This is duplication that `to_additive` is designed to remove: the surrounding file
already uses `@[to_additive]` everywhere else (`prod_Ico_eq_prod_range`,
`prod_range_diag_flip`, …). The patch tags the two multiplicative lemmas and deletes
the two hand-written ones.

**Diff:** `contribution/to_additive-reflect.patch` — 8 lines removed, 2 added in
`Intervals.lean`.

**Why this is safe (checked, not argued):** `@[to_additive]` generates exactly the
names `Finset.sum_Ico_reflect` and `Finset.sum_range_reflect`, with byte-identical
statements and identical explicit/implicit binder structure, so no call site changes:

```
@Finset.sum_range_reflect : ∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ → M) (n : ℕ),
  ∑ j ∈ Finset.range n, f (n - 1 - j) = ∑ j ∈ Finset.range n, f j
@Finset.sum_Ico_reflect : ∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ → M) (k : ℕ) {m n : ℕ},
  m ≤ n + 1 → ∑ j ∈ Finset.Ico k m, f (n - j) = ∑ j ∈ Finset.Ico (n + 1 - m) (n + 1 - k), f j
```

This is machine-checked in `RequestProject/MathlibContribution.lean`: it re-derives the
two lemmas with `@[to_additive]` and states

```lean
theorem sum_Ico_reflect_statements_agree   : @sum_Ico_reflect'   = @Finset.sum_Ico_reflect   := rfl
theorem sum_range_reflect_statements_agree : @sum_range_reflect' = @Finset.sum_range_reflect := rfl
```

which only typechecks if the generated statement is *the same proposition* as the one
currently in Mathlib. That file builds against unmodified Mathlib.

In addition, the patched `Intervals.lean` and every one of the 7 call sites of the two
lemmas were rebuilt successfully:
`Mathlib.Data.Nat.Choose.Sum`, `Mathlib.Algebra.Ring.GeomSum`,
`Mathlib.NumberTheory.BernoulliPolynomials`, `Mathlib.Topology.EMetricSpace.BoundedVariation`,
`Mathlib.Combinatorics.SetFamily.AhlswedeZhang`,
`Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule`.

**Why it is on-topic for Exercises 1.1–1.19.** `Finset.sum_range_reflect` is the lemma
used two declarations further down in the very same file to prove Gauss' summation
formula `Finset.sum_range_id_mul_two` (`(∑ i ∈ range n, i) * 2 = n * (n - 1)`), i.e.
Exercise 1.14 a; and `Finset.sum_Ico_reflect` is used in `Nat.sum_range_choose_halfway`
in `Mathlib/Data/Nat/Choose/Sum.lean`, the binomial-coefficient file of Exercise 1.19.

### Same pattern, same directory (optional second hunk)

The scan (below) found the identical anomaly in `Mathlib/Algebra/BigOperators/NatAntidiagonal.lean`
— `sum_antidiagonal_succ` / `sum_antidiagonal_succ'` are hand-written twins of
`prod_antidiagonal_succ` / `prod_antidiagonal_succ'`, while the *neighbouring* lemmas in
that file (`prod_antidiagonal_swap`, `prod_antidiagonal_subst`, …) already use
`@[to_additive]`. Deleting them also makes the section variables `N` and
`[AddCommMonoid N]` dead, so the `variable` line shrinks too: 9 lines removed, 3 added.
Generated statements were checked to be identical, and the call sites
(`Mathlib.Data.Nat.Choose.Sum`, `Mathlib.NumberTheory.Bernoulli`) rebuild.

Both hunks are in the same patch file; they can be shipped as one small PR
("generate the additive `Finset` big-operator lemmas with `to_additive`") or split.

Net effect of the patch: **−17 lines, +5 lines**, no declaration removed from the API,
no proof made harder, and two more lemma pairs now linked by `to_additive` so they
cannot drift apart.

---

## The reusable artifact

`scripts/deletion_scout.py` — a single-file, dependency-free tool for finding *and
verifying* pure-deletion opportunities in any `lake`-managed Lean 4 library.

```
scan-twins  PATH...   declarations whose entire proof transports their partner through
                      `Multiplicative`/`Additive` -> candidates for `@[to_additive]`
scan-dupes  PATH...   declarations with a syntactically identical statement
scan-hyps   PATH...   named hypotheses that occur nowhere else in their declaration
verify      FILE      delete a line range (--drop A-B), optionally append a check
                      snippet (--check "..."), rebuild with `lake env lean`, restore
prune-simp  FILE      drop each `simp [...]` argument in turn, rebuild, report the
                      ones that were not needed
```

The scans are heuristics and are *only* used to propose a deletion; `verify` and
`prune-simp` do the deciding by actually editing the file, calling
`lake env lean`, and restoring the original afterwards.

Reproducing this contribution:

```bash
python3 scripts/deletion_scout.py scan-twins .lake/packages/mathlib/Mathlib
# ... 11 candidates, including:
#   Mathlib/Algebra/BigOperators/Intervals.lean:151: sum_Ico_reflect is a hand-written
#     twin of prod_Ico_reflect (via Multiplicative) -- try `@[to_additive]` on prod_Ico_reflect
#   Mathlib/Algebra/BigOperators/Intervals.lean:163: sum_range_reflect ...
#   Mathlib/Algebra/BigOperators/NatAntidiagonal.lean:30: sum_antidiagonal_succ ...
#   Mathlib/Algebra/BigOperators/NatAntidiagonal.lean:45: sum_antidiagonal_succ' ...
```

The full list of 11 candidates the scan produced on this Mathlib tree is in
`contribution/scan-twins.txt`; the four above are the ones inside the exercise scope,
and they are the ones this patch handles.

---

## Candidates that were checked and rejected

Recorded because they are the kind of thing that looks like a free win and is not:

* **Unused import.** `lake exe shake` claims `Mathlib.RingTheory.Int.Basic` is unused by
  `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` (Exercise 1.10, Dirichlet
  approximation). Deleting it and recompiling gives
  `unknown identifier 'isCoprime_iff_nat_coprime.mpr'` at line 540 — shake missed a use
  inside a tactic block. Every other shake suggestion in the exercise-scope files came
  with an `add` line, so none of them is a pure deletion.
* **Redundant `simp` arguments / no-op tactic steps.** Brute-forced away every argument
  of every `simp`-style call in `Mathlib/Data/Nat/Choose/Sum.lean` (16 calls) with
  `prune-simp`: none is redundant. `linter.unusedTactic` also reports nothing on the
  Choose/Factorial/Intervals/Irrational/DiophantineApproximation files.
* **Dead hypotheses.** The `unusedArguments` linter is a default `env_linter` and runs in
  Mathlib CI, and `scripts/nolints.json` contains no `unusedArguments` entries, so there
  is nothing to harvest here in the exercise scope. Textual candidates
  (e.g. `Nat.choose_lt_descFactorial`, `Irrational.mul_intCast`,
  `Set.nonempty_Ico_sdiff`) all turned out to be picked up by `simpa`/`rwa`/`simp [*]`.
* **Duplicate lemmas.** `scan-dupes` does find real duplication near the exercises —
  e.g. `AbsoluteValue.map_neg`/`IsAbsoluteValue.abv_neg`,
  `AbsoluteValue.sub_le`/`IsAbsoluteValue.abv_sub_le` (Exercises 1.11–1.13),
  `Ne.lt_or_gt`/`lt_or_gt_of_ne` — but each removal touches many call sites and is a
  deprecation-cycle refactor, not a tiny deletion.

---

## Reproducing / re-verifying

```bash
# 1. the statement-agreement check (builds against unmodified Mathlib)
lake build RequestProject.MathlibContribution

# 2. apply the patch to the Mathlib checkout and rebuild the two files + all call sites
git -C .lake/packages/mathlib apply "$PWD/contribution/to_additive-reflect.patch"
lake build mathlib/Mathlib.Algebra.BigOperators.Intervals \
           mathlib/Mathlib.Algebra.BigOperators.NatAntidiagonal \
           mathlib/Mathlib.Data.Nat.Choose.Sum mathlib/Mathlib.Algebra.Ring.GeomSum \
           mathlib/Mathlib.NumberTheory.Bernoulli mathlib/Mathlib.NumberTheory.BernoulliPolynomials \
           mathlib/Mathlib.Topology.EMetricSpace.BoundedVariation \
           mathlib/Mathlib.Combinatorics.SetFamily.AhlswedeZhang \
           mathlib/Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
git -C .lake/packages/mathlib checkout Mathlib/Algebra/BigOperators   # undo
```

All of the above was run on this tree and completed without errors.

---

## Follow-up: the finder/verifier, factored out as a reusable module

The parts of this work that were *additions* rather than deletions — the twin scan and the
"delete it, rebuild, compare the statement" loop — now live on their own in
`scripts/to_additive_twins.py` (see `scripts/README.md`). It is a single dependency-free
file, usable as a script or imported as a module, and works on any `lake`-managed Lean 4
project:

```bash
scripts/to_additive_twins.py find   .lake/packages/mathlib/Mathlib
scripts/to_additive_twins.py verify .lake/packages/mathlib/Mathlib/Algebra/BigOperators \
    --patch contribution/to_additive-twins-generated.patch
```

Run on the Mathlib pinned here it re-derives this contribution without human input: 7
candidates found, 4 verified (the two `*_reflect` and the two `*_antidiagonal_succ`
lemmas), 3 rejected by the compiler because there the hand-written twin is the
multiplicative one, a direction `to_additive` cannot generate. The generated diff is
`contribution/to_additive-twins-generated.patch` (identical in effect to the hand-written
`to_additive-reflect.patch`, minus the two now-dead `variable` binders, which the tool
only reports); the log is `contribution/verify-twins.txt`.

`deletion_scout.py scan-twins` now delegates to the new module instead of keeping its own
copy of the heuristic.

---

## Follow-up: twelve more `to_additive` twins, found by asking `to_additive`

The text-level scan above only recognises one shape of twin: an additive lemma whose whole
proof transports its multiplicative partner through `Multiplicative`. That is a symptom,
not the pattern. The pattern is *the statement*: a hand-written declaration whose type is
what `@[to_additive]` would have produced from its partner, however it happens to be
proved.

`scripts/scan_to_additive.lean` (new) checks exactly that, for the whole environment, by
calling the attribute's own machinery: `GuessName.guessName` for the name `to_additive`
would generate, and `applyReplacementForall` for the statement. Where a hand-written
theorem of the same module already has that statement, it prints a candidate; the existing
`scripts/to_additive_twins.py --scan` then decides each one by really tagging the partner,
really deleting the twin, rebuilding the file and checking that the old statement survives.

On the Mathlib pinned here (toolchain 4.28.0): 334 candidates, 31 of them hand-written
theorems that exist as source text (the rest are compiler-generated declarations such as
`mk.injEq` or `brecOn`), **16 verified**, in seven files — the four lemmas of the
contribution above, and twelve new ones:

* `Mathlib/Algebra/BigOperators/Expect.lean` — `Finset.expect_neg_index`
  (partner `expect_inv_index`, proved by `expect_image neg_injective.injOn`).
* `Mathlib/Algebra/Group/Translate.lean` — `translate_sum_right`
  (partner `translate_prod_right`, proved by `by ext; simp`).
* `Mathlib/Algebra/Group/Action/End.lean` — `AddAction.toPerm_zero`
  (partner `MulAction.toPerm_one`, proved by `aesop`).
* `Mathlib/RingTheory/FiniteType.lean` — `AddMonoidAlgebra.fg_of_finiteType` and
  `AddMonoidAlgebra.finiteType_iff_group_fg`; the latter needs the explicit form
  `@[to_additive finiteType_iff_group_fg]`, which the tool discovers by trying the bare
  tag first.
* `Mathlib/Tactic/LinearCombination'.lean` — the seven congruence lemmas `pf_add_c`,
  `c_add_pf`, `add_pf`, `pf_sub_c`, `c_sub_pf`, `sub_pf`, `neg_pf`, each of which is the
  `to_additive` translation of the `Mul`/`Div`/`Inv` lemma a few lines below it.

Diff: `contribution/to_additive-env-generated.patch` (−45/+17 lines, applies with
`git apply`); log: `contribution/verify-env.txt`; scan output: `contribution/scan-env.txt`.
As before the tool notes that the section variable `N` in `NatAntidiagonal.lean` becomes
unused; that removal is not part of the generated diff.

Verification actually performed on this tree, beyond the per-file rebuild that the tool
does for every candidate:

* the patch applies cleanly to the pinned Mathlib checkout (`git apply`);
* with it applied, `lake build` of the seven patched modules succeeded — 1521 jobs, i.e.
  the patched files together with everything in their dependency closures that depends on
  them (`contribution/patched-build.txt`);
* every other Mathlib file mentioning one of the deleted names compiles against the
  patched modules: `Algebra/Ring/GeomSum`, `Combinatorics/SetFamily/AhlswedeZhang`,
  `Data/Nat/Choose/Sum`, `GroupTheory/GroupAction/SubMulAction/Combination`,
  `MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule`, `NumberTheory/Bernoulli`,
  `NumberTheory/BernoulliPolynomials`, `Tactic/LinearCombination`, `Tactic/Ring/Common`,
  `Topology/EMetricSpace/BoundedVariation` (`contribution/downstream-check.txt`);
* the Mathlib checkout was restored afterwards and is byte-identical to the pinned
  revision.

The 15 rejections are informative rather than embarrassing, and all come from the
compiler: `Mathlib/Data/Set/Insert.lean` (and the three `Batteries` twins) does not import
`to_additive` at all, so the fix would mean adding an import rather than deleting lines;
`AddSubmonoid.mem_closure_singleton`, `AddSubmonoid.closure_singleton_zero`,
`AddCommGroup.finite_of_fg_torsion`, `AddAction.stabilizerEquivStabilizer_symm`,
`AddMonoidAlgebra.finiteType_iff_fg` and the three `GrpCat`/`CommGrpCat` lemmas make
`to_additive` fail to build the translated proof; deleting `AddGroup.fg_def` breaks a
`⊤.FG` dot-notation elsewhere in `GroupTheory/Finiteness.lean`; and the two
`ArithmeticFunction` Möbius twins are the *multiplicative* ones, obtained via `Additive`,
which is not a direction `to_additive` generates.

An independent, self-contained double check of ten of these twins lives in
`RequestProject/MathlibContributionEnv.lean` (the analogue of
`RequestProject/MathlibContribution.lean` for the follow-up batch): it copies the
multiplicative lemma verbatim, tags it `@[to_additive]`, and states
`@Generated = @Mathlib.Name := rfl`, which only typechecks if the generated declaration
has literally the type of the hand-written Mathlib one. It covers
`Finset.expect_neg_index`, `translate_sum_right`, `AddAction.toPerm_zero` and the seven
`Mathlib.Tactic.LinearCombination'` congruence lemmas, and compiles with no `sorry`.

# Bridges scope on current Mathlib master

Everything above was done against the Mathlib this project pins (`v4.28.0`). This section
redoes the search on the **latest Mathlib**: `leanprover-community/mathlib4` at
`5b8fb9a61c99c703b9946122c1dc5f36272c0e01`, toolchain `leanprover/lean4:v4.34.0-rc1`,
built from the public cache. "Bridges" here means the connecting tissue between the
multiplicative and additive (and, on master, dual) halves of the library: `@[to_additive]`
links, hand-maintained twins, and the `attribute [to_additive existing]` glue that joins a
lemma to a twin written out by hand.

## Porting the tooling

Two changes were needed, both now in `scripts/`:

* `scripts/scan_to_additive_master.lean` — the environment-level scanner for master's
  `Mathlib.Tactic.Translate` framework. The naming dictionary moved out of
  `TranslateData` into an environment extension (`TranslateData.guessNameExt`), so the
  name `to_additive` *would* generate is now `GuessName.guessName (d.guessNameExt.getState
  env) s`. `scripts/scan_to_additive.lean` is unchanged and still targets the pinned
  version.
* `scripts/to_additive_twins.py` — the source-level finder now understands
  `theorem _root_.foo` (a declaration escaping the surrounding `namespace`) and refers to
  partners by any suffix of their name. Without this it missed, for instance, the
  hand-written twin of Cauchy's theorem.

## What has changed upstream since the pinned version

`Finset.sum_Ico_reflect` and `Finset.sum_range_reflect`, the two lemmas of the original
proposal, no longer exist on master: `Finset.prod_Ico_reflect` and
`Finset.prod_range_reflect` are now tagged `@[to_additive]` and the hand-written twins are
gone — the change proposed here has meanwhile been made upstream. The remaining pairs
found earlier are still open (some have moved: `AddAction.toPerm_zero` now lives in
`Mathlib/Algebra/Group/Action/End.lean`, and `Mathlib/Tactic/LinearCombination'.lean` is
now `Mathlib/Tactic/LinearCombinationPrime.lean`).

## The tiny contribution: repairing one broken bridge (−12/+3)

`Mathlib/GroupTheory/OrderOfElement.lean` maintains one bridge by hand:

```lean
theorem smul_eq_self_of_mem_zpowers ... := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAction.toPerm_apply, ← MulAction.toPermHom_apply, map_zpow _ y k,
    MulAction.toPermHom_apply]
  exact Function.IsFixedPt.perm_zpow (by exact hs) k -- Porting note: help elab'n with `by exact`

theorem vadd_eq_self_of_mem_zmultiples ... :=
  @smul_eq_self_of_mem_zpowers (Multiplicative G) _ _ _ α _ hx a hs

attribute [to_additive existing] smul_eq_self_of_mem_zpowers
```

`@[to_additive]` cannot translate the multiplicative proof — it goes through
`MulAction.toPermHom`, a `MonoidHom` into `Equiv.Perm α`, which stays multiplicative on the
additive side, and the attribute fails with *"the translated value is not type correct"*
(`contribution/master-verify-twins.txt`). Hence the hand-written twin and the
`to_additive existing` line.

Routing the proof through the stabilizer subgroup removes the obstruction — `x` lies in
`Subgroup.zpowers y ≤ MulAction.stabilizer G a` — and the whole block collapses to

```lean
@[to_additive]
theorem smul_eq_self_of_mem_zpowers {α : Type*} [MulAction G α] (hx : x ∈ Subgroup.zpowers y)
    {a : α} (hs : y • a = a) : x • a = a :=
  MulAction.mem_stabilizer_iff.1 <| Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hs) hx
```

The diff (`contribution/master-smul_eq_self_of_mem_zpowers.patch`) deletes 12 lines and
adds 3: the hand-written additive twin, the `attribute [to_additive existing]` glue line
and a Porting-note workaround all go away, and no name, statement or attribute changes.
`to_additive` even names the generated lemma `vadd_eq_self_of_mem_zmultiples` by itself,
as its own linter points out.

Verification actually performed:

* the patched `Mathlib/GroupTheory/OrderOfElement.lean` compiles with no warning;
* a **full `lake build` of master with the patch applied succeeded** (8716 jobs, no error;
  `contribution/master-patched-build.txt`), so nothing downstream depended on the deleted
  form;
* `RequestProject/MathlibContributionBridges.lean` re-derives the lemma in this project
  and states `@smul_eq_self_of_mem_zpowers' = @smul_eq_self_of_mem_zpowers := rfl` and
  `@vadd_eq_self_of_mem_zmultiples' = @vadd_eq_self_of_mem_zmultiples := rfl`; those only
  typecheck if the two statements are literally the Mathlib ones. It builds with no
  `sorry`.

## The refreshed twin scan on master (−41/+16)

`scan_to_additive_master.lean` reports **412 candidates** on master
(`contribution/master-scan-env.txt`); 30 of them are hand-written `theorem`/`lemma`s that
the Python decider can locate in the source, and it settles them by really tagging,
really deleting and rebuilding: **15 PASS**, in seven files
(`contribution/master-verify-env.txt`, patch
`contribution/master-to_additive-env-generated.patch`, −41/+16 lines; a full `lake build`
of master with this patch *and* the bridge repair above applied succeeded as well, 8716
jobs, `contribution/master-patched-build.txt`):

| file | twins that `@[to_additive]` regenerates |
| --- | --- |
| `Mathlib/Algebra/BigOperators/Expect.lean` | `Finset.expect_neg_index` |
| `Mathlib/Algebra/BigOperators/NatAntidiagonal.lean` | `Finset.Nat.sum_antidiagonal_succ`, `…_succ'` |
| `Mathlib/Algebra/Group/Action/End.lean` | `AddAction.toPerm_zero` |
| `Mathlib/Algebra/Group/Translate.lean` | `translate_sum_right` |
| `Mathlib/NumberTheory/Height/NumberField.lean` | `NumberField.sum_nonarchAbsVal_eq` |
| `Mathlib/RingTheory/FiniteType.lean` | `AddMonoidAlgebra.fg_of_finiteType`, `AddMonoidAlgebra.finiteType_iff_group_fg` |
| `Mathlib/Tactic/LinearCombinationPrime.lean` | `pf_add_c`, `c_add_pf`, `add_pf`, `pf_sub_c`, `c_sub_pf`, `sub_pf`, `neg_pf` |

`NumberField.sum_nonarchAbsVal_eq` is new: it was added upstream after the version this
project pins, i.e. the pattern is still being introduced. Deleting the twins in
`NatAntidiagonal.lean` also leaves the section variables `N`/`[AddCommMonoid N]` unused.

## Genuine `to_additive` gaps found (reported, not fixed)

These are the interesting failures — places where a bridge is missing because the
attribute cannot cross it:

* **Cauchy's theorem**, `exists_prime_orderOf_dvd_card` in
  `Mathlib/GroupTheory/Perm/Cycle/Type.lean`: the additive version is written out by hand
  and glued on with `attribute [to_additive existing]`. Tagging fails because the proof
  uses the auxiliary definition `vectorsProdEqOne`, which has no additive counterpart
  (`contribution/master-verify-cauchy.txt`). Making that definition translatable would
  close the gap.
* **`AddGroup.fg_def`** (`Mathlib/GroupTheory/Finiteness.lean`): deleting the twin breaks a
  `⊤.FG` dot-notation elsewhere in the same file.
* The two **Möbius inversion** lemmas in
  `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean` are hand-written in the
  *multiplicative* direction, transported through `Additive` — a direction `to_additive`
  does not generate at all.
* `AddMonoidAlgebra.finiteType_iff_fg`, `AddMonoidAlgebra.comulAlgHom_comp_mapRingHom`,
  `AddMonoidAlgebra.counitAlgHom_comp_mapRingHom` and `NumberField.sum_archAbsVal_eq`:
  the attribute fails to build the translated proof.

## Where the remaining bridge work is

* **`attribute [to_additive existing]` sites.** Master has 186 mentions of
  `to_additive existing`, 37 of them standalone `attribute [to_additive existing] …` lines.
  Each is a bridge maintained by hand; the `smul_eq_self_of_mem_zpowers` fix above is one
  of them, and the decider in `scripts/to_additive_twins.py` settles such a site
  mechanically (tag, delete, rebuild, compare statements).
* **Categorical bridges.** The scan does report `GrpCat`/`AddGrpCat`,
  `CommMonCat`/`AddCommMonCat` pairs, but there they are *generated* declarations
  (`mk.injEq`, `ext_iff`, `Hom.ext`, …), so there is nothing to delete; the duplication in
  the concrete↔categorical layer is not of this mechanical kind.
* **Order duals.** `scripts/dual_gaps.py` is a new, dependency-free candidate generator for
  the "an `sSup` lemma with no `sInf` dual" pattern: it swaps dual tokens in every
  declaration name and reports the ones whose counterpart is nowhere in the library.
  On master, restricted to `sSup`/`sInf` and `iSup`/`iInf` and to files that otherwise keep
  both sides in step, it lists 693 names (`contribution/master-dual-gaps.txt`). This list
  is *unverified* — many duals are genuinely absent because they are false or say
  something different (`TopologicalSpace.Opens.mem_sInf` is not the dual of `mem_sSup`) —
  it is a place to look, not a set of results. Note that master now also has a `to_dual`
  attribute in the same `Mathlib.Tactic.Translate` framework, so the same
  scan-tag-delete-rebuild loop applies verbatim to order duals.

## Reproducing

```bash
git clone https://github.com/leanprover-community/mathlib4 && cd mathlib4
lake exe cache get && lake build

lake env lean ../scripts/scan_to_additive_master.lean > scan.txt      # ~7 min, 412 candidates
../scripts/to_additive_twins.py verify . --scan scan.txt --patch twins.patch
../scripts/dual_gaps.py Mathlib --pairs sSup:sInf,iSup:iInf --same-file
```

# Hand-maintained `to_additive existing` bridges (a second search on master)

This section is a *new* search, run against `leanprover-community/mathlib4` master at
`b5fdb9f818dc16a94e3da48fc72191a504ffa114` (14 August 2026, toolchain
`leanprover/lean4:v4.34.0-rc1`), built from the public cache.

## The blind spot it closes

The scanner of the previous section (`scan_to_additive_master.lean`) only looks at
declarations that carry **no** translation link: it asks what `to_additive` *would*
generate and checks whether that declaration is already there, written by hand. It
therefore cannot see the opposite situation, which is just as common:

```lean
theorem upperCentralSeries_one : upperCentralSeries G 1 = center G := by ...

theorem _root_.AddSubgroup.upperCentralSeries_one (G : Type*) [AddGroup G] :
    AddSubgroup.upperCentralSeries G 1 = AddSubgroup.center G := by ...

attribute [to_additive existing (attr := simp) AddSubgroup.upperCentralSeries_one]
  upperCentralSeries_one
```

Here the two declarations *are* linked — by the `attribute [to_additive existing] …` line,
or by an `@[to_additive existing]` on the multiplicative declaration — but the additive one
is still written out and maintained by hand. Every such site is a bridge someone has to
keep in step. Some are unavoidable; others exist only because the multiplicative proof was
not translatable when the file was written.

## The new tooling

* `scripts/scan_to_additive_existing.lean` — walks the translation table of the whole
  environment and reports the pairs whose additive side is **hand-written**. The test used
  is a property of `to_additive` itself: a declaration it generates gets a source position
  *inside* the declaration it came from, whereas a hand-written one occupies a range of its
  own. Restricted to theorems and `Prop`-valued instances (a `def` genuinely has to be
  written twice) and to pairs living in the same module, master gives **168 candidates**
  (`contribution/master-scan-existing.txt`); it runs in about 20 seconds.
* `scripts/to_additive_existing.py` — the decider. For each candidate it moves the
  attribute onto the multiplicative declaration as a plain `@[to_additive …]`, drops the
  name from the `attribute [to_additive existing …]` command (deleting the command when it
  becomes empty), deletes the hand-written additive declaration, and rebuilds — requiring
  both that the file compiles and that an appended
  `example : <the old statement> := @Ns.the_additive_name` typechecks, so that the
  generated declaration provably has the statement that was there before. The file on disk
  is always restored, several candidates in one file are chained, and `--patch` emits the
  composed diff. `scripts/to_additive_twins.py` gained the shared parsing this needs
  (named `instance`s, and `set_option … in` / `variable … in` lines as part of the
  declaration below them).

## Result: 8 confirmed sites (−60 / +8)

`contribution/master-verify-existing.txt`, patch
`contribution/master-to_additive-existing.patch`; the ready-to-file PR text is
`contribution/PR-to_additive-existing.md`.  A full `lake build` of master with the
patch applied succeeds (8721 jobs, no error, `contribution/master-patched-build-existing.txt`).

| file | hand-written declaration that `@[to_additive]` regenerates |
| --- | --- |
| `Mathlib/Algebra/BigOperators/Pi.lean` | `Pi.single_induction` |
| `Mathlib/Algebra/Category/Grp/Limits.lean` | `AddCommGrpCat.forget_preservesLimits` |
| `Mathlib/Algebra/Category/MonCat/Limits.lean` | `AddCommMonCat.forget_preservesLimits` |
| `Mathlib/Algebra/Group/Defs.lean` | `negSucc_zsmul` |
| `Mathlib/Algebra/Symmetrized.lean` | `SymAlg.sym_neg`, `SymAlg.unsym_neg` |
| `Mathlib/GroupTheory/GroupAction/SubMulAction/OfStabilizer.lean` | `AddAction.stabilizerEquivStabilizer_compTriple` |
| `Mathlib/GroupTheory/Nilpotent.lean` | `AddSubgroup.upperCentralSeries_one` |

A detail the statement check alone does not catch: attributes. In
`Mathlib/Algebra/Symmetrized.lean` the hand-written `sym_neg` / `unsym_neg` are `@[simp]`,
and a naive `@[simp, to_additive]` would give `simp` to the multiplicative lemma only —
silently shrinking the simp set. The decider therefore moves the deleted declaration's own
attributes into `(attr := …)`, producing `@[to_additive (attr := simp)]`, which is also
what Mathlib's `existingAttributeWarning` linter asks for; that all four lemmas are simp
lemmas afterwards was checked in the patched file.

Two of them are of interest beyond the line count:

* `Pi.single_induction` is preceded by the comment *"manually additivized to fix variable
  names — see mathlib4 issue #11462"*. `to_additive` now renames those binders itself: the
  generated statement is the hand-written one, hypothesis names `zero`, `add`, `single`
  included. The workaround is no longer needed at this site.
* `AddSubgroup.upperCentralSeries_one` needs the explicit form
  `@[to_additive (attr := simp) AddSubgroup.upperCentralSeries_one]`: the naming heuristic
  turns `upperCentralSeries_one` into `upperCentralSeries_zero`, which is a different
  lemma. That is exactly the argument the attribute already carries, so the diff is a pure
  deletion of the twin and of the glue (−11 / +1). This hunk on its own is
  `contribution/master-upperCentralSeries_one.patch`.

## Independent Lean evidence

`RequestProject/MathlibContributionExisting.lean` re-checks four of the eight sites without
the scripts and against the Mathlib this project pins, where the same hand-written bridges
are present: the multiplicative declaration is copied verbatim, tagged `@[to_additive]`,
and the generated declaration is asserted equal to the Mathlib one
(`@negSucc_zsmul' = @negSucc_zsmul := rfl`, and likewise for `Pi.single_induction`,
`SymAlg.sym_neg`, `SymAlg.unsym_neg`). These `rfl`s only elaborate if the statements are
literally the same. The file builds with no `sorry`.

## Why the other 160 candidates were rejected

All of them were run through the same decider (`contribution/master-verify-existing-all.txt`):

* **17** were rejected by the compiler: the tag does not reproduce the hand-written
  declaration, usually because the multiplicative proof is not translatable, or because
  the additive statement is genuinely more general. `smul_eq_self_of_mem_zpowers`
  (repaired in the previous section by rerouting its proof) and Cauchy's theorem
  `exists_prime_orderOf_dvd_card` are among them, which is a useful consistency check: the
  new scanner independently rediscovers the bridges the earlier work identified as broken.
* **84** have an additive side that no one wrote by hand in the first place — it is
  produced by `mk_iff`, `irreducible_def (lemma := …)`, `simps` or `alias` on an additive
  definition, so there is nothing to delete (`finsum_def'`, `isLeftCancelAdd_iff`, …).
* **29** are `alias` pairs and **22** other declaration forms that the first pass of the
  source-level decider did not rewrite.

## Second batch: deprecated `alias` pairs (−86 / +15)

The decider was then taught to parse `alias` (including `alias ⟨a, _⟩ := h`, refusing the
deletion when the command introduces another name as well), and the 26 candidates whose
additive side is an `alias` were rerun: **15 PASS**
(`contribution/master-verify-existing-aliases.txt`, patch
`contribution/master-to_additive-existing-aliases.patch`). They are all instances of one
idiom — a deprecated alias pair kept in step by hand:

```lean
@[deprecated (since := "2026-04-08")] alias tendsto_finset_sum := tendsto_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias tendsto_finset_prod := tendsto_finsetProd
```

which collapses to

```lean
@[to_additive (attr := deprecated (since := "2026-04-08"))]
alias tendsto_finset_prod := tendsto_finsetProd
```

`(attr := deprecated …)` marks *both* the multiplicative alias and the generated additive
one as deprecated — checked in the patched file, not assumed — so the deprecation warnings
users see are unchanged. The 15 sites are in `Mathlib/Algebra/BigOperators/Finprod.lean`,
`…/Finsupp/Basic.lean`, `…/Group/Finset/Defs.lean`, `…/Group/Finset/Lemmas.lean`,
`Mathlib/Algebra/Group/Basic.lean`, `Mathlib/Probability/Process/Adapted.lean` and
`Mathlib/Topology/Algebra/Monoid.lean`. This is bookkeeping rather than mathematics — the
aliases are scheduled for deletion anyway — so it is kept separate from the eight-site
patch above; a full `lake build` of master with *both* patches applied succeeds
(`contribution/master-patched-build-existing.txt`).

---

## Import cost of homing `smul_eq_self_of_mem_zpowers` in the stabilizer file

An earlier note claimed that `Mathlib/GroupTheory/GroupAction/Basic.lean` (where
`MulAction.stabilizer` lives) can host the rerouted lemma
`smul_eq_self_of_mem_zpowers` at a cost of **one extra import, adding exactly one module
to that file's import closure**, and that `Mathlib/GroupTheory/GroupAction/FixedPoints.lean`
would cost **eight**. Both figures were re-measured here, against the Mathlib pinned by
this project (`8f9d9cff`, toolchain v4.28.0); the raw output is
`contribution/import-bump-stabilizer-file.txt`, produced by the new
`scripts/import_closure.py`.

**Result: the claim checks out, on both counts.**

| host file | closure now | new import | closure after | modules added |
|---|---|---|---|---|
| `GroupTheory/GroupAction/Basic.lean` | 522 | `Algebra.Group.Subgroup.ZPowers.Basic` | 523 | **1** |
| `GroupTheory/GroupAction/FixedPoints.lean` | 483 | same | 491 | **8** |

The asymmetry is explained by the direct imports of `ZPowers/Basic.lean`
(`Algebra.Divisibility.Basic`, `Algebra.Group.Subgroup.Map`, `Algebra.Group.Int.Defs`):
the stabilizer file already imports `Algebra.Group.Subgroup.Map` — it needs `Subgroup` to
state `MulAction.stabilizer` at all — so nothing but `ZPowers/Basic` itself is new. The
fixed-points file does not, so it drags in the `Subsemigroup`/`Submonoid`/`Subgroup` chain
as well (`Algebra.Group.Subsemigroup.Basic`, `Algebra.Group.Submonoid.Basic`,
`Algebra.Group.Submonoid.Operations`, `Algebra.Group.Subgroup.Lattice`,
`Algebra.Group.Subgroup.Map`, plus `Algebra.Group.Pi.Lemmas` and `Data.Set.Piecewise`).

**Downstream cost.** 2500 Mathlib modules import `GroupAction/Basic.lean` transitively, but
2486 of them already have `ZPowers/Basic` in their closure; only 14 grow, by one module
each (8 in `CategoryTheory/Galois` and `CategoryTheory/Action`, `GroupAction.CardCommute`,
`GroupAction.Quotient`, `GroupAction.SubMulAction.OfStabilizer`, `Perm.ClosureSwap`,
`LinearAlgebra.Alternating.DomCoprod`, and the file itself). Via `FixedPoints.lean` the
blast radius is smaller (195 dependants, 3 of which grow) but the per-file cost is up to 8.

**Compile checks** (checkout edited, compiled, restored byte-identically each time):

* `GroupAction/Basic.lean` with `public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic`
  added and the `@[to_additive]`-tagged lemma appended — compiles clean, no warnings;
* `OrderOfElement.lean` with the lemma, its hand-written twin
  `vadd_eq_self_of_mem_zmultiples` and the `attribute [to_additive existing]` line removed
  — compiles clean;
* no other Mathlib file mentions either name, and `OrderOfElement` imports
  `GroupAction/Basic` transitively anyway, so no call site can break.

So moving the lemma is possible at a genuine cost of one module in one file plus 14
downstream files gaining one module each. Whether it is *worth* moving is a separate,
non-mechanical question: the −12/+3 simplification of
`contribution/master-smul_eq_self_of_mem_zpowers.patch` needs no move at all
(`OrderOfElement.lean` already has everything), so the move buys only better placement,
at a nonzero import cost.

---

## Retest of the import bump against online Mathlib master

The measurement above was made on the Mathlib this project pins (`8f9d9cff`, toolchain
v4.28.0). It was re-run end to end on a fresh clone of
`leanprover-community/mathlib4` **master**, commit
`97b6a17d7e93a942ab7f7f777bb8fac2af129040` (15 Aug 2026, toolchain v4.34.0-rc1), with the
oleans taken from the public cache.

| host file | closure on `8f9d9cf` | closure on master `97b6a17` | modules added | downstream files that grow |
|---|---|---|---|---|
| `GroupTheory/GroupAction/Basic.lean` | 522 → 523 | 533 → 534 | **1** | 13 of 2850 dependants, +1 each |
| `GroupTheory/GroupAction/FixedPoints.lean` | 483 → 491 | 497 → 505 | **8** | 3 of 1719 dependants, ≤ +8 |

The costs are unchanged; only the absolute closure sizes and the dependant counts have
grown, and `LinearAlgebra.Alternating.DomCoprod` has left the list of files that would grow
(it now reaches `ZPowers/Basic` by another route).

What was actually run on master, with the move applied
(`contribution/master-import-bump-stabilizer.patch`, +8 / −13 lines over the two files):

* `lake env lean Mathlib/GroupTheory/GroupAction/Basic.lean` — exit 0, no errors, no
  warnings; deleting the added import again makes it fail with `Unknown constant
  `Subgroup.zpowers``, so the one extra import is exactly what the move needs;
* `lake env lean Mathlib/GroupTheory/OrderOfElement.lean` (13 lines removed) — exit 0;
* **whole-library `lake build` of patched master — `Build completed successfully (8724
  jobs)`**, no error or warning in the log;
* `contribution/check_import_bump.lean` — the pre-move multiplicative *and* additive
  statements typecheck against the moved lemma and the `@[to_additive]`-generated twin; the
  only change is binder order (`{α}` now precedes `{x y : G}`, since the stabilizer file has
  `G`, `α` as section variables), which no call site can observe — the two names occur in no
  other Mathlib file.

The checkout was restored afterwards and `git status` is empty. Raw log:
`contribution/master-import-bump.txt`. A step-by-step reproduction of all of this from
inside VS Code — extension setup, `lake exe cache get`, where to type the two edits, the
"Restart File" pitfall when import blocks change, and how to read the result — is
`REPRODUCE-IMPORT-BUMP.md`.
