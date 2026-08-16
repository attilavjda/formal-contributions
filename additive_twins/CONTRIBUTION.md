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
