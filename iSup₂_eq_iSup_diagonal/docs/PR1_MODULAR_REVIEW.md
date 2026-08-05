# Review of the modularised PR 1 draft

Short answer: **yes, worth adding** — the modularisation is an improvement on the single-lemma
version, and everything in the draft compiles unchanged. Two amendments are worth making before
posting, and one scope question needs a decision.

Everything below is machine-checked in `RequestProject/PR1Modular.lean` (full project build, no
`sorry`/`admit`). That file keeps the draft verbatim in namespace `AsProposed` and the suggested
amendment in namespace `Refined`.

---

## 1. What checks out as written

* All of part (a), (b) and (c) compile against the pinned Mathlib (`v4.28.0`).
* The three `example : @… = @… := rfl` checks succeed, so the replacement proofs really do prove
  the current `ENNReal.iSup_add_iSup`, `ENNReal.iInf_add_iInf` and `ENat.iSup_add_iSup` statements,
  unchanged.
* The two multiplicative statements compile too. This **refutes** the caution recorded earlier in
  `PR_SPLIT.md` §4, which guessed that multiplicative versions would need extra `≠ ∞` side
  conditions. They do not.
* None of the six new order/bounds lemmas exists upstream. A ripgrep of `Mathlib/` finds
  `upperBounds_mono_of_isCofinalFor` (`Order/Bounds/Basic.lean:144`), the `IsCofinalFor`
  `.of_subset`/`.rfl`/`.trans`/`.mono_left`/`.mono_right` API, `IsCofinalFor.image_of_monotone`
  (`Order/Bounds/Image.lean`) and `sSup_le_sSup_of_isCofinalFor` (`Order/CompleteLattice/Basic.lean:54`),
  but no range criterion, no `BddAbove` transfer, and no cofinal-collapse equality.
* The naming `iSup₂_eq_iSup_diagonal` matches the recommendation in `PR_SPLIT.md` §5, so adopting
  this draft also settles that naming nit.

---

## 2. Amendment 1 — state part (b) over `CompleteSemilatticeSup` and let `@[to_dual]` do the duals

The draft states the collapse lemmas over `CompleteLattice` and writes each dual by hand through
`(α := αᵒᵈ)`. Both can be improved at once:

```lean
@[to_dual]
theorem iSup₂_eq_iSup_of_forall_exists_le [CompleteSemilatticeSup α] (F : ι → κ → α) (G : ν → α)
    (hle : ∀ i j, ∃ k, F i j ≤ G k) (hge : ∀ k, ∃ i j, G k ≤ F i j) :
    ⨆ i, ⨆ j, F i j = ⨆ k, G k := by
  refine le_antisymm (sSup_le ?_) (sSup_le ?_) <;> rintro _ ⟨i, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hle i j
    exact hk.trans (le_sSup ⟨k, rfl⟩)
  · obtain ⟨a, b, hab⟩ := hge i
    exact hab.trans ((le_sSup (s := range (F a)) ⟨b, rfl⟩).trans (le_sSup ⟨a, rfl⟩))
```

* **Generality.** `CompleteSemilatticeSup` is strictly weaker than `CompleteLattice`, and the
  statement never mentions `⊓`, `⊥` or `⊤`. The draft is forced up to `CompleteLattice` only by the
  API it uses: `iSup_mono'`, `iSup₂_le`, `le_iSup₂` and `iSup_le` all carry `[CompleteLattice α]`
  in this Mathlib, while `sSup_le`/`le_sSup` need only `[CompleteSemilatticeSup α]`. (Checked: the
  `iSup_mono'` proof fails to elaborate at `CompleteSemilatticeSup`.)
* **Half the declarations.** With `@[to_dual]` the three `iInf` lemmas are generated, including
  their names — the linter reports the explicit dual names as redundant for
  `iSup_eq_iSup_of_forall_exists_le` and `isCofinalFor_range_iff`. The generated duals land at
  `CompleteSemilatticeInf`, which the hand-written `(α := αᵒᵈ)` versions cannot reach from a
  `CompleteLattice` statement.
* Same for part (a): `@[to_dual]` generates `IsCoinitialFor.bddBelow` and the coinitial range
  criterion, so the `(α := αᵒᵈ)` bodies can go.

One caveat carried over from the earlier draft, still true: the shorter `iSup_le`/`le_iSup` form of
the proof breaks `@[to_dual]` (`SupSet`/`InfSet` projection mismatch), so the proof must stay on the
`sSup`/`le_sSup` API. Worth a sentence in the PR body, or a reviewer will suggest exactly that golf.

## 3. Amendment 2 — drop `[Nonempty ι]` from the two multiplicative statements

They hold for empty `ι` as well (both sides are `0` in `ℝ≥0∞` and in `ℕ∞`), with the same
`cases isEmpty_or_nonempty ι` opening the additive proofs already use:

```lean
theorem ennreal_iSup_mul_iSup {ι : Sort*} {f g : ι → ℝ≥0∞}
    (h : ∀ i j, ∃ k, f i * g j ≤ f k * g k) : iSup f * iSup g = ⨆ i, f i * g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [ENNReal.iSup_mul, ENNReal.mul_iSup]
    exact iSup₂_eq_iSup_diagonal _ h
```

Checked for both `ℝ≥0∞` and `ℕ∞`.

## 4. Scope question — part (a) has no caller inside PR 1

`isCofinalFor_range_iff`, `IsCofinalFor.bddAbove` and `IsCoinitialFor.bddBelow` are not used
anywhere else in the draft: parts (b) and (c) go through `sSup_le`/`le_sSup` and never mention
`IsCofinalFor` or `BddAbove`. By the splitting rule in `PR_SPLIT.md` §0 (rule 7: no caller yet),
they do not belong in PR 1 as it stands. Three ways out, in order of preference:

1. **Move part (a) to PR 2.** The conditionally complete lemma `ciSup₂_eq_ciSup_diagonal` is where
   `BddAbove` side conditions actually appear, and `IsCofinalFor.bddAbove` discharges the inner one
   (`BddAbove (range (f i))` for each row `i`, since a row is cofinal in the diagonal) — checked,
   so that is a real caller. The outer side condition `BddAbove (range fun i => ⨆ j, f i j)` is
   *not* an instance of it: a row supremum need not be below any single diagonal entry.
2. **Use it in part (b)**: phrase the hypotheses of the collapse lemmas as
   `IsCofinalFor (range F.uncurry) (range G)` and let `isCofinalFor_range_iff` mediate. This makes
   part (a) load-bearing but makes the call sites slightly noisier.
3. Keep it, and justify the two `BddAbove` lemmas as the missing companions of the existing
   `upperBounds_mono_of_isCofinalFor` in the same file. Defensible, but it is a second review
   argument inside one PR.

Also minor, on the same lemma: `isCofinalFor_range_iff` is proved by `simp [IsCofinalFor]`, i.e. by
unfolding the definition. That is fine, but as a `@[simp]` lemma it should be checked against the
existing `IsCofinalFor` simp set so that `simp` does not have two routes to the same normal form.

## 5. Remaining judgement call — the multiplicative lemmas

They are true, cheap, and now hypothesis-free (§3), but they have **no caller** in Mathlib. Rule 7
would keep them out of PR 1. The pragmatic option is to mention them in the PR description
("the same lemma gives the multiplicative versions, which Mathlib currently lacks; happy to add
them here or in a follow-up") and let the reviewer choose.

---

## Summary

| Item | Verdict |
|---|---|
| Part (a) `isCofinalFor_range_iff` | New upstream, compiles; no caller in PR 1 — move to PR 2 or make it load-bearing |
| Part (a) `IsCofinalFor.bddAbove` / `IsCoinitialFor.bddBelow` | New upstream, compiles; same scope question; use `@[to_dual]` for the second |
| Part (b) mutual cofinality / cofinal family / diagonal | Keep the modular chain; restate at `CompleteSemilatticeSup` with `@[to_dual]` (3 declarations instead of 6) |
| Part (c) three call sites | Correct, `rfl`-checked against current statements; residual `cases isEmpty_or_nonempty ι` is genuinely unavoidable |
| Multiplicative additions | Compile, and `[Nonempty ι]` can be dropped; no caller, so offer in the PR text rather than the diff |
