# What goes in the same PR, and what goes in a different one

This note is the packaging plan for the golfed material: which of the checked declarations in
this project belong together in one upstream pull request, which must be split off, and which
should not be posted at all.

Everything quoted below is machine-checked in this project (`RequestProject/Diagonal.lean`,
`RequestProject/NextPR.lean`, `RequestProject/MutualCofinalityPR.lean`, `Main.lean`; the build has
no `sorry`/`admit`). The golfing rationale is in `GOLF.md`, the applied diffs in `UPSTREAM.patch`
(PR 1) and `GOLF.patch` (PR 1 + PR 2 hunks).

---

## 0. The splitting rule used here

A change belongs in the **same** PR as the new lemma when it is *evidence for that lemma*:

1. it is the lemma itself, its `@[to_dual]` partner, and its docstring;
2. it is a **caller rewrite the new lemma enables** (this is what justifies the addition);
3. it is a golf **inside a hunk the PR already touches** (free, reviewed anyway).

A change belongs in a **different** PR when it is *independently justifiable*:

4. it lives in a different file / different typeclass API and would still be worth landing if the
   first PR were rejected;
5. it needs its own hypotheses (`BddAbove`, `Nonempty`, …) and therefore its own review argument;
6. it is a golf of code the PR does not otherwise touch (unrelated churn — reviewers dislike it);
7. it is a generalisation with no caller yet.

One consequence worth stating: **the golfing is not a separate PR.** Golfs of the *new* lemma
ship inside the PR that introduces it (nobody should review the ungolfed version first), and golfs
of *existing* proofs ship only when the PR already rewrites those proofs.

---

## 1. PR 1 — the diagonal collapse lemma + its three callers

**Title:** `feat(Order/CompleteLattice): diagonal collapse for doubly indexed suprema`

**Same PR (all of it):**

* New lemma in `Mathlib/Order/CompleteLattice/Basic.lean`, next to `iSup_mono'` / `iSup₂_mono'`,
  in the `CompleteSemilatticeSup` section — golfed form (9 lines, was 16):

```lean
/-- A doubly indexed supremum equals the supremum along its diagonal when the diagonal is
cofinal. -/
@[to_dual iInf₂_eq_diagonal]
theorem iSup₂_eq_diagonal {α : Type*} {ι : Sort*} [CompleteSemilatticeSup α]
    (f : ι → ι → α) (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  refine le_antisymm (sSup_le ?_) (sSup_le ?_) <;> rintro _ ⟨i, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := h i j
    exact hk.trans (le_sSup ⟨k, rfl⟩)
  · exact (le_sSup (s := range (f i)) ⟨i, rfl⟩).trans (le_sSup ⟨i, rfl⟩)
```

  The generated dual `iInf₂_eq_diagonal` is part of the same declaration — never a separate PR.

* The three caller rewrites it collapses (these *are* the justification, so they must be here):
  * `ENat.iSup_add_iSup` — `Mathlib/Data/ENat/Lattice.lean`
  * `ENNReal.iSup_add_iSup` — `Mathlib/Data/ENNReal/Operations.lean`
  * `ENNReal.iInf_add_iInf` — same file, via the generated dual

```lean
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [iSup_add, add_iSup]
    exact iSup₂_eq_diagonal (fun i j ↦ f i + g j) h
```

* The one-token golf `simp only [iSup_of_empty, bot_eq_zero, zero_add]` → `simp` in the empty
  branch of those same proofs. Same PR by rule 3: the hunk is open anyway.

**Explicitly not in PR 1** (rules 4–7): the conditionally complete variants, the `IsCofinalFor`
equalities, the `Cardinal` corollary, the cofinal-subset chain.

**Deliberate scope note for the PR description:** the lemma is stated over `CompleteSemilatticeSup`
rather than `CompleteLattice`, and the proof stays on the `sSup_le`/`le_sSup` API because the
shorter `iSup_le`/`le_iSup` golf breaks `@[to_dual]` (the translated term keeps a `SupSet`
projection where an `InfSet` one is needed). Say this in the PR body — otherwise a reviewer will
suggest exactly that golf.

---

## 2. PR 2 — the conditionally complete version + the `Cardinal` caller

**Title:** `feat(Order/ConditionallyCompleteLattice): diagonal collapse for conditionally complete suprema`

Separate from PR 1 by rules 4 and 5: different file, different API, extra `BddAbove` hypothesis,
and its own caller evidence. It does **not** depend on PR 1 landing first — the two can be open
simultaneously; neither patch touches the other's files.

**Same PR:**

* One lemma in `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`, next to
  `ciSup_mono_of_forall_exists` — golfed form (~12 lines, was two lemmas of ~26 lines; checked here
  in the argument order recommended in section 5):

```lean
theorem ciSup₂_eq_ciSup_diagonal {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]
    (f : ι → ι → α) (hf : BddAbove (Set.range fun k ↦ f k k))
    (h : ∀ i j, ∃ k, f i j ≤ f k k) :
    (⨆ i, ⨆ j, f i j) = ⨆ k, f k k := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · -- The central fact: every entry is below the diagonal supremum, `f i j ≤ ⨆ k, f k k`.
    have hle : ∀ i j, f i j ≤ ⨆ k, f k k := fun i j ↦
      let ⟨k, hk⟩ := h i j; hk.trans (le_ciSup hf k)
    have hrow : ∀ i, BddAbove (Set.range (f i)) := fun i ↦ ⟨_, Set.forall_mem_range.2 (hle i)⟩
    have hcol : BddAbove (Set.range fun i ↦ ⨆ j, f i j) :=
      ⟨_, Set.forall_mem_range.2 fun i ↦ ciSup_le (hle i)⟩
    exact le_antisymm (ciSup_le fun i ↦ ciSup_mono_of_forall_exists hf (h i))
      (ciSup_le fun k ↦ le_ciSup_of_le hcol k (le_ciSup (hrow k) k))
```

* The `Cardinal` caller `Cardinal.ciSup_add_ciSup_diagonal` in
  `Mathlib/SetTheory/Cardinal/Arithmetic.lean` (see `GOLF.patch`). It is the only concrete caller
  that *needs* the conditionally complete version, so it stays with it rather than going to PR 1.

**Post the deduplication finding in the PR text, not as code.** The
`ConditionallyCompleteLinearOrderBot` variant requested on Zulip is *not a second lemma*: once
`Nonempty ι` is dropped from the general statement (empty `ι` gives `sSup ∅` on both sides, no `⊥`
needed), the primed version is literally the same statement, since a
`ConditionallyCompleteLinearOrderBot` is a `ConditionallyCompleteLattice`. Say so in the PR
description; do **not** ship

```lean
theorem ciSup₂_eq_ciSup_diagonal' … := ciSup₂_eq_ciSup_diagonal f hf h   -- redundant, don't post
```

(It is kept in `RequestProject/NextPR.lean` only as a record of the fact.)

**If the reviewer insists on one PR.** The Zulip request asked for the complete and conditionally
complete versions together. If that is repeated on the PR, merging PR 2 into PR 1 is acceptable —
the combined diff is still ~40 added lines across three files plus four caller rewrites. In that
case order the commits `add complete-lattice lemma` → `add conditionally complete lemma` →
`simplify callers`, so the review can be read hunk by hunk. Do *not* additionally fold in PR 3.

---

## 3. PR 3 — mutual cofinality (follow-up, independent)

**Title:** `feat(Order): suprema of mutually cofinal families agree`

Separate by rule 4: it is a statement about `IsCofinalFor`, self-justifying, and it lands next to
the existing one-sided lemmas `sSup_le_sSup_of_isCofinalFor` / `sInf_le_sInf_of_isCoinitialFor`.

**Same PR:**

* the set-level pair `sSup_eq_sSup_of_isCofinalFor` / `sInf_eq_sInf_of_isCoinitialFor`;
* the indexed pair `iSup_eq_iSup_of_forall_exists_le` / `iInf_eq_iInf_of_forall_exists_le`,
  derived from the set-level ones on `Set.range`;
* the two caller rewrites: `iSup_eq_iSup_subseq_of_monotone` and
  `iSup_eq_iSup_subseq_of_antitone` in `Mathlib/Topology/Order/MonotoneConvergence.lean`. Their two
  `iInf` counterparts already delegate to these, so they improve transitively — mention that,
  don't rewrite them.

**Not in this PR:** re-deriving `iSup₂_eq_diagonal` through the mutual-cofinality route. It works
(checked in `Main.lean` via `iSup_prod'`) but weakens the index from `Sort*` to `Type*`, so the
diagonal lemma keeps its direct proof and PR 1 stays independent of PR 3.

---

## 4. What not to post anywhere (yet)

| Item | Where it lives here | Why not |
|---|---|---|
| `ciSup₂_eq_ciSup_diagonal'` | `RequestProject/NextPR.lean` | Same statement as the unprimed lemma once `Nonempty ι` is dropped (rule: no duplicate API). |
| Cofinal-subset chain (`sSup_eq_sSup_of_subset_of_isCofinalFor`, indexed subfamily/reindexing lemmas, `iSup_ne_bot_subtype` refactor) | `RequestProject/SubsetTransitiveCallers.lean`, `SUBSET_TRANSITIVE_CALLERS.md` | Credible as its own later PR, but overlaps PR 3's content; wait until PR 3 lands and a reviewer asks. |
| `Monotone.iSup_comp_eq` refactor | `RequestProject/SubsetTransitiveCallers.lean` | Existing proof is already one line — a rewrite is churn, not simplification (rule 6). |
| ~20 stylistic variants (term mode, `calc`, `iSup_mono'` one-liner) | `RequestProject/DiagonalVariations.lean` | Exploration only; the submitted form is argued in `PR_FORM.md`. |
| Multiplicative `iSup_mul_iSup` equalities | — | Do not exist upstream; would need extra `≠ ∞` / `BddAbove` side conditions and have no caller (rule 7). |
| A "cofinal subfamily" typeclass or a general binary-op-commutes-with-sup abstraction | — | New framework; the stated preference is small discoverable lemmas. |

---

## 5. Two naming nits to settle before posting

Both appear inconsistently across the drafts in this project; pick once and make the patch and the
PR text agree.

* **Lemma name.** `iSup₂_eq_diagonal` (used in `UPSTREAM.patch`, `Diagonal.lean`, `Main.lean`)
  vs `iSup₂_eq_iSup_diagonal` (used in `GOLF.patch`). The second matches the `ciSup` name and the
  usual convention of naming both sides; the first is shorter and is what the checked callers use.
  Recommendation: submit as `iSup₂_eq_iSup_diagonal` / `iInf₂_eq_iInf_diagonal` for symmetry with
  `ciSup₂_eq_ciSup_diagonal`, and update the three callers accordingly.
* **Argument order of the conditionally complete lemma.** `(f) (hf) (h)` in `Diagonal.lean` vs
  `(f) (h) (hb)` in `GOLF.patch`. Recommendation: `(f) (hf) (h)`, matching
  `ciSup_mono_of_forall_exists`, which takes the boundedness hypothesis first.

---

## 6. Posting order

1. Open **PR 1**. Smallest, has three existing duplicate callers, no new hypotheses.
2. Open **PR 2** in parallel (or fold into PR 1 if the reviewer asks); link it from PR 1 and state
   that the `…Bot` variant collapses into the general one.
3. After PR 1 or PR 2 is merged, open **PR 3**; then reconsider the cofinal-subset chain from
   section 4 in light of the review comments.

Each PR must be green on its own: none of the three depends on another's declarations.
