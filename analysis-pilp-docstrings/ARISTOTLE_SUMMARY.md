# Summary of changes for run bc6b24e8-19af-4b70-a7e4-21700f916d69
I identified a tiny Mathlib PR opportunity and then formalized its mathematical content in Lean, so the proposed docstring text is checked by the kernel rather than only proofread.

**The PR opportunity** — `Mathlib/Analysis/Normed/Lp/PiLp.lean`. Four sibling lemmas compute the (nn)norm of a constant vector: `PiLp.nnnorm_toLp_const` / `PiLp.norm_toLp_const` (assuming `p ≠ ∞`) and `PiLp.nnnorm_toLp_const'` / `PiLp.norm_toLp_const'` (assuming `[Nonempty ι]`). Their docstrings cross-reference each other, and two of those references were never updated when the lemmas were renamed from the `equiv_symm` scheme to the `toLp` scheme, so they name declarations that do not exist (`PiLp.nnnorm_equiv_symm_const'`, `PiLp.norm_equiv_symm_const`). Two of the same docstrings also have a bad line wrap that splits a sentence with a stray full stop. The fix is a four-line diff that only removes breakage — the "wrong docstrings" category, no new API.

**Formalization** (`RequestProject/PiLpConstNorm.lean`, builds with no `sorry`, axioms `propext`/`Classical.choice`/`Quot.sound` only). The docstrings assert that the hypotheses cannot be dropped and give a reason; all of that is now proved:

- `PiLp.nnnorm_toLp_const_top_of_isEmpty` — the docstrings' "the left-hand side simplifies to `0`".
- `PiLp.const_rhs_top_of_isEmpty` — the docstrings' "the right-hand side simplifies to `‖b‖₊`".
- `PiLp.nnnorm_toLp_const_of_forall_false` and `PiLp.norm_toLp_const_of_forall_false` — the unrestricted formula is genuinely **false**, with the explicit witness `p = ∞`, `ι = Fin 0`, `β = ℝ`, `b = 1` (sides `0` and `1`).
- `PiLp.nnnorm_toLp_const_of_ne_top_or_nonempty` and `PiLp.norm_toLp_const_of_ne_top_or_nonempty` — the disjunction `p ≠ ∞ ∨ Nonempty ι` already suffices, so the two Mathlib lemmas are the two halves of a single statement.
- `PiLp.nnnorm_toLp_const_iff` — exact characterisation: the formula holds iff `p ≠ ∞ ∨ Nonempty ι ∨ ‖b‖₊ = 0`; so outside the trivial case `‖b‖₊ = 0` the disjunction is necessary as well as sufficient.

**Also in the project**
- `mathlib-pilp-docstring-fix.patch` — the ready-to-apply diff, with a suggested commit message. `Mathlib.Analysis.Normed.Lp.PiLp` was rebuilt with it applied and compiles cleanly; the dependency checkout was then restored to pristine so the patch applies to unmodified upstream.
- `RequestProject/PiLpDocRefCheck.lean` — a machine check that the four corrected names exist and that neither pre-rename name is declared, so the two references really are dangling.
- `PR-PROPOSAL.md` — the write-up: what is broken, the patch, what was formalized, and a note that promoting the two merged lemmas into Mathlib (making the existing four one-line corollaries) is a natural follow-up, deliberately kept out of this docstring-only PR.

All work is committed and pushed. Two other leads were checked and rejected: the `@[to_additive]` TODO on `FreeGroup.Red.decidableRel` still fails with exactly the equation-lemma mismatch its comment records, and the `Finset.Ico_subset_Ioo_iff` / `Ioc_subset_Ioo_iff` TODO is not a one-liner because the corresponding `Set` lemmas are absent too.