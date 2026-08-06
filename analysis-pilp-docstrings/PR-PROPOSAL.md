# A tiny Mathlib PR: fix stale cross-references in `PiLp` docstrings

## Category

*Fixing what's broken — wrong docstrings.* The diff is four lines and removes breakage
(dangling references to declarations that no longer exist); it adds no new API.

## Where

`Mathlib/Analysis/Normed/Lp/PiLp.lean`, the block of four lemmas computing the (nn)norm of a
constant vector:

| lemma | hypothesis |
|---|---|
| `PiLp.nnnorm_toLp_const`  | `p ≠ ∞` |
| `PiLp.nnnorm_toLp_const'` | `[Nonempty ι]` |
| `PiLp.norm_toLp_const`    | `p ≠ ∞` |
| `PiLp.norm_toLp_const'`   | `[Nonempty ι]` |

Each docstring points the reader at its sibling ("See `X` for a version which exchanges the
hypothesis ... for ...").

## What is broken

1. Two of those cross-references were never updated when the lemmas were renamed from the
   `equiv_symm` naming scheme to the `toLp` one. They name declarations that do not exist:
   - `PiLp.nnnorm_equiv_symm_const'` (should be `PiLp.nnnorm_toLp_const'`)
   - `PiLp.norm_equiv_symm_const` (should be `PiLp.norm_toLp_const`)

   The second one is additionally the *wrong* sibling in spirit: it sits on the primed lemma
   `norm_toLp_const'`, so the sibling it should advertise is the unprimed `PiLp.norm_toLp_const`.

2. Two docstrings have a stray full stop in the middle of a sentence caused by a bad line wrap:

   ```
   ... which exchanges the hypothesis `Nonempty ι`.
   for `p ≠ ∞`. -/
   ```

   which renders in the docs as two broken sentences. Rewrapping fixes it.

## The patch

See `mathlib-pilp-docstring-fix.patch` (applies to `Mathlib/Analysis/Normed/Lp/PiLp.lean`).

Suggested commit message:

```
chore(Analysis/Normed/Lp/PiLp): fix stale docstring cross-references

The docstrings of `PiLp.nnnorm_toLp_const` and `PiLp.norm_toLp_const'` still referred to
`PiLp.nnnorm_equiv_symm_const'` and `PiLp.norm_equiv_symm_const`, which no longer exist after
the `equiv_symm` -> `toLp` rename. Also fix a line wrap that split a sentence with a stray
full stop.
```

## Verification

* `Mathlib.Analysis.Normed.Lp.PiLp` was rebuilt with the patch applied and compiles cleanly.
* `RequestProject/PiLpDocRefCheck.lean` is a machine check of the claim: it `#check`s that the
  four corrected names exist, and a `run_cmd` fails the build if either of the two pre-rename
  names is still declared in the environment. It builds successfully, so the two referenced
  names really are dangling.
* `RequestProject/PiLpConstNorm.lean` formalizes the *mathematical* content of the docstrings
  being edited, so that the corrected text is checked against Lean and not just proofread.

## What is formalized (`RequestProject/PiLpConstNorm.lean`)

The docstrings claim that the hypotheses `p ≠ ∞` / `[Nonempty ι]` cannot be dropped, and give a
reason. All of that is now proved, with no `sorry` and on the standard axioms only:

| theorem | content |
|---|---|
| `PiLp.nnnorm_toLp_const_top_of_isEmpty` | the docstrings' "the left-hand side simplifies to `0`" |
| `PiLp.const_rhs_top_of_isEmpty` | the docstrings' "the right-hand side simplifies to `‖b‖₊`" |
| `PiLp.nnnorm_toLp_const_of_forall_false` | the unrestricted formula is **false** (witness `p = ∞`, `ι = Fin 0`, `b = (1 : ℝ)`) |
| `PiLp.norm_toLp_const_of_forall_false` | ditto for `norm` |
| `PiLp.nnnorm_toLp_const_of_ne_top_or_nonempty` | the disjunction `p ≠ ∞ ∨ Nonempty ι` already suffices |
| `PiLp.norm_toLp_const_of_ne_top_or_nonempty` | ditto for `norm` |
| `PiLp.nnnorm_toLp_const_iff` | exact characterisation: the formula holds iff `p ≠ ∞ ∨ Nonempty ι ∨ ‖b‖₊ = 0` |

The last three make the "exchanges the hypothesis `p ≠ ∞` for `Nonempty ι`" phrasing of the
docstrings precise: the two Mathlib lemmas are exactly the two halves of one statement whose
hypothesis is the disjunction, and (outside the trivial case `‖b‖₊ = 0`) that disjunction is
not merely sufficient but necessary.  A possible follow-up PR is to add
`nnnorm_toLp_const_of_ne_top_or_nonempty` / `norm_toLp_const_of_ne_top_or_nonempty` to Mathlib
and make the existing four lemmas one-line corollaries of them; the present PR deliberately
stays a docstring-only fix.

## How the opportunity was found

All docstrings in the compiled Mathlib environment were scanned for backticked identifier-like
tokens, and each token was tested against the set of declaration names (and their namespace
suffixes) present in the environment. Tokens that resolve to nothing are candidate broken
cross-references; this one was confirmed by hand as a leftover from a rename.
