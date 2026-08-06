import Mathlib

/-!
# PR 3 — the smallest defensible fix: two wrong docstrings on `mul_iInf_of_ne`

While looking for an upstream contribution in the scope of this project (indexed `⨆`/`⨅`
over `ℝ≥0∞`, `ℕ∞` and friends), the smallest near-unambiguous improvement found is a pure
documentation fix: in the pinned Mathlib, both `ENNReal.mul_iInf_of_ne` and
`ENat.mul_iInf_of_ne` carry the docstring of their *right*-multiplication twin.

Current text (verbatim, checked by `#eval` below):

* `ENNReal.mul_iInf_of_ne` —
  "If `a ≠ 0` and `a ≠ ∞`, then **right** multiplication by `a` maps infimum to infimum.
   See `ENNReal.mul_iInf'` for the general case, and `ENNReal.iInf_mul` for another special
   case that assumes `Nonempty ι` but does not require `a ≠ 0`, **and `ENNReal`.**"
* `ENat.mul_iInf_of_ne` —
  "If `a ≠ 0`, then **right** multiplication by `a` maps infimum to infimum.
   See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`."

Three defects, all a consequence of one copy-paste from the neighbouring `iInf_mul_of_ne`:

1. **Wrong side.**  `mul_iInf_of_ne : a * ⨅ i, f i = ⨅ i, a * f i` is *left* multiplication;
   right multiplication is `iInf_mul_of_ne : (⨅ i, f i) * a = ⨅ i, f i * a`, whose (correct)
   docstring is where this text belongs.
2. **Cross-reference points at the wrong-sided lemma.**  The "see also" of the left lemma
   names `iInf_mul`, the `Nonempty ι` version of the *right* lemma; the intended target is
   `mul_iInf`.
3. **Truncated sentence** (`ENNReal` only): the docstring ends with a dangling
   "…, and `ENNReal`."

The fix is a four-line diff, changes no statement and no proof, and removes breakage rather
than adding API.  This file machine-checks every claim above: the current docstrings are read
out of the environment, the sidedness of all six declarations involved is pinned down by
`example`s that must elaborate, and the replacement text is recorded verbatim.

The diff itself is in `MATHLIB-PR3-DOCFIX.md` (and `mathlib-docfix-mul_iInf_of_ne.patch`),
against `Mathlib/Data/ENNReal/Inv.lean` and `Mathlib/Data/ENat/Lattice.lean`.
-/

namespace PR3

/-! ### 1. What the declarations actually say

Each `example` below elaborates only if the named lemma has exactly the indicated side, so
these four lines are the machine-checked form of "the two docstrings are swapped".
-/

section Statements

variable {ι : Sort*}

/-- `ENNReal.mul_iInf_of_ne` is **left** multiplication — contradicting its docstring. -/
example {f : ι → ENNReal} {a : ENNReal} (ha₀ : a ≠ 0) (ha : a ≠ ⊤) :
    a * ⨅ i, f i = ⨅ i, a * f i := ENNReal.mul_iInf_of_ne ha₀ ha

/-- `ENNReal.iInf_mul_of_ne` is **right** multiplication — its docstring is the correct one. -/
example {f : ι → ENNReal} {a : ENNReal} (ha₀ : a ≠ 0) (ha : a ≠ ⊤) :
    (⨅ i, f i) * a = ⨅ i, f i * a := ENNReal.iInf_mul_of_ne ha₀ ha

/-- `ENat.mul_iInf_of_ne` is **left** multiplication — contradicting its docstring. -/
example {f : ι → ℕ∞} {a : ℕ∞} (ha₀ : a ≠ 0) :
    a * ⨅ i, f i = ⨅ i, a * f i := ENat.mul_iInf_of_ne ha₀

/-- `ENat.iInf_mul_of_ne` is **right** multiplication — its docstring is the correct one. -/
example {f : ι → ℕ∞} {a : ℕ∞} (ha₀ : a ≠ 0) :
    (⨅ i, f i) * a = ⨅ i, f i * a := ENat.iInf_mul_of_ne ha₀

/-! The cross-referenced lemmas, showing that the "see also" of each `mul_iInf_of_ne` names
the wrong-sided one: `mul_iInf` is the left `Nonempty ι` version, `iInf_mul` the right one. -/

example [Nonempty ι] {f : ι → ENNReal} {a : ENNReal}
    (hinfty : a = ⊤ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    a * ⨅ i, f i = ⨅ i, a * f i := ENNReal.mul_iInf hinfty

example [Nonempty ι] {f : ι → ENNReal} {a : ENNReal}
    (hinfty : a = ⊤ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    (⨅ i, f i) * a = ⨅ i, f i * a := ENNReal.iInf_mul hinfty

example [Nonempty ι] {f : ι → ℕ∞} {a : ℕ∞} : a * ⨅ i, f i = ⨅ i, a * f i := ENat.mul_iInf

example [Nonempty ι] {f : ι → ℕ∞} {a : ℕ∞} : (⨅ i, f i) * a = ⨅ i, f i * a := ENat.iInf_mul

end Statements

/-! ### 2. The docstrings, read out of the environment

`checkDocString` fails at elaboration time unless the declaration's docstring is exactly the
given string, so the two `#eval`s below pin the *current* (incorrect) text: if the fix lands
upstream, or the text is edited in any way, this file stops compiling.
-/

open Lean in
/-- Throw unless the docstring of `n` is, up to surrounding whitespace, `s`. -/
def checkDocString (n : Name) (s : String) : CoreM Unit := do
  let some d ← findDocString? (← getEnv) n | throwError "{n} has no docstring"
  unless d.trimAscii.toString = s.trimAscii.toString do
    throwError "docstring of {n} is not the expected one; found:\n{d}"

open Lean in
#eval checkDocString ``ENNReal.mul_iInf_of_ne
  "If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum.\n\n\
   See `ENNReal.mul_iInf'` for the general case, and `ENNReal.iInf_mul` for another special \
   case that\nassumes `Nonempty ι` but does not require `a ≠ 0`, and `ENNReal`."

open Lean in
#eval checkDocString ``ENat.mul_iInf_of_ne
  "If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.\n\
   See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`."

-- For contrast, the two right-multiplication lemmas carry that same text legitimately.
open Lean in
#eval checkDocString ``ENat.iInf_mul_of_ne
  "If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.\n\
   See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`."

/-! ### 3. The replacement text

Recorded verbatim so the PR body and the patch cannot drift apart.  These are the exact
docstrings the diff installs on `ENNReal.mul_iInf_of_ne` and `ENat.mul_iInf_of_ne`.
-/

/-- The corrected docstring for `ENNReal.mul_iInf_of_ne`. -/
def ennrealReplacement : String :=
  "If `a ≠ 0` and `a ≠ ∞`, then left multiplication by `a` maps infimum to infimum.\n\n\
   See `ENNReal.mul_iInf'` for the general case, and `ENNReal.mul_iInf` for another special \
   case that\nassumes `Nonempty ι` but does not require `a ≠ 0`."

/-- The corrected docstring for `ENat.mul_iInf_of_ne`. -/
def enatReplacement : String :=
  "If `a ≠ 0`, then left multiplication by `a` maps infimum to infimum.\n\
   See also `ENat.mul_iInf` that assumes `[Nonempty ι]` but does not require `a ≠ 0`."

/-! The replacement is exactly the current text with the three flagged edits applied — wrong
side, wrong cross-reference, and (for `ENNReal`) the dangling trailing clause — and nothing
else.  The two `#eval`s below patch the docstring found in the environment and compare it with
the recorded replacement, so the PR body cannot drift from the diff. -/

open Lean in
#eval show CoreM Unit from do
  let some d ← findDocString? (← getEnv) ``ENNReal.mul_iInf_of_ne | throwError "no docstring"
  let patched := ((d.replace "right multiplication" "left multiplication").replace
    "`ENNReal.iInf_mul`" "`ENNReal.mul_iInf`").replace ", and `ENNReal`." "."
  unless patched.trimAscii.toString = ennrealReplacement.trimAscii.toString do
    throwError "patched docstring differs from the recorded replacement:\n{patched}"

open Lean in
#eval show CoreM Unit from do
  let some d ← findDocString? (← getEnv) ``ENat.mul_iInf_of_ne | throwError "no docstring"
  let patched := (d.replace "right multiplication" "left multiplication").replace
    "`ENat.iInf_mul`" "`ENat.mul_iInf`"
  unless patched.trimAscii.toString = enatReplacement.trimAscii.toString do
    throwError "patched docstring differs from the recorded replacement:\n{patched}"

end PR3
