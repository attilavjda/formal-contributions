/-
Machine check backing the proposed Mathlib docstring fix in
`Mathlib/Analysis/Normed/Lp/PiLp.lean` (see `mathlib-pilp-docstring-fix.patch`).

The docstrings of the four `PiLp` "norm of a constant vector" lemmas cross-reference each
other. Two of those cross-references still used the pre-rename names
`PiLp.nnnorm_equiv_symm_const'` and `PiLp.norm_equiv_symm_const`, which no longer exist.

This file checks, mechanically, that

* the four lemma names used in the corrected docstrings all exist, and
* the two names used in the current (broken) docstrings do not exist.
-/
import Mathlib.Analysis.Normed.Lp.PiLp

namespace PiLpDocRefCheck

open Lean

-- The names referenced by the *corrected* docstrings all exist.
#check @PiLp.nnnorm_toLp_const
#check @PiLp.nnnorm_toLp_const'
#check @PiLp.norm_toLp_const
#check @PiLp.norm_toLp_const'

-- Fail at elaboration time if either of the pre-rename names is still declared.
run_cmd do
  let env ← Lean.getEnv
  for n in [`PiLp.nnnorm_equiv_symm_const', `PiLp.norm_equiv_symm_const] do
    if env.contains n then
      throwError "unexpected: `{n}` exists"

end PiLpDocRefCheck
