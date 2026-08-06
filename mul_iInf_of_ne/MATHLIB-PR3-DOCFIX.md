# PR 3 — the smallest thing worth upstreaming here

**Title:** `chore(Data/ENNReal,Data/ENat): fix the docstring of `mul_iInf_of_ne``

**Type:** documentation fix. No statement, proof or name changes; nothing added to the API.

## What is wrong

`mul_iInf_of_ne` and `iInf_mul_of_ne` sit next to each other in two files. In both files the
*left*-multiplication lemma carries the docstring of its *right*-multiplication twin, evidently a
copy-paste that was never edited.

`Mathlib/Data/ENNReal/Inv.lean` (in the pinned version, lines 849–854):

```
/-- If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum.

See `ENNReal.mul_iInf'` for the general case, and `ENNReal.iInf_mul` for another special case that
assumes `Nonempty ι` but does not require `a ≠ 0`, and `ENNReal`. -/
lemma mul_iInf_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * ⨅ i, f i = ⨅ i, a * f i :=
```

`Mathlib/Data/ENat/Lattice.lean` (lines 170–173):

```
/-- If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.
See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`. -/
lemma mul_iInf_of_ne (ha₀ : a ≠ 0) : a * ⨅ i, f i = ⨅ i, a * f i :=
```

Three defects, all from the same copy-paste:

1. **Wrong side.** The statement is `a * ⨅ i, f i = ⨅ i, a * f i`, i.e. *left* multiplication.
   Right multiplication is the neighbouring `iInf_mul_of_ne`, whose identical docstring is
   correct there.
2. **Cross-reference to the wrong-sided lemma.** The "see also" of the left lemma names
   `iInf_mul`, which is the `Nonempty ι` version of the *right* lemma; the intended target is
   `mul_iInf`. A reader following the pointer lands on a lemma that does not specialise to the
   one they are reading.
3. **Truncated sentence** (`ENNReal` only): the docstring ends with a dangling
   "`…, and `ENNReal`.`".

This is squarely "fixing what's broken": the docstring claims something the statement does not
say, and the diff removes the breakage without adding anything.

## The diff

Four changed lines, in `mathlib-docfix-mul_iInf_of_ne.patch`:

```diff
--- a/Mathlib/Data/ENNReal/Inv.lean
+++ b/Mathlib/Data/ENNReal/Inv.lean
-/-- If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum.
+/-- If `a ≠ 0` and `a ≠ ∞`, then left multiplication by `a` maps infimum to infimum.

-See `ENNReal.mul_iInf'` for the general case, and `ENNReal.iInf_mul` for another special case that
-assumes `Nonempty ι` but does not require `a ≠ 0`, and `ENNReal`. -/
+See `ENNReal.mul_iInf'` for the general case, and `ENNReal.mul_iInf` for another special case that
+assumes `Nonempty ι` but does not require `a ≠ 0`. -/
 lemma mul_iInf_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * ⨅ i, f i = ⨅ i, a * f i :=

--- a/Mathlib/Data/ENat/Lattice.lean
+++ b/Mathlib/Data/ENat/Lattice.lean
-/-- If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.
-See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`. -/
+/-- If `a ≠ 0`, then left multiplication by `a` maps infimum to infimum.
+See also `ENat.mul_iInf` that assumes `[Nonempty ι]` but does not require `a ≠ 0`. -/
 lemma mul_iInf_of_ne (ha₀ : a ≠ 0) : a * ⨅ i, f i = ⨅ i, a * f i :=
```

The patch applies cleanly to Mathlib at `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(`git apply mathlib-docfix-mul_iInf_of_ne.patch` from the Mathlib root).

## Evidence

`RequestProject/PR3.lean` compiles the whole claim rather than asserting it:

* eight `example`s fix the sidedness of `mul_iInf_of_ne`, `iInf_mul_of_ne`, `mul_iInf` and
  `iInf_mul` in both `ENNReal` and `ENat` — each elaborates only for the stated side, so
  "the docstrings are swapped" and "the cross-reference is wrong-sided" are checked, not claimed;
* three `#eval`s read the current docstrings out of the environment and fail unless they are
  character-for-character the text quoted above;
* two further `#eval`s apply the three edits to the docstring found in the environment and check
  that the result is exactly the replacement text recorded in the file, so the PR text and the
  patch cannot drift apart.

## Deliberately out of scope

Adjacent things noticed while checking, each a separate judgement call and none of them
unambiguous, so they are *not* in this PR:

* `ENNReal.mul_iInf`/`iInf_mul` describe `mul_iInf_of_ne`/`iInf_mul_of_ne` as "another special
  case that assumes `a ≠ 0`", omitting the `a ≠ ∞` hypothesis. Arguably imprecise, arguably
  deliberate brevity.
* `ENat.mul_iInf'`/`iInf_mul'` say "a version of `mul_iInf` with a slightly more general
  hypothesis" where the `ENNReal` file gives full "see also" paragraphs; harmonising them is a
  taste call.
* The maintainer TODO at `Data/ENNReal/Operations.lean:720` ("Prove the two one-side versions"
  of `exists_lt_add_of_lt_add`) is real work in the same area and a good candidate for a next
  PR, but it adds API rather than removing breakage.
