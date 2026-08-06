# A tiny pure-deduplication contribution to Mathlib

**Target file:** `Mathlib/Algebra/Tropical/Basic.lean` (Mathlib at commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, the version pinned by this project)

**Suggested PR title:** `chore(Algebra/Tropical/Basic): deduplicate five pairs of identical lemmas`

**Effect of the diff:** 17 lines removed, 8 added (net −9), three redundant `@[simp]` lemmas
gone, no API lost — every removed name survives as a deprecated alias.

## What is redundant

`Mathlib/Algebra/Tropical/Basic.lean` states five pairs of lemmas whose statements are not merely
equivalent but *the same term*. Two independent causes:

1. **`⊓`/`⊔` versus `min`/`max`.** In current Mathlib the lattice operations on a `LinearOrder`
   are `Min.min`/`Max.max`, and `x ⊓ y` elaborates to exactly `min x y`. So the four lemmas
   `trop_inf`, `untrop_sup`, `inf_eq_add`, `trop_sup_def` have statements identical to
   `trop_min`, `untrop_max`, `min_eq_add`, `trop_max_def` respectively (`inf_eq_add` differs from
   `min_eq_add` only by eta). Three of these pairs are pairs of `@[simp]` lemmas, i.e. `simp` is
   carrying a second copy of a rule that can never do anything the first copy does not.

2. **Two spellings of injectivity.** `trop_injective` / `untrop_injective` (`fun _ _ => id`) and
   `injective_trop` / `injective_untrop` (via `tropEquiv`) are the same statements proved twice,
   fifty lines apart in the same file. `_injective` is the Mathlib naming convention, so those
   are the copies to keep.

| removed (kept as deprecated alias) | kept |
| --- | --- |
| `Tropical.trop_inf` (`@[simp]`) | `Tropical.trop_min` (`@[simp]`) |
| `Tropical.untrop_sup` (`@[simp]`) | `Tropical.untrop_max` (`@[simp]`) |
| `Tropical.inf_eq_add` (`@[simp]`) | `Tropical.min_eq_add` (`@[simp]`) |
| `Tropical.trop_sup_def` | `Tropical.trop_max_def` |
| `Tropical.injective_trop` | `Tropical.trop_injective` |
| `Tropical.injective_untrop` | `Tropical.untrop_injective` |

Choosing the `min`/`max` spellings as the survivors matches the rest of the file, whose whole API
(`untrop_add`, `trop_add_def`, `min_eq_add`, …) is phrased with `min`; the lattice-notation
material about `Tropical` lives in `Mathlib/Algebra/Tropical/Lattice.lean`.

## The diff

The patch is in [`tropical-dedup.patch`](tropical-dedup.patch); apply with
`git apply tropical-dedup.patch` from a Mathlib checkout.

Only one call site inside Mathlib had to be updated
(`decidable_of_iff _ injective_untrop.eq_iff` → `untrop_injective.eq_iff`); no other file in
Mathlib mentions any of the removed names.

## Verification performed

* **Statements really are identical.** `RequestProject/TropicalDedup.lean` proves
  `@Tropical.trop_inf = @Tropical.trop_min` and the analogous equations for all six pairs by
  `rfl`; these only typecheck because the two constants have literally the same type.
* **No API is lost.** The same file restates each removed lemma verbatim and proves it by the
  retained lemma alone.
* **Mathlib still builds.** With the patch applied, `Mathlib.Algebra.Tropical.Basic`,
  `Mathlib.Algebra.Tropical.Lattice` and `Mathlib.Algebra.Tropical.BigOperators` (the only
  modules importing this material) compile with no errors and no deprecation warnings.

## How the opportunity was found

`scripts/find_duplicate_statements.lean` walks the whole imported environment, normalizes binder
names in every theorem's type, and groups theorems by that normalized statement; the resulting
list (`dups.txt`) is filtered to groups whose members are all ordinary, non-deprecated, non-`alias`
Mathlib declarations. `Tropical/Basic.lean` stood out as a single small file contributing five
such groups.
