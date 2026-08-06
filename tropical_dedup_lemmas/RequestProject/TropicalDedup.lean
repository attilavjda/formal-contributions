/-
Verification supporting a proposed Mathlib cleanup:
`Mathlib/Algebra/Tropical/Basic.lean` contains five pairs of lemmas whose statements are
*literally the same term*, so each pair can be collapsed to a single lemma plus a deprecated alias.
-/
import Mathlib.Algebra.Tropical.Basic

namespace TropicalDedupCheck

open Tropical

/-!
### Each pair has an identical statement

For each pair below, the two constants have the same type up to nothing at all: the `rfl`
type-ascription checks that the statement of one is syntactically the statement of the other
(`⊓`/`⊔` on a `LinearOrder` *are* `min`/`max` in current Mathlib), and the `rfl` proof checks
that the two constants are interchangeable.
-/

theorem trop_inf_eq_trop_min : @Tropical.trop_inf = @Tropical.trop_min := rfl

theorem trop_sup_def_eq_trop_max_def : @Tropical.trop_sup_def = @Tropical.trop_max_def := rfl

theorem untrop_sup_eq_untrop_max : @Tropical.untrop_sup = @Tropical.untrop_max := rfl

theorem injective_trop_eq_trop_injective : @Tropical.injective_trop = @Tropical.trop_injective := rfl

theorem injective_untrop_eq_untrop_injective :
    @Tropical.injective_untrop = @Tropical.untrop_injective := rfl

/-- `Tropical.inf_eq_add` is `Tropical.min_eq_add` up to eta. -/
theorem inf_eq_add_eq_min_eq_add : @Tropical.inf_eq_add = @Tropical.min_eq_add := rfl

/-!
### No API is lost

The statement of each lemma that the cleanup removes is proved verbatim by the lemma that is kept.
-/

theorem trop_inf' {R : Type*} [LinearOrder R] (x y : R) : trop (x ⊓ y) = trop x + trop y :=
  trop_min x y

theorem trop_sup_def' {R : Type*} [LinearOrder R] (x y : Tropical R) :
    x ⊔ y = trop (untrop x ⊔ untrop y) :=
  trop_max_def x y

theorem untrop_sup' {R : Type*} [LinearOrder R] (x y : Tropical R) :
    untrop (x ⊔ y) = untrop x ⊔ untrop y :=
  untrop_max x y

theorem inf_eq_add' {R : Type*} [LinearOrder R] :
    ((· ⊓ ·) : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  min_eq_add

theorem injective_trop' {R : Type*} : Function.Injective (trop : R → Tropical R) :=
  trop_injective

theorem injective_untrop' {R : Type*} : Function.Injective (untrop : Tropical R → R) :=
  untrop_injective

end TropicalDedupCheck
