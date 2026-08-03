import Mathlib

/-!
# Machine-checked backing for a Category 3 (decidability bridge) candidate

`Mathlib/Algebra/Group/Center.lean:213` carries the explicit TODO

```
-- TODO Add `instance : Decidable (IsMulCentral a)` for `instance decidableMemCenter [Mul M]`
```

At commit `8f9d9cff` (tag `v4.28.0`) a ripgrep of `Mathlib/` finds **no**
`Decidable (Commute _ _)`, no `Decidable (IsMulCentral _)`, and no `Fintype`-based
`DecidablePred (· ∈ Set.center M)`; the only `decidableMemCenter` instance carries the
awkward hypothesis `[∀ a : M, Decidable <| ∀ b : M, b * a = a * b]`.

This file discharges that TODO. Everything below compiles with no `sorry`/`admit`, and
each declaration carries a `to_additive` twin (auto-generated), so the additive side of
the API (`AddCommute`, `IsAddCentral`, `Set.addCenter`) comes for free.

Leverage: `IsMulCentral`/`Commute` are foundational predicates used across the group,
ring, and centralizer APIs. Giving them a `Decidable` instance from `Fintype`+`DecidableEq`
alone lets `decide`/`native_decide` (and instance synthesis for `Fintype (center M)` etc.)
close membership-in-the-center goals that currently require the hand-supplied decidability
hypothesis, and it strictly widens the applicability of `decidableMemCenter`.
-/

namespace HighLeverage

/-- `Commute a b` (i.e. `a * b = b * a`) is decidable whenever equality is. -/
@[to_additive /-- `AddCommute a b` (i.e. `a + b = b + a`) is decidable whenever equality is. -/]
instance decidableCommute {M : Type*} [Mul M] [DecidableEq M] (a b : M) :
    Decidable (Commute a b) := by
  unfold Commute SemiconjBy; infer_instance

/-- The missing instance requested by the TODO in `Mathlib/Algebra/Group/Center.lean`:
being multiplicatively central is decidable for a finite type with decidable equality.
The three defining conditions of `IsMulCentral` are universally quantified equalities
(via `Commute`), each decidable over a `Fintype`. -/
@[to_additive /-- Being additively central is decidable for a finite type with decidable equality. -/]
instance decidableIsMulCentral {M : Type*} [Mul M] [Fintype M] [DecidableEq M] (z : M) :
    Decidable (IsMulCentral z) :=
  decidable_of_iff' _ (isMulCentral_iff z)

/-- Downstream payoff: membership in `Set.center M` becomes decidable from `Fintype` and
`DecidableEq` alone, without the bespoke decidability hypothesis carried by the current
`decidableMemCenter`. -/
@[to_additive decidableMemAddCenterFintype /-- Membership in `Set.addCenter M` is decidable from `Fintype` and `DecidableEq` alone. -/]
instance decidableMemCenterFintype {M : Type*} [Mul M] [Fintype M] [DecidableEq M] :
    DecidablePred (· ∈ Set.center M) :=
  fun _ => decidable_of_iff' _ Set.mem_center_iff

end HighLeverage
