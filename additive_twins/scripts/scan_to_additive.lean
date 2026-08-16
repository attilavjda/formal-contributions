/-
Environment-level scanner for hand-written `to_additive` twins.

The pattern is the one described in `scripts/README.md`: a library contains a
multiplicative declaration and, next to it, its additive counterpart written out by hand,
where a `@[to_additive]` tag on the multiplicative one would have generated exactly that
declaration for free.

Instead of guessing from the source text, this scanner asks `to_additive` itself, for
every theorem `src` of the environment that is not already tagged:

* what *name* would it generate?          (`GuessName.guessName`)
* what *statement* would it generate?     (`applyReplacementForall`, the expression
  translation that `@[to_additive]` applies to the type of a tagged declaration)

If a hand-written declaration with that statement already exists in the same module, then
tagging `src` reproduces it, and the hand-written one is redundant.  Two passes:

* `auto`    -- the existing declaration is named exactly as `to_additive` would name it,
              so a bare `@[to_additive]` suffices;
* `renamed` -- the statement matches but the name does not, so the fix needs the explicit
              form `@[to_additive the_name]`.

Each hit is printed as

    CANDIDATE <module> <src> <tgt> <auto|renamed>

and the list is handed to `to_additive_twins.py --scan`, which decides every candidate by
really tagging the partner, really deleting the hand-written twin, rebuilding the file and
checking that the old statement still typechecks.  Nothing here is trusted: this scanner
only proposes.

Run with:  lake env lean scripts/scan_to_additive.lean
-/
import Mathlib

open Lean Meta Elab Command Mathlib.Tactic Mathlib.Tactic.Translate

namespace ToAdditiveScan

/-- `Thunk` is only `Inhabited` through a local instance in `Batteries`. -/
local instance [Inhabited α] : Inhabited (Thunk α) := ⟨.pure default⟩

/-- Theorems only, no internal/auxiliary declarations.  (Instances would match here too,
but for a `def` an agreeing *type* says very little, and the resulting list is noise:
`Polynomial.instMul` and `Polynomial.instAdd` have translated-equal types and nothing
whatsoever to do with each other.) -/
def interesting (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  (ci matches .thmInfo _) && !n.isInternalDetail &&
    !n.hasMacroScopes && !(isPrivateName n) && (env.getModuleIdxFor? n).isSome

/-- The name `to_additive` would generate for `n`, if it is different from `n`. -/
def guessTarget (n : Name) : Option Name :=
  match n with
  | .str pre s =>
    let tgt := pre.str (GuessName.guessName ToAdditive.data.guessNameData s)
    if tgt == n then none else some tgt
  | _ => none

/-- A cheap key that equal types have to share: the number of `∀`-binders and the head
constant of the conclusion.  Used to avoid quadratically many `isDefEq` calls. -/
partial def shape : Expr → Nat × Name
  | .forallE _ _ b _ => let (n, h) := shape b; (n + 1, h)
  | .mdata _ e => shape e
  | e => (0, e.getAppFn.constName?.getD .anonymous)

/-- Run `x` with a private heartbeat budget, returning `none` if it runs out or fails.
`tryCatchRuntimeEx` is what catches the deterministic timeout. -/
def try? (x : MetaM α) : MetaM (Option α) :=
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
      ({ · with maxHeartbeats := 40000 * 1000 }) do return some (← x))
    (fun _ => pure none)

/-- The type `to_additive` would give the translation of `ci`, with universe parameters
turned into metavariables (the two declarations name their universes independently). -/
def translatedType (d : TranslateData) (ci : ConstantInfo) : MetaM (Option Expr) :=
  try? do
    let ls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    return (← applyReplacementForall d [] (ci.instantiateTypeLevelParams ls)).1

/-- Is `ty` the type of `ci`?  `withReducible` keeps this a syntactic comparison: with
default transparency unrelated closed statements such as `0! = 1` and `1! = 1` would
count as equal. -/
def typeIs (ty : Expr) (ci : ConstantInfo) : MetaM Bool := do
  let some r ← try? do
    let ls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    withReducible <| isDefEq ty (ci.instantiateTypeLevelParams ls) | return false
  return r

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let env ← getEnv
  let d := ToAdditive.data
  -- everything `to_additive` already generates: such a declaration is not hand-written
  let generated : NameSet :=
    (SimplePersistentEnvExtension.getState d.translations env).get.foldl
      (fun s _ info => s.insert info.translation) ∅
  -- the hand-written, untagged theorems of each module
  let mut byModule : Std.HashMap Nat (Array (Name × ConstantInfo)) := ∅
  for (n, ci) in env.constants.toList do
    unless interesting env n ci do continue
    if (findTranslation? env d n).isSome || generated.contains n then continue
    let some m := env.getModuleIdxFor? n | continue
    byModule := byModule.insert m.toNat ((byModule.getD m.toNat #[]).push (n, ci))
  let mut hits : Array (Name × Name × Name × String) := #[]
  for (m, decls) in byModule.toList do
    if decls.size < 2 then continue
    let mut buckets : Std.HashMap (Nat × Name) (Array (Name × ConstantInfo)) := ∅
    for (n, ci) in decls do
      let k := shape ci.type
      buckets := buckets.insert k ((buckets.getD k #[]).push (n, ci))
    for (n, ci) in decls do
      -- necessary condition, and cheap: the statement mentions something translatable
      unless ci.type.foldConsts false
          (fun c b => b || (findTranslation? env d c).isSome) do continue
      let some ty ← translatedType d ci | continue
      if ← typeIs ty ci then continue          -- nothing in the statement was translated
      let mut best : Option (Name × String) := none
      for (tn, tci) in buckets.getD (shape ty) #[] do
        if tn == n then continue
        if best.isSome && guessTarget n != some tn then continue
        if ← typeIs ty tci then
          best := some (tn, if guessTarget n == some tn then "auto" else "renamed")
          if guessTarget n == some tn then break
      if let some (tn, how) := best then
        hits := hits.push (env.header.moduleNames[m]!, n, tn, how)
  for (m, n, t, how) in hits.qsort (fun a b => a.1.toString < b.1.toString) do
    logInfo m!"CANDIDATE {m} {n} {t} {how}"
  logInfo m!"-- {hits.size} candidate(s)"

end ToAdditiveScan
