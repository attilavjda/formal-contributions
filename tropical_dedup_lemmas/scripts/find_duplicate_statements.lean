import Mathlib
import Lean

open Lean Meta Elab

/-- Normalize binder names so that alpha-equivalent statements compare equal. -/
partial def norm (e : Expr) : Expr :=
  match e with
  | .forallE _ t b bi => .forallE `x (norm t) (norm b) bi
  | .lam _ t b bi => .lam `x (norm t) (norm b) bi
  | .letE _ t v b nd => .letE `x (norm t) (norm v) (norm b) nd
  | .app f a => .app (norm f) (norm a)
  | .mdata _ b => norm b
  | .proj s i b => .proj s i (norm b)
  | e => e

def isBad (n : Name) : Bool :=
  n.isInternal ||
  (n.components.any fun c =>
    let s := c.toString
    s.startsWith "proof_" || s.startsWith "match_" || s == "eq_def" || s == "sizeOf_spec"
      || s == "injEq" || s == "noConfusionType" || s == "rec" || s == "recOn" || s == "below"
      || s == "brecOn" || s == "ndrec" || s == "casesOn" || s == "ofNat_toCtorIdx")

set_option maxHeartbeats 0 in
run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut m : Std.HashMap Expr (Array (Name × Name)) := {}
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo v =>
      if isBad n then continue

      let some mod := env.getModuleFor? n | continue
      unless (`Mathlib).isPrefixOf mod do continue
      if (Lean.Linter.deprecatedAttr.getParam? env n).isSome then continue
      let k := norm v.type
      m := m.insert k ((m.getD k #[]).push (n, mod))
    | _ => pure ()
  let mut out : Array String := #[]
  for (_, ns) in m do
    if ns.size ≥ 2 then
      out := out.push (String.intercalate " | " (ns.toList.map fun (n, mod) => s!"{n}@{mod}"))
  IO.FS.writeFile "dups.txt" (String.intercalate "\n" out.toList)
  logInfo s!"groups: {out.size}"
