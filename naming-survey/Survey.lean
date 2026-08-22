/-
Naming survey of Mathlib.

Question studied: to what extent are the underscore-separated components of a
mathlib lemma name *exactly the names of definitions that occur in the
statement of that lemma*?

Method (fully mechanical, no hand curation):

* `defToks`  : lowercased last name-component of every non-theorem, non-axiom
               constant in the environment (definitions, structures, classes,
               inductives, projections, abbreviations) -- i.e. "the vocabulary
               of named definitions".
* for each mathlib theorem `T`:
  - `nameToks`  : the last component of `T`'s name, split at `_`;
  - `stmtToks`  : lowercased last name-component of every constant occurring in
                  the *statement* (type) of `T`.
  - each name token is then classified as
      GROUNDED  : it names a definition that occurs in the statement,
      ELSEWHERE : it names a definition of mathlib/core, but that definition
                  does not occur in this statement,
      FREE      : no definition of that name exists anywhere in the environment.
* Matching is case-insensitive, and also tries: dropping trailing subscript
  digits / primes (`iSup₂` ↦ `iSup`, `add'` ↦ `add`), and adding an `Is`
  prefix (`cofinal` ↦ `IsCofinal`).  Those two normalisations are counted
  separately so that their size can be seen.
* Auto-generated declarations (instances, `congr`/`hcongr`/`match` lemmas,
  equation lemmas, ...) are filtered out: they are not human-chosen names.
* Everything is also broken down per mathlib area (top-level directory), and a
  list of tokens of interest gets per-area examples.

Run with:  lake env lean naming-survey/Survey.lean > naming-survey/output.txt
-/
import Mathlib
open Lean

namespace NamingSurvey

def lastStr (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

def isMathlib (m : Name) : Bool := (`Mathlib).isPrefixOf m

/-- `Mathlib.Order.CompleteLattice.Basic ↦ Order`, `Mathlib.Data.Finset.X ↦ Data.Finset`. -/
def areaOf (m : Name) : String :=
  match m.components with
  | _ :: a :: rest =>
      if a.toString == "Data" || a.toString == "Algebra" then
        match rest with
        | b :: _ => a.toString ++ "." ++ b.toString
        | [] => a.toString
      else a.toString
  | _ => m.toString

def subChars : List Char := ['₀','₁','₂','₃','₄','₅','₆','₇','₈','₉','\'','!','?']

def stripSub (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => subChars.contains c)).reverse

def hasSub (s : String) : Bool := s != stripSub s

/-- names Lean generates automatically; they say nothing about human naming. -/
def autoGenLast : List String :=
  ["injEq", "sizeOf_spec", "noConfusion", "noConfusionType", "recOn", "casesOn",
   "below", "brecOn", "ndrec", "rec", "eq_def", "mk", "toCtorIdx", "sizeOf_eq",
   "induct", "fun_cases", "congr_simp", "eq_1", "eq_2", "eq_3", "eq_4"]

def isAutoGen (n : Name) : Bool :=
  let s := lastStr n
  autoGenLast.contains s
    || s.startsWith "inst" || s.startsWith "congr_" || s.startsWith "hcongr"
    || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_"
    || (s.toList.all Char.isDigit)
    || n.components.any (fun c => (lastStr c).startsWith "match_")

structure Bucket where
  count : Nat := 0
  examples : Array Name := #[]
deriving Inhabited

abbrev Tally := Std.HashMap String Bucket

def bump (t : Tally) (k : String) (ex : Name) (maxEx : Nat := 4) : Tally :=
  let b := t.getD k {}
  t.insert k { count := b.count + 1,
               examples := if b.examples.size < maxEx then b.examples.push ex else b.examples }

def top (t : Tally) (n : Nat) : Array (String × Bucket) :=
  let a := (t.toArray).qsort (fun x y => x.2.count > y.2.count)
  a.extract 0 (min n a.size)

def showTop (title : String) (t : Tally) (n : Nat) (withEx : Bool := true) : IO Unit := do
  IO.println ""
  IO.println s!"### {title}"
  IO.println ""
  for (k, b) in top t n do
    if withEx then
      IO.println s!"{b.count}\t{k}\t{b.examples.toList.map (·.toString)}"
    else
      IO.println s!"{b.count}\t{k}"

/-- tokens whose per-area usage we display individually. -/
def watch : List String :=
  ["self", "of", "diag", "diagonal", "cofinal", "aux", "comm", "assoc", "left",
   "right", "iff", "eq", "ne", "def", "apply", "two", "same", "cancel", "ext",
   "congr", "coe", "cast", "elim", "intro", "spec", "unique", "induction",
   "rec", "simp", "tfae", "swap", "symm", "trans", "refl", "id", "const"]

run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  -- 1. vocabulary of named definitions (whole environment, incl. core/batteries)
  let mut defToks : Std.HashSet String := {}
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail then continue
    match ci with
    | .thmInfo _ | .axiomInfo _ => pure ()
    | _ => defToks := defToks.insert (lastStr n).toLower
  IO.println s!"named-definition vocabulary size: {defToks.size}"

  -- 2. mathlib theorems, with their area
  let mut thms : Array (Name × String) := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if !isMathlib m then continue
    if (`Mathlib.Tactic).isPrefixOf m || (`Mathlib.Util).isPrefixOf m then continue
    let a := areaOf m
    for n in env.header.moduleData[i]!.constNames do
      if n.isInternalDetail || isAutoGen n then continue
      match env.find? n with
      | some (.thmInfo _) => thms := thms.push (n, a)
      | _ => pure ()
  IO.println s!"mathlib theorems analysed: {thms.size}"

  let mut nTok := 0
  let mut nGround := 0
  let mut nGroundExact := 0
  let mut nGroundSub := 0    -- grounded only after dropping ₂ / ' etc.
  let mut nGroundIs := 0     -- grounded only after adding an `Is` prefix
  let mut nElsewhere := 0
  let mut nFree := 0
  let mut namesAllGround := 0
  let mut namesSomeFree := 0
  let mut elsewhereT : Tally := {}
  let mut freeT : Tally := {}
  let mut groundT : Tally := {}
  let mut groundIsT : Tally := {}  -- grounded only after adding an `Is` prefix
  let mut groundSubT : Tally := {} -- grounded only after dropping ₂ / '
  let mut subT : Tally := {}      -- tokens carrying a subscript/prime
  let mut subFreeT : Tally := {}  -- ... whose full form is not a definition
  -- per area: (#tokens, #grounded, #elsewhere, #free)
  let mut areaStats : Std.HashMap String (Nat × Nat × Nat × Nat) := {}
  let mut areaFree : Std.HashMap String Tally := {}
  let mut areaElse : Std.HashMap String Tally := {}
  -- per (watched token, area) examples
  let mut watchT : Std.HashMap String Tally := {}
  for (th, area) in thms do
    let some (.thmInfo ti) := env.find? th | continue
    let mut stmt : Std.HashSet String := {}
    for c in ti.type.getUsedConstants do
      stmt := stmt.insert (lastStr c).toLower
    let toks := ((lastStr th).splitOn "_").filter (· != "")
    let mut allG := true
    let mut someF := false
    let (a0, a1, a2, a3) := areaStats.getD area (0,0,0,0)
    let mut st := (a0, a1, a2, a3)
    for tok0 in toks do
      let tok := tok0.toLower
      nTok := nTok + 1
      st := (st.1 + 1, st.2.1, st.2.2.1, st.2.2.2)
      if hasSub tok then
        subT := bump subT tok th
        if !defToks.contains tok then subFreeT := bump subFreeT tok th
      let s := stripSub tok
      let grounded :=
        stmt.contains tok || stmt.contains s || stmt.contains ("is" ++ tok) || stmt.contains ("is" ++ s)
      if watch.contains tok then
        let t := watchT.getD tok {}
        watchT := watchT.insert tok
          (bump t (area ++ (if grounded then " [in stmt]" else " [not in stmt]")) th (maxEx := 3))
      if stmt.contains tok then
        nGround := nGround + 1; nGroundExact := nGroundExact + 1
        groundT := bump groundT tok th
        st := (st.1, st.2.1 + 1, st.2.2.1, st.2.2.2)
      else if stmt.contains s then
        nGround := nGround + 1; nGroundSub := nGroundSub + 1
        groundT := bump groundT tok th
        groundSubT := bump groundSubT tok th
        st := (st.1, st.2.1 + 1, st.2.2.1, st.2.2.2)
      else if stmt.contains ("is" ++ tok) || stmt.contains ("is" ++ s) then
        nGround := nGround + 1; nGroundIs := nGroundIs + 1
        groundT := bump groundT tok th
        groundIsT := bump groundIsT tok th
        st := (st.1, st.2.1 + 1, st.2.2.1, st.2.2.2)
      else if defToks.contains tok || defToks.contains s || defToks.contains ("is" ++ tok) then
        nElsewhere := nElsewhere + 1; allG := false
        elsewhereT := bump elsewhereT tok th
        areaElse := areaElse.insert area (bump (areaElse.getD area {}) tok th (maxEx := 3))
        st := (st.1, st.2.1, st.2.2.1 + 1, st.2.2.2)
      else
        nFree := nFree + 1; allG := false; someF := true
        freeT := bump freeT tok th
        areaFree := areaFree.insert area (bump (areaFree.getD area {}) tok th (maxEx := 3))
        st := (st.1, st.2.1, st.2.2.1, st.2.2.2 + 1)
    areaStats := areaStats.insert area st
    if allG then namesAllGround := namesAllGround + 1
    if someF then namesSomeFree := namesSomeFree + 1

  IO.println ""
  IO.println "## token-level"
  IO.println s!"name tokens total          : {nTok}"
  IO.println s!"GROUNDED (def in statement): {nGround}  ({nGround * 100 / nTok}%)"
  IO.println s!"  of which exact match     : {nGroundExact}"
  IO.println s!"  only after ₂/' stripping : {nGroundSub}"
  IO.println s!"  only after Is-prefixing  : {nGroundIs}"
  IO.println s!"ELSEWHERE (def, not here)  : {nElsewhere}  ({nElsewhere * 100 / nTok}%)"
  IO.println s!"FREE (no definition at all): {nFree}  ({nFree * 100 / nTok}%)"
  IO.println ""
  IO.println "## name-level"
  IO.println s!"names all of whose tokens are grounded: {namesAllGround}  ({namesAllGround * 100 / thms.size}%)"
  IO.println s!"names with >=1 FREE token             : {namesSomeFree}  ({namesSomeFree * 100 / thms.size}%)"

  showTop "most frequent FREE tokens (no definition of that name exists)" freeT 120
  showTop "most frequent ELSEWHERE tokens (a definition of that name exists, but not in the statement)" elsewhereT 80
  showTop "most frequent GROUNDED tokens" groundT 60 (withEx := false)
  showTop "tokens carrying a subscript / prime" subT 60 (withEx := false)
  showTop "subscripted tokens that are not themselves definitions" subFreeT 60
  showTop "tokens matching a statement definition only after dropping the subscript/prime" groundSubT 40
  showTop "tokens matching a statement definition only after adding an `Is` prefix" groundIsT 40

  IO.println ""
  IO.println "## per-area statistics (tokens: grounded / elsewhere / free)"
  IO.println ""
  let areas := (areaStats.toArray).qsort (fun x y => x.2.1 > y.2.1)
  for (a, (tot, g, e, f)) in areas do
    if tot < 300 then continue
    IO.println s!"{a}\ttokens={tot}\tgrounded={g * 100 / tot}%\telsewhere={e * 100 / tot}%\tfree={f * 100 / tot}%"

  IO.println ""
  IO.println "## per-area FREE tokens (top 8 per area)"
  for (a, _) in areas do
    if (areaStats.getD a (0,0,0,0)).1 < 300 then continue
    IO.println ""
    IO.println s!"#### {a}"
    for (k, b) in top (areaFree.getD a {}) 8 do
      IO.println s!"  {b.count}\t{k}\t{b.examples.toList.map (·.toString)}"

  IO.println ""
  IO.println "## per-area ELSEWHERE tokens (top 6 per area)"
  for (a, _) in areas do
    if (areaStats.getD a (0,0,0,0)).1 < 300 then continue
    IO.println ""
    IO.println s!"#### {a}"
    for (k, b) in top (areaElse.getD a {}) 6 do
      IO.println s!"  {b.count}\t{k}\t{b.examples.toList.map (·.toString)}"

  IO.println ""
  IO.println "## watched tokens, per area, split by whether the token is realised in the statement"
  for w in watch do
    IO.println ""
    IO.println s!"### token `{w}`"
    for (k, b) in top (watchT.getD w {}) 24 do
      IO.println s!"  {b.count}\t{k}\t{b.examples.toList.map (·.toString)}"

end NamingSurvey
