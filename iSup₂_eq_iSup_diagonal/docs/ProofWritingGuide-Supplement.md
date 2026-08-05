# Supplement: Variability in Definitions, Comments, and Other Lean 4 Aspects

This companion to `ProofWritingGuide.md` covers the things that guide leaves out.
The original guide is almost entirely about **proofs** (the three proof styles,
proof strategies, the "knobs" you turn on a proof). This document covers the rest
of the language surface: how you write and vary **definitions**, how **binders /
`variable` declarations** work, the different **comment** forms, and a grab-bag of
other features (notation, attributes, visibility, commands, etc.).

---

## 1. Ways of Writing a Definition

A "definition" in Lean is far more varied than `def name : T := body`. Here are the
main forms, roughly from simplest to most structural.

### a) `def` — the workhorse

```lean
def double (n : ℕ) : ℕ := 2 * n
def double' : ℕ → ℕ := fun n => 2 * n   -- same thing, body as a lambda
```

The return type is optional (it is inferred), but stating it is good style:

```lean
def double'' (n : ℕ) := 2 * n
```

### b) `abbrev` — a *reducible* definition

`abbrev` is like `def` but marked `@[reducible]`, so the elaborator and `simp`
unfold it freely and typeclass search sees through it. Use it for thin aliases.

```lean
abbrev Nat.Pos := { n : ℕ // 0 < n }
abbrev MyVec := Fin 3 → ℝ
```

Trade-off: too many `abbrev`s slow elaboration and leak implementation details
into goals. Use `def` when you want the name to stay *opaque* unless explicitly unfolded.

### c) Definition by pattern matching

You can match directly on the arguments:

```lean
def isZero : ℕ → Bool
  | 0     => true
  | _ + 1 => false

def myAnd : Bool → Bool → Bool
  | true,  b => b
  | false, _ => false
```

### d) Recursive definitions (structural & well-founded)

Plain recursion is allowed; Lean compiles it via the equation compiler:

```lean
def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)
```

When recursion is **not** structurally decreasing, supply a measure with
`termination_by` and justify it with `decreasing_by`:

```lean
def gcd : ℕ → ℕ → ℕ
  | 0, y => y
  | x + 1, y => gcd (y % (x + 1)) (x + 1)
  termination_by x _ => x        -- the measure (params are in scope)
  decreasing_by omega            -- discharge the "measure decreases" goal

-- (Exact `termination_by` / `decreasing_by` spelling varies slightly across
--  Lean versions; check your toolchain's reference if the elaborator complains.)
```

### e) `partial` and `unsafe`

`partial def` opts out of termination checking — the function is treated as an
opaque constant for proving (you cannot unfold it in proofs), which is fine for
runtime code like parsers or interpreters. `unsafe def` additionally bypasses the
type-theoretic guarantees and is rarely needed.

```lean
partial def collatzSteps (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else if n % 2 = 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)
```

### f) `noncomputable`

When a definition depends on classical choice, real-number operations, or other
non-executable constructs, mark it `noncomputable` so Lean does not try to compile
it to runtime code:

```lean
noncomputable def myLimit (f : ℕ → ℝ) : ℝ := Classical.choose (someExistenceProof f)
```

### g) Local definitions inside a body

- `let` introduces a local binding (and remembers the value, so it can unfold).
- `have` introduces a local fact/value but **forgets** the value (used for
  proof-irrelevant data; it does not unfold).
- `where` attaches helper definitions *after* the main body.
- `let rec` defines a local recursive helper.

```lean
def f (n : ℕ) : ℕ :=
  let m := n + 1          -- local value, unfoldable
  go m
where
  go : ℕ → ℕ              -- helper visible only inside f
  | 0 => 0
  | k + 1 => k + go k
```

### h) `mutual` blocks

Definitions that refer to each other go in a `mutual ... end` block:

```lean
mutual
  def isEven : ℕ → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : ℕ → Bool
    | 0 => false
    | n + 1 => isEven n
end
```

### i) Type-forming definitions

These define new *types*, not just values:

- **`structure`** — a record with named fields (and automatically generated
  projections, constructor, and an `.mk` / anonymous-constructor `⟨…⟩` syntax).
- **`inductive`** — a freely generated datatype with constructors.
- **`class`** — a structure intended for typeclass resolution.
- **`instance`** — a member of a class (often anonymous).

```lean
structure Point where
  x : ℝ
  y : ℝ
  deriving Repr

inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

class HasNorm (α : Type) where
  norm : α → ℝ

instance : HasNorm Point where
  norm p := Real.sqrt (p.x ^ 2 + p.y ^ 2)
```

Structures support **default field values** and **field update syntax**:

```lean
structure Config where
  width  : ℕ := 80      -- default
  height : ℕ := 24

def wide : Config := { width := 200 }       -- height defaults to 24
def taller : Config := { wide with height := 50 }   -- record update
```

`extends` gives structure inheritance:

```lean
structure ColoredPoint extends Point where
  color : String
```

### j) `deriving`

Auto-generate instances (`Repr`, `DecidableEq`, `BEq`, `Inhabited`, `Hashable`, …):

```lean
inductive Color where
  | red | green | blue
  deriving Repr, DecidableEq, Inhabited
```

---

## 2. Binders and the `variable` Mechanism — Where "Variable Components" Live

This is the heart of "variable components of definitions." A *binder* tells Lean how
an argument is supplied. The four bracket styles:

| Syntax | Name | How it is supplied |
|---|---|---|
| `(x : T)` | explicit | You pass it positionally |
| `{x : T}` | implicit | Lean infers it by unification |
| `⦃x : T⦄` | strict (instance-)implicit | Inferred, but only once a later explicit arg pins it down |
| `[x : T]` or `[T]` | instance-implicit | Found by typeclass resolution |

```lean
def cast' {α β : Type} (h : α = β) (a : α) : β := h ▸ a   -- α, β inferred from a
def sum [Add α] [Zero α] (xs : List α) : α := xs.foldr (· + ·) 0  -- instances found automatically
```

### `variable` — factor shared binders out of many declarations

`variable` declares binders once; every following declaration that *uses* them gets
them prepended automatically (and only if it actually mentions them):

```lean
variable (G : Type) [Group G] (a b : G)

theorem mul_left_cancel' (h : a * b = a * c) : b = c := by
  -- G, the Group instance, a, b are all in scope here automatically
  ...
```

Variants:
- `variable {α : Type}` — implicit shared binder.
- `variable [DecidableEq α]` — shared instance binder.
- `variable (n : ℕ := 0)` — even default values are allowed.
- `variable {α} [Group α]` in a later block re-opens/extends scope.

### `universe` variables

Control universe polymorphism explicitly:

```lean
universe u v
def idType (α : Type u) : Type u := α
structure Sigma' {α : Type u} (β : α → Type v) where ...
```

Lean also has **auto-bound implicit**: a lowercase identifier used but not declared
(like `α` in `def f (xs : List α) := …`) is automatically added as an implicit binder.

### `autoParam` and `optParam` — arguments with defaults / tactics

- `optParam`: `(x : T := default)` gives an explicit argument a default value.
- `autoParam`: `(h : P := by tac)` fills the argument by running a tactic if omitted.

```lean
def greet (name : String := "world") : String := s!"hello {name}"
def safeDiv (a b : ℕ) (hb : b ≠ 0 := by omega) : ℕ := a / b
```

---

## 3. Comment Blocks

Lean has four distinct comment forms — only `--` and `/- -/` are "ordinary"
comments; the other two are *documentation* and are part of the tooling.

### a) Line comment `--`

```lean
def x := 1   -- everything after the dashes is ignored
```

### b) Block comment `/- ... -/` (nests!)

Unlike C, Lean block comments **nest**, so you can comment out code that already
contains block comments:

```lean
/- this is
   a multi-line comment
   /- and this nested one is fine -/
-/
```

### c) Declaration docstring `/-- ... -/`

Attached to the *following* declaration; shown on hover, in generated docs, and by
`#check`/`#print`. This is the right place to document what a definition/theorem means.

```lean
/-- `double n` returns twice `n`. -/
def double (n : ℕ) : ℕ := 2 * n
```

Docstrings support Markdown and inline math, and can be attached to `def`,
`theorem`, `structure`, fields, `class`, `inductive` constructors, etc.

### d) Module / section documentation `/-! ... -/`

A free-standing documentation block (not attached to any declaration) used for
section headers and file overviews; it shows up in the generated HTML docs.

```lean
/-!
# Group theory basics

This section develops cancellation lemmas.
-/
```

### e) Where comments matter for *this* workflow

Per the project conventions, prefer block-commenting `/- ... -/` to deleting
user-provided content you want to keep but exclude from elaboration, and use
docstrings (`/-- ... -/`) to record *why* a statement was modified.

---

## 4. Other Aspects Not in the Guide

### a) Namespaces, sections, and scoping

```lean
namespace Geometry
  def area (r : ℝ) : ℝ := Real.pi * r ^ 2   -- full name: Geometry.area
end Geometry

section Helpers           -- sections scope `variable`s and `open`s, not names
  variable (n : ℕ)
  ...
end Helpers
```

### b) `open` and its variants

Brings names into scope. Variants: `open Foo`, `open Foo (bar baz)` (selective),
`open Foo hiding qux`, `open scoped Foo` (only scoped notation/instances),
and the local `open Foo in <decl>`.

### c) Notation, infix, prefix, and macros

You can define new syntax:

```lean
infixl:65 " ⊕ " => myAdd                 -- left-assoc operator, precedence 65
notation:50 a " ≼ " b => myLe a b         -- general notation
prefix:75 "−" => myNeg

macro "trivial_arith" : tactic => `(tactic| (omega <;> simp))   -- a custom tactic
syntax (name := myStx) "foo" term : term  -- low-level syntax extension
```

`scoped notation` / `scoped infix` make notation available only when the namespace
is opened.

### d) Attributes `@[...]`

Modify how a declaration is treated:

```lean
@[simp] theorem my_lemma : 0 + n = n := Nat.zero_add n   -- add to simp set
@[reducible] def Alias := ActualType
@[ext] structure Foo where ...                           -- generate ext lemma
@[inline, specialize] def hot (x : ℕ) := ...
@[deprecated (since := "2024-01-01")] def old := ...
```

Attributes can also be applied after the fact: `attribute [simp] existing_lemma`.

### e) Visibility and modifiers

- `private def` — visible only in the current file/namespace.
- `protected def Foo.bar` — must be referred to as `Foo.bar` even when `Foo` is open.
- `local notation` / `local instance` — limited to the current section/file.

### f) `instance` priorities and `class`/`structure` distinctions

```lean
instance (priority := high) : Inhabited Bool := ⟨true⟩
```

### g) Helper *commands* for exploration (not part of the final proof term)

| Command | Purpose |
|---|---|
| `#check e` | Show the type of `e` |
| `#eval e` | Evaluate `e` (needs a computable / `Repr`-able value) |
| `#print foo` | Show the definition/axioms of `foo` |
| `#print axioms foo` | List axioms `foo` depends on (soundness audit) |
| `#reduce e` | Reduce `e` to normal form |
| `example : T := …` | An anonymous, unnamed declaration for testing |
| `#help tactic` / `#help option` | Built-in help |

### h) `set_option` — tweak elaboration behavior

```lean
set_option maxHeartbeats 400000 in
theorem slow_one : ... := by ...

set_option pp.all true in        -- verbose pretty-printing for debugging
#check foo
```

### i) `deriving`, `instance`-derivation, and `Decidable`

Auto-deriving `DecidableEq` lets `decide` work on your custom types; deriving `Repr`
lets `#eval` print them.

### j) `import` and `open` at file scope

`import` brings in whole modules (must appear at the top of the file, before any
declaration). It is coarser than `open`, which only adjusts name resolution.

---

## 5. A "Definition Design Space" (mirroring the guide's proof design space)

Just as a proof has axes of variation, so does a definition:

```
Form:         def ←—————→ abbrev ←—————→ structure/inductive/class
Computability:computable ←—————→ noncomputable ←—————→ partial/unsafe
Recursion:    none ←—————→ structural ←—————→ well-founded (termination_by)
Binders:      explicit (x:T) ←—————→ implicit {x} ←—————→ instance [C] / strict ⦃x⦄
Sharing:      repeated binders ←—————→ factored via `variable`
Generality:   concrete type ←—————→ universe-polymorphic, class-constrained
Defaults:     required args ←—————→ optParam / autoParam
Documentation:none ←—————→ `--` ←—————→ `/-- docstring -/` + `/-! module -/`
Visibility:   public ←—————→ protected ←—————→ private/local
```

Moving deliberately along these axes — e.g. turning a concrete `def` into a
class-polymorphic one, factoring repeated hypotheses into a `variable` block, or
adding docstrings and `@[simp]` — builds the same fluency the original guide
encourages for proofs.

---

## 6. Where to Read More

- **Theorem Proving in Lean 4** — chapters on *Inductive Types*, *Structures and
  Records*, *Type Classes*, and *Conv* cover definitions and binders in depth.
- **The Lean Language Reference** (`lean-lang.org/doc/reference/latest/`) — the
  authoritative description of `def`/`structure`/`inductive`, binders, attributes,
  notation, and commands.
- **Functional Programming in Lean** — the best source for `partial def`, `do`
  notation, monads, and writing *programs* (as opposed to proofs).
- **Metaprogramming in Lean 4** — for `macro`, `syntax`, `elab`, and custom
  attributes/commands.
