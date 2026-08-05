# Companion: Point-Free Style and Related Patterns in Lean 4

This companion to `ProofWritingGuide.md` and `ProofWritingGuide-Supplement.md`
zooms in on one stylistic axis that the others only touch: **how you express
functions and combine them**. The headline topic is **point-free (tacit) style** —
writing functions by *composing* other functions instead of naming their
arguments — together with the family of "similar and different" patterns that
sit next to it: operator sections, pipelines, combinators, and the
monadic/applicative styles.

All Lean snippets below were checked to elaborate against Mathlib.

---

## 1. What "Point-Free" Means

A function is written in **pointful** (a.k.a. *pointed*) style when it names its
argument(s) — the "points" — and an expression involving them:

```lean
def addThenDouble' (n : ℕ) : ℕ := (n + 1) * 2   -- pointful: names `n`
```

It is written in **point-free** (a.k.a. *tacit*) style when it is built purely by
combining other functions, with no argument named:

```lean
def addThenDouble : ℕ → ℕ := (· * 2) ∘ (· + 1)   -- point-free
```

These two are *definitionally equal* — Lean accepts the proof by `rfl`:

```lean
example : addThenDouble = addThenDouble' := rfl
```

The point-free version reads "right to left": first add one, then double.
The trade-off is exactly that: point-free can be elegantly compositional, but
deeply nested compositions become hard to read ("point-free" is sometimes called
"point-*less*" for this reason). Use it where it clarifies, not as a sport.

---

## 2. The Building Blocks of Point-Free Style

### a) Function composition `∘` (`Function.comp`)

`f ∘ g` is "do `g`, then `f`". It unfolds definitionally:

```lean
example (f : β → γ) (g : α → β) (x : α) : (f ∘ g) x = f (g x) := rfl
```

Composition is associative and has `id` as a unit — all by `rfl`, and also
available as named Mathlib lemmas for rewriting:

```lean
example (f : γ → δ) (g : β → γ) (h : α → β) : (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

#check @Function.comp_assoc   -- (f ∘ g) ∘ h = f ∘ g ∘ h
#check @Function.id_comp      -- id ∘ f = f
#check @Function.comp_id      -- f ∘ id = f
```

### b) The cdot `·` — operator sections

The `·` placeholder turns an expression into an anonymous function; each `·`
becomes a fresh argument, and the enclosing parentheses delimit the lambda. This
is the most common, lightweight way to get point-free-*ish* code:

```lean
#check (· + 1)     -- fun x => x + 1   : ℕ → ℕ
#check (2 ^ ·)     -- fun x => 2 ^ x
#check (· + ·)     -- fun x y => x + y  (two placeholders → two args)
#check (· ∈ s)     -- membership predicate, fun x => x ∈ s
```

Caveat on scope: the *parentheses* are the boundary of the `·`-lambda, so
`(· + 1, · + 2)` is **one** function returning a pair, not a pair of functions.
When in doubt, fall back to an explicit `fun`.

### c) The combinators: `id`, `Function.const`, `flip`, `Function.swap`

These are the classic point-free glue:

```lean
#check @id                -- {α} → α → α
#check @Function.const    -- {α} → (β) → α → β → α   : ignore the second arg
#check @flip              -- (α → β → φ) → β → α → φ  : swap the two arguments
#check @Function.swap     -- dependent version of flip

example : flip (· - ·) (1 : ℤ) 5 = 4 := rfl       -- 5 - 1
example : Function.const ℕ 7 = (fun _ : ℕ => 7) := rfl
```

`Function.const β a` is the function that ignores its `β`-argument and always
returns `a` — the point-free way to say "a constant function".

### d) `curry` / `uncurry` — moving between `a → b → c` and `a × b → c`

```lean
#check @Function.curry     -- (α × β → φ) → α → β → φ
#check @Function.uncurry   -- (α → β → φ) → α × β → φ

example (f : α → β → γ) : Function.uncurry f = fun p => f p.1 p.2 := rfl
```

These let you adapt a function's *shape* without naming its arguments — handy
when feeding a binary function to something that expects a single pair argument
(or vice versa).

---

## 3. Point-Free in the Wild: Higher-Order Functions

Point-free style shines when passing functions to `map`, `filter`, `foldr`, etc.,
because you avoid a throwaway lambda:

```lean
example : [1, 2, 3].map (· + 1) = [2, 3, 4] := rfl
#check List.map (· + 1)
#check List.filter (· % 2 == 0)
```

A whole transformation can be assembled by composition:

```lean
def process : List ℕ → ℕ :=
  List.sum ∘ List.map (· * 2) ∘ List.filter (· % 2 == 0)
```

Compare the pointful equivalent — same result, different readability trade-off:

```lean
def process' (xs : List ℕ) : ℕ :=
  (xs.filter (· % 2 == 0) |>.map (· * 2)).sum
```

---

## 4. A Different but Related Pattern: Pipelines (`|>`, `<|`, `|>.`)

Pipelines are the *pointful*, left-to-right cousin of point-free composition.
Instead of building a function, you thread a **value** through stages:

```lean
#eval (3 |> (· + 1) |> (· * 2))        -- 8   : "3, then +1, then *2"
#eval [1, 2, 3].map (· + 1) |>.sum     -- 9   : method-pipeline `|>.`
```

The mirror operators:

- `x |> f` is `f x` (forward application).
- `f <| x` is `f x` (backward application — removes trailing parentheses).
- `x |>.foo` is `(x).foo` — chains *dot-methods* left to right.

```lean
example (f : ℕ → ℕ) (x : ℕ) : (x |> f) = f x := rfl
example (f : ℕ → ℕ) (x : ℕ) : (f <| x) = f x := rfl
```

Rule of thumb: **composition (`∘`)** combines *functions* and reads right-to-left;
**pipelines (`|>`)** combine *computations on a value* and read left-to-right.
Many people find pipelines easier to read than long `∘` chains for data
transformations, and reserve `∘` for short, genuinely function-level glue.

---

## 5. Another Relative: Functor / Applicative / Monadic Style

When the values live in a context (`Option`, `List`, `Except`, `IO`, …), three
more "combine without writing the plumbing" styles appear.

### a) Functor map `<$>`

```lean
#eval (· + 1) <$> some 3        -- some 4
```

### b) Applicative `<*>` — apply a wrapped function to wrapped arguments

```lean
#eval (· + ·) <$> some 3 <*> some 4   -- some 7
```

### c) Monadic `do` — the pointful, imperative-looking style

`do` notation is the readable, *named-intermediate* counterpart to dense
applicative chains:

```lean
def safeDivAll (xs : List ℕ) : Option (List ℕ) := do
  let ys ← xs.mapM (fun x => if x = 0 then none else some (100 / x))
  pure ys
```

### d) Kleisli composition `>=>` — point-free for *monadic* functions

Just as `∘` composes plain functions, `>=>` composes functions returning a monad
(`a → m b` then `b → m c`), with no argument named:

```lean
#check (· >=> ·)   -- (α → m β) → (β → m γ) → α → m γ
```

---

## 6. Point-Free Style *in Proofs*

The same idea applies to proof terms, where it can be very compact.

### a) Eta / composition at the term level

A proof of `P → R` from `P → Q` and `Q → R` is literally function composition:

```lean
example (h1 : P → Q) (h2 : Q → R) : P → R := h2 ∘ h1
```

### b) Combinator-style term proofs

```lean
example (P : Prop) : P → P := id
example (h : Q) : P → Q := Function.const P h    -- ignore the P-proof, return h
```

### c) Unfolding composition during tactic proofs

When a `∘` blocks a goal, `simp` / `Function.comp` lemmas or `ext` clear it:

```lean
example (f g : ℕ → ℕ) : (f ∘ g) ∘ id = f ∘ g := by
  ext x; simp
```

Useful rewriting lemmas: `Function.comp_apply` (`(f ∘ g) x = f (g x)`),
`Function.comp_id`, `Function.id_comp`, `Function.comp_assoc`.

---

## 7. When to Prefer Each Style

| Goal | Prefer | Why |
|---|---|---|
| Short glue of 2–3 functions | `∘` / cdot sections | Compact, reads as a single pipeline |
| Longer data transformation | `\|>` pipelines | Left-to-right reads like a recipe |
| Passing a one-off function | `(· op ·)` section | Avoids a noisy `fun` lambda |
| Constant / argument-ignoring fn | `Function.const` | States intent directly |
| Swapping argument order | `flip` / `Function.swap` | No need to re-bind arguments |
| Reshaping arity | `curry` / `uncurry` | Adapt to an API without lambdas |
| Effectful sequencing | `do` notation | Named steps beat dense `<*>` chains |
| Composing effectful functions | `>=>` | The monadic analogue of `∘` |
| Anything that gets *unreadable* | explicit `fun x => …` | Clarity beats cleverness |

**The central trade-off:** point-free style removes *naming noise* but also removes
*names you can hover over and reason about*. It is at its best for small, total,
genuinely compositional pieces, and at its worst for long chains where the reader
has to mentally re-introduce the arguments anyway.

---

## 8. A "Combination Style" Design Space

Mirroring the design-space diagrams in the other two guides, the way you *combine*
functions has its own axes:

```
Argument naming:   pointful (fun x => …) ←————→ point-free (∘, combinators)
Reading direction: right-to-left (∘) ←————→ left-to-right (|>, do)
Lambda weight:     full `fun x =>` ←————→ cdot section (· + 1) ←————→ none (id/flip)
Effect handling:   pure (∘) ←————→ functor (<$>) ←————→ applicative (<*>) ←————→ monad (do, >=>)
Arity shape:       curried (a→b→c) ←————→ uncurried (a×b→c)
Optimization:      readability ←————→ conciseness
```

As with proofs, the exercise that builds fluency is **rewriting the same function
along an axis**: take a pointful `def`, make it point-free with `∘` and cdot
sections; then rewrite it as a `|>` pipeline; then, if it is effectful, as a `do`
block. Seeing the same logic in each form is the fastest way to learn when each
one earns its keep.

---

## 9. Where to Read More

- **Functional Programming in Lean** — the best source for `do` notation, functors,
  applicatives, monads, and the `<$>` / `<*>` / `>=>` operators.
- **Theorem Proving in Lean 4** — the chapter on functions and the discussion of
  `fun`, `id`, and composition underpins the term-level point-free proofs.
- **The Lean Language Reference** (`lean-lang.org/doc/reference/latest/`) — the
  authoritative description of the `·` notation, `|>` / `<|` pipelines, and
  `Function.comp` / `flip` / `const`.
- **Mathlib's `Mathlib/Logic/Function/Basic.lean`** — the home of `Function.comp`,
  `Function.const`, `flip`, `Function.swap`, `curry`/`uncurry`, and their lemmas.
