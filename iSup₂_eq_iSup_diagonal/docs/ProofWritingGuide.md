# A Guide to Approaches, Variability, and Patterns in Lean 4 Proofs

## 1. The Three Fundamental Proof Styles

Every Lean proof can be written in one of three fundamentally different styles — and often in combinations of them.

### a) **Tactic Mode** (`by ...`)
The most common style for beginners. You enter an interactive "goal state" and transform it step by step.

```lean
theorem add_comm_example (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero => simp
  | succ k ih => simp [Nat.succ_add, ih]
```

### b) **Term Mode** (direct proof terms)
You write the proof as a single expression — like writing a program that has the proposition as its type.

```lean
theorem add_zero (n : ℕ) : n + 0 = n :=
  Nat.rec rfl (fun k ih => congrArg Nat.succ ih) n
```

### c) **Structured Proof / Calculus Style** (`calc`, `show`, `have`, `suffices`)
A middle ground that reads more like a textbook proof.

```lean
theorem triangle (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  calc a ≤ b := h1
    _ ≤ c := h2
```

**Key insight:** These are freely mixable. You can use `have` inside `by` blocks, drop into term mode from tactic mode with `exact`, or enter tactic mode from term mode with `by`.

---

## 2. Approaches to Writing Any Given Proof

Here are the major proof *strategies* — the mathematical "how do I get from A to B":

| Approach | When to Use | Key Tactics/Constructs |
|---|---|---|
| **Direct proof** | The result follows from definitions and simple reasoning | `intro`, `exact`, `apply`, `rfl` |
| **Rewriting / Simplification** | Goal involves equations or known identities | `rw`, `simp`, `ring`, `norm_num` |
| **Case analysis** | Result depends on which of finitely many cases holds | `cases`, `rcases`, `match`, `split`, `by_cases` |
| **Induction** | Property of naturals, lists, or recursive structures | `induction`, `Nat.rec`, `strong induction` |
| **Contradiction** | Easier to show the negation leads to absurdity | `by_contra`, `absurd`, `exfalso` |
| **Contrapositive** | Proving `¬Q → ¬P` is easier than `P → Q` | `contrapose` |
| **Forward reasoning** | Build up facts until the goal becomes trivial | `have h := ...`, `obtain ⟨x, hx⟩ := ...` |
| **Backward reasoning** | Reduce the goal to simpler subgoals | `apply`, `suffices`, `refine` |
| **Construction / witness** | Existential goal — need to provide an example | `use`, `exact ⟨..., ...⟩`, `refine ⟨?_, ?_⟩` |
| **Calculation chains** | Step-by-step equalities or inequalities | `calc`, `gcongr`, `linarith`, `omega` |

### How to Decide Which Approach to Use

Ask yourself these questions in order:

1. **What is the shape of the goal?**
   - `∀ x, ...` → Use `intro x`
   - `∃ x, ...` → Use `use` (you need to supply a witness)
   - `P ∧ Q` → Use `constructor` (prove both halves)
   - `P ∨ Q` → Use `left` or `right` (pick a side)
   - `P ↔ Q` → Use `constructor` (prove both directions)
   - `P → Q` → Use `intro h` (assume P, prove Q)
   - `¬P` → This is `P → False`, so use `intro h`
   - `a = b` → Try `rfl`, `ring`, `simp`, `omega`, `norm_num`, or `rw`
   - `a ≤ b` or `a < b` → Try `omega`, `linarith`, `norm_num`, or `gcongr`

2. **What hypotheses do I have?**
   - `h : P ∧ Q` → Use `obtain ⟨hp, hq⟩ := h` or `h.1`, `h.2`
   - `h : P ∨ Q` → Use `cases h` (handle both branches)
   - `h : ∃ x, ...` → Use `obtain ⟨x, hx⟩ := h`
   - `h : a = b` → Use `rw [h]` or `subst h`
   - `h : False` → Use `exact h.elim` or `contradiction`

3. **Is there recursion or a natural number involved?** → Consider `induction` or `Nat.rec`

4. **Is the goal purely computational?** → Try `decide`, `norm_num`, `omega`, or `native_decide`

5. **Nothing obvious?** → Try `simp?`, `exact?`, `apply?` — these search for applicable lemmas.

---

## 3. Tweakable Aspects — Where Variability Lives

These are the "knobs" you can turn on almost any proof:

### a) **Granularity**
You can write a proof in 1 line or 50. Compare:

```lean
-- Maximally terse
theorem ex1 : 2 + 2 = 4 := by decide

-- Maximally verbose
theorem ex2 : 2 + 2 = 4 := by
  show 2 + 2 = 4
  norm_num
```

### b) **Automation level**
Choose how much work you delegate to automation:

```lean
-- High automation
theorem sq_nonneg' (x : ℝ) : 0 ≤ x ^ 2 := by positivity

-- Medium automation
theorem sq_nonneg'' (x : ℝ) : 0 ≤ x ^ 2 := mul_self_nonneg x

-- Low automation (build from primitives)
theorem sq_nonneg''' (x : ℝ) : 0 ≤ x ^ 2 := by
  rw [sq]
  exact mul_self_nonneg x
```

### c) **Named vs. anonymous hypotheses**
```lean
-- Named: readable, referable
have h_pos : 0 < n := by omega

-- Anonymous / inline
exact Nat.pos_of_ne_zero (by omega)
```

### d) **Forward vs. backward reasoning**
```lean
-- Forward: build up from hypotheses
theorem ex_fwd (h : n < m) (h2 : m < k) : n < k := by
  have h3 := Nat.lt_trans h h2
  exact h3

-- Backward: reduce goal to subgoals
theorem ex_bwd (h : n < m) (h2 : m < k) : n < k := by
  apply Nat.lt_trans
  · exact h
  · exact h2
```

### e) **Which lemma from the library to invoke**
There are often many paths to the same result. For example, to show `a * b = b * a` you could use:
- `mul_comm a b`
- `ring`
- `simp [mul_comm]`
- `rw [mul_comm]`
- `omega` (for `ℕ`/`ℤ` with small enough values)

### f) **How to decompose the proof into helper lemmas**
Any proof can be factored into sub-lemmas in many different ways. This is a major design choice.

### g) **Universe and type generality**
Prove for `ℕ`, `ℤ`, `ℝ`, or an arbitrary `CommRing`? More general proofs are harder but more reusable.

---

## 4. Tiny Patterns to Explore as a New Learner

These are small, self-contained exercises you can try right now. Each one teaches a different proof concept.

### Pattern 1: **Proof by `rfl` (reflexivity)**
```lean
example : 42 = 42 := rfl
example : "hello" = "hello" := rfl
-- Try: Change one side. What error do you get?
```

### Pattern 2: **`intro` + `exact`**
```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

-- Variation: use `apply h; exact hp` instead
```

### Pattern 3: **`constructor` for `∧` and `↔`**
```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- Try: prove `P ∧ Q → Q ∧ P`
```

### Pattern 4: **`cases` for `∨`**
```lean
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq
```

### Pattern 5: **`use` for existentials**
```lean
example : ∃ n : ℕ, n + n = 10 := by
  use 5

-- Try: Change 10 to 11. What happens?
```

### Pattern 6: **`induction` on natural numbers**
```lean
theorem sum_formula (n : ℕ) : 2 * (Finset.range n).sum id = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih => sorry -- try filling this in!
```

### Pattern 7: **`calc` chains**
```lean
example (a b c : ℕ) (h1 : a = b + 1) (h2 : b = c + 2) : a = c + 3 := by
  calc a = b + 1 := h1
    _ = (c + 2) + 1 := by rw [h2]
    _ = c + 3 := by ring
```

### Pattern 8: **`simp` with custom lemmas**
```lean
@[simp] theorem my_lemma : (0 : ℕ) + n = n := Nat.zero_add n

example : 0 + (0 + n) = n := by simp
-- Try: remove the @[simp] attribute. Does `simp` still work?
```

### Pattern 9: **`omega` for linear arithmetic**
```lean
example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by omega
example (a b : ℤ) (h : 2 * a = 2 * b) : a = b := by omega
-- Try: replace `ℤ` with `ℝ`. Does `omega` still work? (No — use `linarith` instead.)
```

### Pattern 10: **`by_contra` for proof by contradiction**
```lean
example (n : ℕ) (h : ¬(n = 0)) : 0 < n := by
  by_contra h2
  push_neg at h2
  omega
```

### Pattern 11: **Switching between tactic and term mode**
```lean
-- Term inside tactic
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

-- Tactic inside term
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  ⟨hp, by exact hq⟩
```

### Pattern 12: **Using `?` tactics for discovery**
```lean
-- These print suggestions to the Lean Infoview:
example (n : ℕ) : n + 0 = n := by exact?   -- finds the lemma for you
example (n : ℕ) : n + 0 = n := by simp?     -- shows which simp lemmas were used
example (n m : ℕ) (h : n ≤ m) : n ≤ m + 1 := by apply?  -- finds applicable lemmas
```

---

## 5. Resources for Exploring Proof Writing in Lean

### Official & Semi-Official
- **[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)** — The best tutorial for mathematicians. Covers tactics, structures, and real math proofs. Highly recommended.
- **[Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)** — The official reference. More computer-science flavored. Excellent for understanding term-mode proofs.
- **[Lean 4 Metaprogramming Book](https://leanprover-community.github.io/lean4-metaprogramming-book/)** — For when you want to write your own tactics.

### Interactive & Game-Based
- **[Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4)** — Learn induction and basic tactics by proving properties of natural numbers. The single best starting point for beginners.
- **[Lean Game Server](https://adam.math.hhu.de/)** — Hosts multiple games beyond NNG: Set Theory Game, Logic Game, etc.

### Community
- **[Lean Zulip Chat](https://leanprover.zulipchat.com/)** — The main community forum. Search archives before asking; most beginner questions have been answered.
- **[Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)** — Searchable documentation for the entire Mathlib library.

### Tactic References
- **[Mathlib Tactic Index](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic.html)** — Browse all available tactics.
- **[Lean 4 Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactics/)** — Core tactics built into Lean itself.

---

## 6. A Mental Framework: The "Proof Design Space"

Think of each proof as having these independent axes of variation:

```
Style:         term ←————————→ tactic
Automation:    manual ←————————→ automated (decide/omega/aesop)
Direction:     forward ←————————→ backward
Granularity:   one-liner ←————————→ 50 lines with helpers
Generality:    concrete (ℕ) ←————————→ abstract (CommMonoid)
Decomposition: monolithic ←————————→ many small lemmas
Readability:   code-like ←————————→ textbook-like (calc/show)
```

As a learner, deliberately move along each axis. Take a proof you've written and rewrite it:
- In a different style (tactic → term, or vice versa)
- With more/less automation
- With `calc` instead of `rw` chains
- Split into helper lemmas, or merged into one

This is the fastest way to build intuition for what Lean offers.

---

## 7. Quick Reference: Common Tactic Cheat Sheet

| Tactic | What it does |
|---|---|
| `intro x` | Introduce a hypothesis or variable |
| `exact e` | Provide the exact proof term |
| `apply f` | Reduce goal using a function/lemma |
| `rw [h]` | Rewrite using an equation |
| `simp` | Simplify using a database of lemmas |
| `ring` | Prove equalities in commutative (semi)rings |
| `omega` | Linear arithmetic over `ℕ` and `ℤ` |
| `linarith` | Linear arithmetic over ordered fields |
| `norm_num` | Evaluate numerical expressions |
| `positivity` | Prove positivity/nonnegativity goals |
| `gcongr` | Prove inequalities by congruence |
| `constructor` | Split `∧`, `↔`, or inductive goals |
| `cases h` | Case-split on `∨`, inductive types |
| `induction n` | Induction on natural numbers, lists, etc. |
| `use x` | Provide witness for `∃` |
| `obtain ⟨a, b⟩ := h` | Destructure `∧`, `∃`, etc. |
| `by_contra h` | Assume negation of goal |
| `contrapose` | Switch to contrapositive |
| `push_neg` | Push negations inward |
| `decide` | Prove decidable propositions by computation |
| `aesop` | General-purpose automation (search) |
| `exact?` | Search for a matching lemma |
| `simp?` | Show which simp lemmas were used |
| `apply?` | Search for applicable lemmas |
