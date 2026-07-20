# Survey of equality orientation and syntactically larger right-hand sides

This survey supplements `FROBENIUS_API_REVIEW.md`. It searches the checked-out
Lean 4 and Mathlib 4 sources for precedents relevant to

```lean
frobenius K p ^ m = frobenius K p ^ (m % n)
```

The sources inspected were:

- Lean 4.28.0, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`;
- Mathlib, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

The scan used several deliberately broad regular-expression families, followed
by manual inspection of the selected declarations. Representative commands:

```sh
# Multiline declarations with a mod-related name and `%` on an equality RHS.
rg -n -U --pcre2 --glob '*.lean' \
  '(?s)(theorem|lemma)\s+\w*(?:mod|Mod)\w*[^:]*:\s*[^\n]*(?:\n\s+[^:=\n][^\n]*){0,3}=\s*[^\n]*%[^\n]*' \
  Mathlib

# Named periodicity and residue-normalization families.
rg -n --glob '*.lean' \
  'pow_eq_pow_mod|I_pow_eq_pow_mod|iterate_mod|pow_mod_period|mod_left|mod_right|nat_mod_four|nat_mod_eight' \
  Mathlib

# Broad equality RHS scans for conditionals, compositions, maps, products,
# and other expressions that are visibly larger than a short LHS.
rg -n --glob '*.lean' \
  'theorem .* : [A-Za-z_.]+ [^=]{0,50} = (if |match |[^ ]+ \+ |[^ ]+ \* |[^ ]+ ∘ |[^ ]+\.map)' \
  Init Std Mathlib
```

These are heuristic text searches, not a parser-based census. They are useful
for finding examples but should not be interpreted as complete counts.

## 1. Strong precedents with the reduced argument on the RHS

These are the closest matches to the proposed Frobenius theorem.

| Declaration | Source | Orientation | Attribute |
|---|---|---|---|
| `pow_eq_pow_mod` | `Mathlib/Algebra/Group/Basic.lean:171` | `a ^ m = a ^ (m % n)` | not `[simp]` |
| `Complex.I_pow_eq_pow_mod` | `Mathlib/Data/Complex/Basic.lean:604` | `I ^ n = I ^ (n % 4)` | not `[simp]` |
| `Int.units_pow_eq_pow_mod_two` | `Mathlib/Data/Int/Order/Units.lean:55` | `u ^ n = u ^ (n % 2)` | not `[simp]` |
| `neg_one_pow_eq_pow_mod_two` | `Mathlib/Algebra/Ring/Commute.lean:171` | `(-1) ^ n = (-1) ^ (n % 2)` | not `[simp]` |
| `χ₄_nat_mod_four` | `Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean:58` | `χ₄ n = χ₄ (n % 4)` | not `[simp]` |
| `χ₈_nat_mod_eight` | same file, line 134 | `χ₈ n = χ₈ (n % 8)` | not `[simp]` |
| `legendreSym.mod` | `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:174` | `legendreSym p a = legendreSym p (a % p)` | not `[simp]` |
| `jacobiSym.mod_left` | `Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:215` | `J(a \| b) = J(a % b \| b)` | not `[simp]` |
| `jacobiSym.mod_right'` | same file, line 453 | `J(a \| b) = J(a \| b % (4 * a))` | not `[simp]` |
| `jacobiSym.mod_right` | same file, line 475 | `J(a \| b) = J(a \| b % (4 * a.natAbs))` | not `[simp]` |

The character and symbol examples are particularly informative. Their right
sides are not merely larger because of `%`; some introduce casts, a product in
the modulus, or `natAbs`. Nonetheless, the declarations point from the
unrestricted input to a canonical residue representative.

The first four power examples form a direct family around the proposed API.
They support both the orientation and the decision not to attach `[simp]`.

## 2. A genuine counter-pattern: dynamics uses the reverse orientation

Mathlib does not use one orientation universally. In
`Mathlib/Dynamics/PeriodicPts/Defs.lean` one finds:

```lean
theorem IsPeriodicPt.iterate_mod_apply
    (h : IsPeriodicPt f n x) (m : ℕ) :
    f^[m % n] x = f^[m] x

@[simp] theorem iterate_mod_minimalPeriod_eq :
    f^[n % minimalPeriod f x] x = f^[n] x

@[simp] theorem pow_mod_period_smul (n : ℕ) :
    m ^ (n % period m a) • a = m ^ n • a
```

There is an analogous `[simp]` theorem for integer powers. Here the modulo form
is on the **left**, and simplification removes it. This is relevant rather than
embarrassing: it demonstrates that orientation is tied to API role.

- The group-theoretic `pow_eq_pow_mod` family is an explicit periodic
  normalization API and puts the reduced representative on the RHS.
- The dynamics declarations are `[simp]` rules and choose a simplifier normal
  form that eliminates an explicit modulo operation already present in a term.

The proposed Frobenius result is a direct specialization of the first family,
not a declaration in the dynamics simplifier family. Keeping it non-`[simp]`
and source-oriented is therefore coherent.

## 3. Lean core arithmetic: canonical RHSs can be larger

The Lean core source also contains many examples where the right side grows in
syntax because it exposes a canonical computational or algebraic form:

```lean
-- Init/Data/Int/DivMod/Bootstrap.lean
theorem Int.add_emod (a b n : Int) :
    (a + b) % n = (a % n + b % n) % n

theorem Int.mul_emod (a b n : Int) :
    (a * b) % n = (a % n) * (b % n) % n

-- Init/Data/Int/DivMod/Lemmas.lean
theorem Int.fmod_eq_emod {a b : Int} :
    fmod a b = a % b + if 0 ≤ b ∨ b ∣ a then 0 else b

theorem Int.tmod_eq_emod {a b : Int} :
    tmod a b = a % b - if 0 ≤ a ∨ b ∣ a then 0 else b.natAbs
```

The RHSs are visibly larger, but encode the operation through a chosen
canonical convention. This supports the general methodological point that
printed term size alone does not determine theorem orientation.

## 4. Non-mod examples of larger explanatory right-hand sides

The same phenomenon occurs outside modular arithmetic.

```lean
-- Lean Init/Core.lean
@[simp] theorem Thunk.sizeOf_eq [SizeOf α] (a : Thunk α) :
    sizeOf a = 1 + sizeOf a.get

-- Lean Init/Grind/Attr.lean, documentation example
 theorem max_def : max n m = if n ≤ m then m else n

-- Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean
 theorem one_apply {i j} :
    (1 : CStarMatrix n n A) i j = if i = j then 1 else 0

-- Mathlib/Probability/ProbabilityMassFunction/Monad.lean
 theorem pure_apply : pure a a' = if a' = a then 1 else 0

-- Mathlib/Logic/Embedding/Basic.lean
 theorem coe_trans (f : α ↪ β) (g : β ↪ γ) :
    ⇑(f.trans g) = ⇑g ∘ ⇑f
```

These examples have different purposes—computation, unfolding an abstract
operation, or exposing composition—so they are not direct Frobenius
precedents. They do show that a useful RHS may be larger because it is more
explicit, canonical, or usable by downstream reasoning.

## 5. Conclusion for the Frobenius API

The expanded survey strengthens and nuances the recommendation:

1. The closest algebraic precedents overwhelmingly use
   `unrestricted = reduced-modulo` and are not `[simp]`.
2. Number-theoretic character APIs independently use the same orientation,
   including RHSs more elaborate than `m % n` alone.
3. The dynamics API supplies a real reverse-oriented counterexample, but its
   `[simp]` role explains the difference and reinforces the decision to keep
   the Frobenius theorem explicit.
4. Lean core and Mathlib routinely accept syntactically larger RHSs when those
   sides expose canonical computational or mathematical structure.

Accordingly, retain

```lean
frobenius K p ^ m = frobenius K p ^ (m % n)
```

without `[simp]`, and use it as an explicit rewrite.
