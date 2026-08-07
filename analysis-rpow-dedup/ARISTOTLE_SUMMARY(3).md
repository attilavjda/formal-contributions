# Summary of changes for run d0b2d709-ba8b-4967-b3e3-010a57be6e93
**Review verdict: your diagnosis is correct, and the alias patch is the right first PR — but two details of the "intended" statement need fixing before it goes anywhere.** Full write-up in `CONTRIBUTION-NOTES-5.md`; everything below is checked in Lean (`RequestProject/RpowLogNameReading.lean`, builds clean, no `sorry`/`admit`/`axiom`, axioms `propext`/`Classical.choice`/`Quot.sound`).

**1. Name vs. statement vs. proof.** Agreed: `rpow_le_of_le_log` promises `(le_log) → (rpow_le)`; the declaration delivers `(log_le) → (le_rpow)` and its proof goes through `le_rpow_iff_log_le`, whose name records that. The correctly named twin `le_rpow_of_log_le` already exists forty lines up, verbatim — certified by `@rpow_le_of_le_log = @le_rpow_of_log_le := rfl` for all six pairs. Since the statement is already correct, only the name is at issue, and a public name is repaired by deprecation, not overwriting.

**2. Corrections to your proposed intended form `(h : z • log y ≤ log x) : y ^ z ≤ x`.**
- The positivity binder must move with the statement. Keeping `0 < y` (base) makes the flipped lemma **false**: `y = 1, z = 1, x = -2` satisfies `0 < y` and `z * log y = 0 ≤ log 2 = log (-2) = log x` but not `1 ≤ -2` (`le_log_reading_needs_pos_bound`). The right binder is `0 < x` on the **bound** — and then no positivity on the base is needed at all (`rpow_le_of_le_log_as_named`).
- Use `*`, not `•`: `z • log y = z * log y` by `smul_eq_mul`, and the `nsmul` form follows by `nsmul_eq_mul` (`pow_le_of_le_log_as_named_smul`), so `•` is not a different lemma; the surrounding block writes the coerced product.

**3. Adjustments to the PRs.** Cleanup PR (`mathlib-patch-rpow-log-dedup.diff`) unchanged in substance — six deprecated aliases, 6 insertions / 20 deletions, no call sites anywhere; set the real `since` date, and place the aliases next to their targets (or in a deprecated group at the end of the section) rather than in the hole left by the deleted block. Keep the generalisation (`…-plus-general.diff`) as a separate PR under `rpow_le_of_mul_log_le` &c., with the sharpness witnesses in the PR text rather than in the file, and state the follow-up plan: rename onto the freed names once the deprecations expire. That is the only route to "the name finally means what it says" that never repurposes a live name.

Committed and pushed: `RequestProject/RpowLogNameReading.lean` and `CONTRIBUTION-NOTES-5.md`; earlier deliverables untouched and still building.

# Summary of changes for run 9440da7a-1fb0-46dc-9809-35f0061803ec
**Short answer: restating the six lemmas to match their names is tempting but not the right patch — though the investigation turned up something that changes the picture, and I verified it in Lean.**

**The correction.** The earlier claim that "P2 is already the `.2` of `rpow_le_iff_le_log`, so nothing is missing" holds only for the weak form. In its natural generality P2 is *strictly stronger* than that direction: the positivity of the base can be dropped entirely,

`(hy : 0 < y) (h : z * log x ≤ log y) : x ^ z ≤ y` for **every** real `x`,

because `log x = log |x|` and `x ^ z ≤ |x ^ z| ≤ |x| ^ z`; the case `x = 0` falls out of `log 0 = 0`. That is the exact mirror of what `le_rpow_of_log_le` does on the other side (it drops `0 < x` from `le_rpow_iff_log_le`). So the "intended" reading of the misleading name is a genuine symmetry gap, not a duplicate. Two sharpness checks: `0 < y` cannot be dropped (`x = 2, z = 1, y = -2`), and the iff itself cannot be generalised by removing `0 < x` — its forward direction fails at `x = -2, z = 1, y = 1`, so only the `←` direction survives.

**Why I still recommend deprecating rather than restating.** (1) It would repurpose a public name: these six entered Mathlib on 2024-08-26 with the current meaning, and a silently changed meaning is precisely what the deprecation machinery cannot warn about. (2) It fails the "the diff removes something" test — the P1 duplication stays and six new theorems are added; it is a feature PR dressed as a cleanup. (3) The two changes are independent: the dedup is riskless (no call sites anywhere in Mathlib, Archive, Counterexamples, tests), while whether `rpow` at a negative base deserves API is a reviewer judgement that should not block the cleanup.

**What is in the project now (all committed and pushed, builds clean, no `sorry`/`admit`/`axiom`, axioms `propext`/`Classical.choice`/`Quot.sound` only):**
- `RequestProject/RpowLogIntent.lean` — the six generalised statements (`rpow`/`pow`/`zpow`, `≤` and `<`), the negative-base witness showing they exceed `(rpow_le_iff_le_log hx hy).2`, and the two counterexamples above.
- `mathlib-patch-rpow-log-dedup-plus-general.diff` — the optional second variant: the six deprecated aliases **plus** the generalised lemmas under collision-free names `rpow_le_of_mul_log_le`, `pow_le_of_mul_log_le`, `zpow_le_of_mul_log_le`, `rpow_lt_of_mul_log_lt`, `pow_lt_of_mul_log_lt`, `zpow_lt_of_mul_log_lt` (40 insertions / 20 deletions). Applied to the pinned Mathlib checkout, the module elaborates with no errors and no linter warnings; the checkout was then reverted and is clean.
- `mathlib-patch-rpow-log-dedup.diff` (unchanged, still the recommended first PR): 6 insertions / 20 deletions, no declaration leaves the environment.
- `CONTRIBUTION-NOTES-4.md` — the full write-up of the comparison.

If one wants the "name finally means what it says" end state, the clean route is: land the dedup now, then rename the general lemmas onto the freed names once the deprecations expire.

# Summary of changes for run 22a0783f-fba3-4836-9c66-d51c1b3b2993
**A new tiny, line-removing Mathlib contribution opportunity — found, verified, and packaged.**

*Scope:* undergraduate real analysis (`Real.log` vs. real/natural/integer powers). *Category:* deduplication, with a naming fix included. It is distinct from the two TODO-discharging items in the earlier notes, as requested.

**The opportunity.** `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` contains two blocks of log-vs-power comparison lemmas that overlap exactly. Lines 783–812 give

- `le_rpow_of_log_le`, `le_pow_of_log_le`, `le_zpow_of_log_le`,
- `lt_rpow_of_log_lt`, `lt_pow_of_log_lt`, `lt_zpow_of_log_lt`,

and lines 832–870 repeat all six verbatim — same binders, same statements, same proof scripts — as `rpow_le_of_le_log`, `pow_le_of_le_log`, `zpow_le_of_le_log`, `rpow_lt_of_lt_log`, `pow_lt_of_lt_log`, `zpow_lt_of_lt_log`. The second block's names are additionally misleading: the conclusion is `x ≤ y ^ z`, which the naming convention spells `le_rpow_of_log_le`, whereas `rpow_le_of_le_log` announces a conclusion `x ^ z ≤ y` — the shape of its neighbours `rpow_le_iff_le_log` and `le_log_of_rpow_le`.

**The patch** (`mathlib-patch-rpow-log-dedup.diff`) replaces each duplicate by a one-line `@[deprecated] alias` pointing at the correctly named survivor: 6 insertions, 20 deletions, no declaration leaves the environment.

**What I verified rather than assumed.**
- `RequestProject/RpowLogDedup.lean` proves, for each of the six pairs, `@Real.rpow_le_of_le_log = @Real.le_rpow_of_log_le := rfl` (the equation only elaborates if the statements coincide), and separately restates each duplicate's statement and closes it with the surviving lemma alone (`…_covers_duplicate`), so the aliases lose no API. The file builds with no `sorry`/`admit`/`axiom`; the theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
- No occurrence of the six duplicate names exists anywhere in Mathlib, the Archive, the Counterexamples or the test suite, at either the pinned commit or current master (2026-08-06); the similar unqualified hits in `Mathlib/Data/Nat/Choose/Factorization.lean` and `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` are the `Nat` namespace lemmas, and both files were recompiled unaffected.
- The patched Mathlib file elaborates with no errors and no linter warnings; the Mathlib checkout was then reverted and is clean.
- The two blocks are unchanged at Mathlib master of 2026-08-06, at the same line numbers, so the opportunity is still live.

**Also reported (a negative result worth knowing).** I ran an environment-level sweep over every theorem in `Mathlib/Analysis` looking for explicit hypotheses occurring neither in the remaining statement nor in the proof term — the "dead hypothesis" vein. It returns zero hits, because Lean's `unusedVariables` linter already keeps that class out of the library, so that vein is unproductive in Mathlib. The same sweep, re-keyed on statement hashes, is what surfaced the duplicates above; the recipe is written up in `CONTRIBUTION-NOTES-3.md`.

All work is committed and pushed: `mathlib-patch-rpow-log-dedup.diff`, `RequestProject/RpowLogDedup.lean`, `CONTRIBUTION-NOTES-3.md`. Earlier deliverables are untouched and still build.