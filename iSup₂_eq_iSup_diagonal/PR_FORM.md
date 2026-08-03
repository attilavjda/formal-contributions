# Which form to submit, and the minimal first PR

The companion file `RequestProject/DiagonalVariations.lean` deliberately re-proves the
same facts in ~20 styles. For an *upstream* submission the choice is not aesthetic — a few
concrete constraints pin it down.

## Which form (style) to submit

Submit the **tactic-mode `sSup`/`le_sSup` proof over the weakest typeclass
`CompleteSemilatticeSup`, carrying `@[to_dual]`.** This is the `diag_sSup` / `sSup_diag_auto`
form in the companion, i.e. the canonical `iSup₂_eq_diagonal` already living in
`RequestProject/Diagonal.lean`.

Reasons, following the "Proof Design Space" axes:

- **Generality → weakest class.** State over `CompleteSemilatticeSup`, not `CompleteLattice`.
  Mathlib prefers the most general home; the `sSup`/`le_sSup` API is available there and the
  callers (`ENat`, `ENNReal`) are complete lattices, so nothing is lost.
- **Automation → `to_dual`-compatible, not maximally golfed.** The one-word `iSup_mono'`
  golf (`cofinal_iSup_eq_golf`) and the `CompleteLattice` `iSup`-API proofs are shorter but
  need the full `CompleteLattice` and, crucially, **break `@[to_dual]`** (the generated
  infimum term keeps a `SupSet` projection — see the run notes). The `sSup_le`/`le_sSup`
  argument dualizes cleanly, so one proof yields both `iSup₂_eq_diagonal` and
  `iInf₂_eq_diagonal`.
- **Style → tactic, not term / not `calc`.** Term mode with `Classical.choose`
  (`*_term`) hides the witness and reads poorly; the `calc` versions are legible but verbose.
  A short forward tactic block (`apply sSup_le; rintro …; exact …`) is the Mathlib norm.
- **Direction / granularity → forward, compact.** Neither one-liner nor many-named-step;
  a handful of lines per antisymmetry branch.

So: **not** the `CompleteLattice` golf, **not** term-mode, **not** `calc`, **not** the
conditionally-complete variants — the `CompleteSemilatticeSup` + `sSup` API + `@[to_dual]`
form.

## The minimal meaningful first PR

Ship the smallest self-contained unit that has demonstrated callers:

1. **One new lemma:** `iSup₂_eq_diagonal` with `@[to_dual iInf₂_eq_diagonal]`,
   placed next to `iSup_mono'`/`iSup₂_mono'` in `Order/CompleteLattice/Basic.lean`
   (the `CompleteSemilatticeSup` section).
2. **Simplify the three duplicate callers** it collapses:
   - `ENat.iSup_add_iSup` (`Data/ENat/Lattice.lean`)
   - `ENNReal.iSup_add_iSup` (`Data/ENNReal/Operations.lean`)
   - `ENNReal.iInf_add_iInf` (`Data/ENNReal/Operations.lean`, via the generated dual)

That is the canonical `new lemma → replace duplicates → CI green` shape: one general,
discoverable lemma, no new framework, immediate reuse.

## Deliberately deferred to follow-ups (keep them OUT of the first PR)

- The `IsCofinalFor` **equality companions** `sSup_eq_sSup_of_isCofinalFor` /
  `sInf_eq_sInf_of_isCoinitialFor` (the most "structural" home, sitting next to the existing
  inequality halves). Clean and worth doing, but it is a separate, self-justifying PR and
  mixing it in widens the diff and the review.
- The **conditionally-complete** variants (`ciSup₂_eq_ciSup_diagonal`,
  `ciSup₂_eq_ciSup_diagonal'`) and the **Cardinal** caller — a natural second follow-up,
  since they need a `BddAbove` hypothesis and a different API.
- The remaining Tier-B gaps noted in `SECOND_REVIEW.md` (`ciInf_mono'`, conditionally-complete
  `csSup…_of_isCofinalFor`).

Keep each PR to one idea; land the diagonal-collapse lemma + three callers first.
