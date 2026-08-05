# Upstream review

The proposed caller simplifications are good, but the generic theorem needs two changes before
submission.

## Required changes

1. **Fix the first inequality.** In the proof from the proposed diff, the target after `hk.trans` is
   the singly indexed diagonal supremum. Thus

   ```lean
   le_iSup_of_le k (le_iSup_of_le k le_rfl)
   ```

   has one indexed-supremum introduction too many. Without `@[to_dual]`, the corresponding term is
   `le_iSup_of_le k le_rfl`.

2. **Do not use that concise `iSup` proof with `@[to_dual]`.** Even after removing the extra
   introduction, automatic dualization leaves a supremum-side projection in the generated proof,
   so creation of `iInf₂_eq_diagonal` fails. The checked replacement in `UPSTREAM.patch` uses
   `sSup_le` and `le_sSup`; these constants dualize correctly.

## Recommended generality and placement

The theorem only needs `CompleteSemilatticeSup α`, not `CompleteLattice α`. Put it in the existing
`CompleteSemilatticeSup` section near `sSup_le_sSup_of_isCofinalFor`; `@[to_dual]` then generates the
corresponding theorem under `CompleteSemilatticeInf`.

A short docstring was added because this is a new public declaration. The inferred existing
variables `{α : Type*}` and `{ι : Sort*}` are retained, avoiding repetition in the declaration.

## Caller changes

The proposed replacements of `ENat.iSup_add_iSup` and `ENNReal.iSup_add_iSup` are retained. Their
empty-index branches remain in the existing explicit `simp only` form, keeping this patch focused;
the diagonal argument applies to the nonempty branch after distribution of addition over the two
indexed suprema.

## Deliverable and checks

`UPSTREAM.patch` contains the complete three-file patch suitable for applying to the matching
mathlib checkout.

The affected modules build successfully:

- `Mathlib.Order.CompleteLattice.Basic`
- `Mathlib.Data.ENat.Lattice`
- `Mathlib.Data.ENNReal.Operations`

The style linter passes for all three modules. Both the new supremum theorem and its generated
infimum dual have no axiomatic dependencies; the two callers use only mathlib's accepted standard
axioms. No `sorry` or `admit` is introduced.
