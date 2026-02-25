# Proof Ideas: Ribbon.lean

## Status (2026-02-25)

Proved:
- `twist_unit`
- `toPivotalCategory` construction and both pivotal zigzags
- Drinfeld helper lemmas (`drinfeldIsoIso_eval`, `drinfeldIsoIso_coeval`,
  `drinfeldIsoIso_naturality`)

Temporarily assumption-backed:
- `RibbonSphericalAxiom` (used by `toSphericalCategory`)

## Remaining Core Obligation

Replace the `RibbonSphericalAxiom` requirement with a proof that the canonical
pivotal structure from the ribbon twist is spherical.

Target statement:
- For all endomorphisms `f : X ⟶ X`, `leftTrace f = rightTrace f`.

## Recommended Proof Path

1. Keep the existing Drinfeld/twist helper lemmas as the algebraic engine.
2. Prove a local rewrite converting both traces to a common monodromy-normal
   form using:
   - `drinfeldIsoIso_eval`
   - `drinfeldIsoIso_coeval`
   - mate identities from `rightAdjointMate_comp_evaluation` and
     `coevaluation_comp_rightAdjointMate`.
3. Close the final normalization step via dedicated twist/monodromy lemmas
   (currently represented by `coeval_twist_sq_monodromy` and
   `eval_twist_sq_monodromy`).

## Architecture Note

The theorem API is stable: consumers use `toSphericalCategory` exactly as
before. Only the internal proof term is currently carried as an explicit
assumption contract.
