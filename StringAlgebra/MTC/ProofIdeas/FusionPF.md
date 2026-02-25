# Proof Ideas: FusionPF.lean

## Current status

`FusionPF.lean` introduces:
- `FusionCategory.PerronFrobeniusPosAxiom`
- `FusionCategory.PerronFrobeniusFusionAxiom`
- `FusionCategory.PerronFrobeniusAxioms`
- constructor `perronFrobeniusAxiomsOfPosFusion`
- wrappers:
  - `fpDimCandidate_unit_of_axioms`
  - `fpDimCandidate_pos_of_axioms`
  - `fpDimCandidate_fusion_of_axioms`
  - Fin-indexed convenience theorems

This keeps FPdim APIs usable while Perron-Frobenius proofs are not yet formalized.
The remaining PF proof debt is now split into two targeted obligations
(positivity + fusion character), with unit normalization derived from the
existing spectral vacuum theorem under canonical indexing.

## Discharge plan for `PerronFrobeniusAxioms`

1. Positivity:
   - Show `leftFusionMatrixByFin i` has a nonnegative real representative.
   - Prove existence of a positive eigenvector under irreducibility.
2. Fusion character identity:
   - Use eigenvector equations for all `N_i`.
   - Show multiplicativity against fusion products and identify coefficients.
3. Unit normalization:
   - Already available from `FusionSpectral.leftFusionSpectralRadius_unit`
     under canonical indexing; bridge this to the axiom-free path as the default.

## Suggested next formal module split

- `FusionPF/Core.lean`: nonnegative matrix and irreducibility lemmas.
- `FusionPF/Perron.lean`: Perron root/vector existence/uniqueness.
- `FusionPF/Character.lean`: fusion-ring character theorem for FP dimensions.
