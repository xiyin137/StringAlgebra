# MTC Module TODO

## Status (2026-02-26)

- `lake build StringAlgebra.MTC` passes.
- Proof-gap count: **16 theorem-level `sorry` markers** in `StringAlgebra/MTC`.
- No local MTC assumption-bundle/axiom-class wrappers remain (`*Axioms`, `*Assumptions`, `RibbonSphericalAxiom` removed).
- Open debt is represented directly at theorem sites.

## Proof-Gap Inventory (16)

1. `Spherical.lean`
- `qdim_dual`
- `qdim_unit`
- `qdim_tensor`

2. `FusionCategory.lean`
- `fusionCoeff_assoc`
- `fusionCoeff_frobenius`
- `fusionCoeff_dual_swap`

3. `SMatrix.lean`
- `sMatrixEnd_symmetric`
- `totalDimSq_ne_zero`
- `quantumDim_fusion`
- `sMatrix_orthogonality`

4. `ModularTensorCategory.lean`
- `sMatrix_squared`
- `modular_relation`

5. `Verlinde.lean`
- `verlinde_formula`
- `sMatrix_diagonalizes_fusion`

6. `FusionPF.lean`
- `fpDimCandidate_pos_gap`
- `fpDimCandidate_fusion_gap`

## Smuggling Cleanup Completed

1. Removed `MTC/Assumptions.lean` and all bundle classes (`FoundationAssumptions`, `ModularAssumptions`, `DevelopmentAssumptions`).
2. Removed theorem-wrapper axiom classes from core files:
- `SphericalDimAxioms`
- `FusionRuleAxioms`
- `SMatrixAxioms`
- `ModularDataAxioms`
- `VerlindeAxioms`
- `PerronFrobeniusPosAxiom`, `PerronFrobeniusFusionAxiom`, `PerronFrobeniusAxioms`
3. Removed ribbon spherical assumption shim:
- `RibbonSphericalAxiom`
- `toSphericalCategory`
4. Updated `DevelopmentHarness.lean` to consume direct theorem-gap interfaces.
5. Removed bridge assumption-bundle layer earlier (`Bridge/Assumptions.lean`) and kept bridge hypotheses theorem-local.

## Build-Verified Import Surface

Top-level MTC entry is now:
- `FoundationLayer`
- `FusionLayer`
- `ModularLayer`
- `DevelopmentHarness`
- `Bridge.Layer`

(no assumption-bundle import)

## Closure Order (Recommended)

1. `Spherical.lean`
- prove `qdim_unit`, `qdim_dual`, `qdim_tensor`

2. `FusionCategory.lean`
- derive associativity/Frobenius/dual-swap from semisimple tensor-Hom infrastructure

3. `SMatrix.lean`
- prove end-valued symmetry and orthogonality, then total-dimension non-vanishing and fusion-character identity

4. `ModularTensorCategory.lean`
- prove `S²` charge-conjugation and `(ST)^3` relation

5. `Verlinde.lean`
- derive Verlinde and diagonalization from established modular identities

6. `FusionPF.lean`
- discharge PF candidate positivity and fusion character theorems

7. `Bridge/VOAToMTC.lean` has no theorem-level `sorry`; bridge interfaces now require explicit VOA analytic hypotheses at theorem call sites.

## Audit Commands

```bash
rg -n '^\s*sorry\b' StringAlgebra/MTC --glob '*.lean'
rg -n '^\s*class\s+.*(Axioms|Assumptions|Axiom)' StringAlgebra/MTC --glob '*.lean'
lake build StringAlgebra.MTC
```
