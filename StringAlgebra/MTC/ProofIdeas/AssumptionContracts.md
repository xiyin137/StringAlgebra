# Assumption Contract Matrix

## Purpose

This file tracks the current proof-debt contracts and their theorem wrappers.
Use it as a checklist for replacing placeholders with real proofs.

## Foundation Contracts

`Ribbon.RibbonSphericalAxiom`
- Field: `spherical`
- Wrapper usage:
  - `Ribbon.toSphericalCategory`

`Spherical.SphericalDimAxioms`
- Fields:
  - `qdim_dual`
  - `qdim_unit`
  - `qdim_tensor`
- Wrapper usage:
  - `Spherical.qdim_dual`
  - `Spherical.qdim_unit`
  - `Spherical.qdim_tensor`

`FusionCategory.FusionRuleAxioms`
- Fields:
  - `fusionCoeff_assoc`
  - `fusionCoeff_frobenius`
  - `fusionCoeff_dual_swap`
- Wrapper usage:
  - `FusionCategory.fusionCoeff_assoc`
  - `FusionCategory.fusionCoeff_frobenius`
  - `FusionCategory.fusionCoeff_dual_swap`

## Modular Contracts

`SMatrix.SMatrixAxioms`
- Fields:
  - `sMatrixEnd_symmetric`
  - `totalDimSq_ne_zero`
  - `quantumDim_fusion`
  - `sMatrix_orthogonality`
- Wrapper usage:
  - `SMatrix.sMatrixEnd_symmetric`
  - `SMatrix.totalDimSq_ne_zero`
  - `SMatrix.quantumDim_fusion`
  - `SMatrix.sMatrix_orthogonality`

`ModularTensorCategory.ModularDataAxioms`
- Fields:
  - `sMatrix_squared`
  - `modular_relation`
- Wrapper usage:
  - `ModularTensorCategory.sMatrix_squared`
  - `ModularTensorCategory.modular_relation`

`Verlinde.VerlindeAxioms`
- Fields:
  - `verlinde_formula`
  - `sMatrix_diagonalizes_fusion`
- Wrapper usage:
  - `Verlinde.verlinde_formula`
  - `Verlinde.sMatrix_diagonalizes_fusion`

## Bundle Aggregates

`FoundationAssumptions`
- Extends:
  - `RibbonSphericalAxiom`
  - `SphericalDimAxioms`
  - `FusionRuleAxioms`

`ModularAssumptions`
- Extends:
  - `SMatrixAxioms`
  - `ModularDataAxioms`
  - `VerlindeAxioms`

`DevelopmentAssumptions`
- Extends:
  - `FoundationAssumptions`
  - `ModularAssumptions`

## Bridge Contracts

`Bridge.VOANondegeneracyAssumptions`
- Field:
  - `mueger_center_trivial`
- Usage:
  - `Bridge.huang_nondegeneracy_of_assumptions`
  - `Bridge.modularTensorCategoryOfAssumptions`

`Bridge.VOATwistRootAssumptions`
- Field:
  - `twist_roots_of_unity`
- Usage:
  - `Bridge.twist_roots_of_unity_of_assumptions`

`Bridge.VOABridgeAssumptions`
- Extends:
  - `Bridge.VOANondegeneracyAssumptions`
  - `Bridge.VOATwistRootAssumptions`
- Usage:
  - `Bridge.modularTensorCategoryOfBridgeAssumptions`
  - `Bridge.huang_nondegeneracy_of_bridge_assumptions`
  - `Bridge.twist_roots_of_unity_of_bundle`
- Constructor:
  - `Bridge.voaBridgeAssumptionsOfComponents`
