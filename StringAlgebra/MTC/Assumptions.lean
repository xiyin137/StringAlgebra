import StringAlgebra.MTC.Verlinde

/-!
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Assumption Bundles for MTC Development

This module groups the explicit placeholder proof contracts used in the
current development phase into coherent bundles.

The goal is to reduce instance clutter in downstream files while keeping
proof debt explicit and auditable.
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

/-- Foundational placeholder assumptions:
    - ribbon -> spherical trace equality
    - spherical dimension identities
    - fusion-rule identities -/
class FoundationAssumptions (k : Type u₁) [Field k]
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C] [RibbonFusionCategory k C]
    extends RibbonCategory.RibbonSphericalAxiom C,
      SphericalDimAxioms C,
      FusionCategory.FusionRuleAxioms (k := k) (C := C)

/-- Modular-level placeholder assumptions:
    - S-matrix identities
    - modular `S,T` relations
    - Verlinde/diagonalization identities -/
class ModularAssumptions (k : Type u₁) [Field k] [IsAlgClosed k]
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C] [HasKernels C]
    [ModularTensorCategory k C]
    extends SMatrix.SMatrixAxioms (k := k) (C := C),
      ModularTensorCategory.ModularDataAxioms (k := k) (C := C),
      Verlinde.VerlindeAxioms (k := k) (C := C)

/-- Full placeholder bundle for current comprehensive development.
    This is a convenience aggregate of foundational and modular assumptions. -/
class DevelopmentAssumptions (k : Type u₁) [Field k] [IsAlgClosed k]
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C] [HasKernels C]
    [ModularTensorCategory k C]
    extends FoundationAssumptions (k := k) (C := C),
      ModularAssumptions (k := k) (C := C)

/-! ### Bundle Constructors -/

/-- Build `FoundationAssumptions` from its component contracts. -/
instance foundationAssumptionsOfComponents
    {k : Type u₁} [Field k]
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C] [RibbonFusionCategory k C]
    [RibbonCategory.RibbonSphericalAxiom C]
    [SphericalDimAxioms C]
    [FusionCategory.FusionRuleAxioms (k := k) (C := C)] :
    FoundationAssumptions (k := k) (C := C) where

/-- Build `ModularAssumptions` from its component contracts. -/
instance modularAssumptionsOfComponents
    {k : Type u₁} [Field k] [IsAlgClosed k]
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C] [HasKernels C]
    [ModularTensorCategory k C]
    [SMatrix.SMatrixAxioms (k := k) (C := C)]
    [ModularTensorCategory.ModularDataAxioms (k := k) (C := C)]
    [Verlinde.VerlindeAxioms (k := k) (C := C)] :
    ModularAssumptions (k := k) (C := C) where

/-- Build `DevelopmentAssumptions` from `FoundationAssumptions` and
    `ModularAssumptions`. -/
instance developmentAssumptionsOfBundles
    {k : Type u₁} [Field k] [IsAlgClosed k]
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C] [HasKernels C]
    [ModularTensorCategory k C]
    [FoundationAssumptions (k := k) (C := C)]
    [ModularAssumptions (k := k) (C := C)] :
    DevelopmentAssumptions (k := k) (C := C) where

end StringAlgebra.MTC
