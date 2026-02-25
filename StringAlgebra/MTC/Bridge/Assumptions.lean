import StringAlgebra.MTC.ModularTensorCategory

/-!
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Bridge Assumption Contracts

Assumption contracts for the VOA-to-MTC bridge layer.
-/

namespace StringAlgebra.MTC.Bridge

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

section Nondegeneracy

variable {k : Type u₁} [Field k]
variable {RepV : Type u₁} [Category.{v₁} RepV] [MonoidalCategory RepV]
variable [BraidedCategory RepV] [Preadditive RepV] [Linear k RepV]
variable [MonoidalPreadditive RepV] [HasFiniteBiproducts RepV] [RigidCategory RepV]

/-- Contract for Huang-style nondegeneracy input on `RepV`. -/
class VOANondegeneracyAssumptions [RibbonFusionCategory k RepV] where
  /-- Transparent simples are isomorphic to the tensor unit. -/
  mueger_center_trivial :
    ∀ i : FusionCategory.Idx (k := k) (C := RepV),
      BraidedFusionCategory.isTransparent (FusionCategory.simpleObj i) →
      Nonempty (FusionCategory.simpleObj i ≅ 𝟙_ RepV)

end Nondegeneracy

section TwistRoots

variable {k : Type u₁} [Field k] [IsAlgClosed k]
variable {RepV : Type u₁} [Category.{v₁} RepV] [MonoidalCategory RepV]
variable [BraidedCategory RepV] [Preadditive RepV] [Linear k RepV]
variable [MonoidalPreadditive RepV] [HasFiniteBiproducts RepV] [RigidCategory RepV]
variable [RibbonFusionCategory k RepV] [HasKernels RepV]

/-- Contract for VOA twist arithmetic input on `RepV`. -/
class VOATwistRootAssumptions where
  /-- Each twist eigenvalue is a root of unity. -/
  twist_roots_of_unity :
    ∀ i : FusionCategory.Idx (k := k) (C := RepV),
      ∃ (n : ℕ) (_ : 0 < n),
        RibbonFusionCategory.twistValue (C := RepV) i ^ n = (1 : k)

/-- Combined bridge contract:
    Huang nondegeneracy plus twist roots-of-unity input. -/
class VOABridgeAssumptions
    extends VOANondegeneracyAssumptions (k := k) (RepV := RepV),
      VOATwistRootAssumptions (k := k) (RepV := RepV)

/-- Build the combined bridge contract from its components. -/
instance voaBridgeAssumptionsOfComponents
    [VOANondegeneracyAssumptions (k := k) (RepV := RepV)]
    [VOATwistRootAssumptions (k := k) (RepV := RepV)] :
    VOABridgeAssumptions (k := k) (RepV := RepV) where

end TwistRoots

end StringAlgebra.MTC.Bridge
