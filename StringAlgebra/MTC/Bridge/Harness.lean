import StringAlgebra.MTC.Bridge.VOAToMTC

/-!
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Bridge Harness

Integration checks for the VOA bridge assumption contracts.
-/

namespace StringAlgebra.MTC.Bridge

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

section Nondegeneracy

variable {k : Type u₁} [Field k]
variable {RepV : Type u₁} [Category.{v₁} RepV] [MonoidalCategory RepV]
variable [BraidedCategory RepV] [Preadditive RepV] [Linear k RepV]
variable [MonoidalPreadditive RepV] [HasFiniteBiproducts RepV] [RigidCategory RepV]
variable [RibbonFusionCategory k RepV]

theorem nondegeneracy_from_contract
    (i : FusionCategory.Idx (k := k) (C := RepV))
    (h : BraidedFusionCategory.isTransparent (FusionCategory.simpleObj i)) :
    Nonempty (FusionCategory.simpleObj i ≅ 𝟙_ RepV) :=
  huang_nondegeneracy_of_assumptions (k := k) (RepV := RepV) i h

noncomputable def modularity_from_contract
    (hHuang :
      ∀ i : FusionCategory.Idx (k := k) (C := RepV),
        BraidedFusionCategory.isTransparent (FusionCategory.simpleObj i) →
        Nonempty (FusionCategory.simpleObj i ≅ 𝟙_ RepV)) :
    ModularTensorCategory k RepV :=
  modularTensorCategoryOfAssumptions (k := k) (RepV := RepV) hHuang

end Nondegeneracy

section TwistRoots

variable {k : Type u₁} [Field k] [IsAlgClosed k]
variable {RepV : Type u₁} [Category.{v₁} RepV] [MonoidalCategory RepV]
variable [BraidedCategory RepV] [Preadditive RepV] [Linear k RepV]
variable [MonoidalPreadditive RepV] [HasFiniteBiproducts RepV] [RigidCategory RepV]
variable [RibbonFusionCategory k RepV] [HasKernels RepV]

theorem twist_roots_from_contract
    (i : FusionCategory.Idx (k := k) (C := RepV)) :
    ∃ (n : ℕ) (_ : 0 < n),
      RibbonFusionCategory.twistValue (C := RepV) i ^ n = (1 : k) :=
  twist_roots_of_unity_of_assumptions (k := k) (RepV := RepV) i

end TwistRoots

section BundledBridge

variable {k : Type u₁} [Field k]
variable {RepV : Type u₁} [Category.{v₁} RepV] [MonoidalCategory RepV]
variable [BraidedCategory RepV] [Preadditive RepV] [Linear k RepV]
variable [MonoidalPreadditive RepV] [HasFiniteBiproducts RepV] [RigidCategory RepV]
variable [RibbonFusionCategory k RepV]

theorem nondegeneracy_from_bundle
    (i : FusionCategory.Idx (k := k) (C := RepV))
    (h : BraidedFusionCategory.isTransparent (FusionCategory.simpleObj i)) :
    Nonempty (FusionCategory.simpleObj i ≅ 𝟙_ RepV) :=
  huang_nondegeneracy_of_bridge_assumptions (k := k) (RepV := RepV) i h

noncomputable def modularity_from_bundle
    (hHuang :
      ∀ i : FusionCategory.Idx (k := k) (C := RepV),
        BraidedFusionCategory.isTransparent (FusionCategory.simpleObj i) →
        Nonempty (FusionCategory.simpleObj i ≅ 𝟙_ RepV)) :
    ModularTensorCategory k RepV :=
  modularTensorCategoryOfBridgeAssumptions (k := k) (RepV := RepV) hHuang

end BundledBridge

section BundledBridgeTwist

variable {k : Type u₁} [Field k] [IsAlgClosed k]
variable {RepV : Type u₁} [Category.{v₁} RepV] [MonoidalCategory RepV]
variable [BraidedCategory RepV] [Preadditive RepV] [Linear k RepV]
variable [MonoidalPreadditive RepV] [HasFiniteBiproducts RepV] [RigidCategory RepV]
variable [RibbonFusionCategory k RepV] [HasKernels RepV]

theorem twist_roots_from_bundle
    (i : FusionCategory.Idx (k := k) (C := RepV)) :
    ∃ (n : ℕ) (_ : 0 < n),
      RibbonFusionCategory.twistValue (C := RepV) i ^ n = (1 : k) :=
  twist_roots_of_unity_of_bundle (k := k) (RepV := RepV) i

end BundledBridgeTwist

end StringAlgebra.MTC.Bridge
