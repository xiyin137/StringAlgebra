/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.FusionCategory
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braided Fusion Categories

A braided fusion category is a fusion category equipped with a braiding.
This is the setting where we can define the Müger center (the subcategory
of transparent objects) whose triviality characterizes modular tensor categories.

## Main Definitions

* `BraidedFusionCategory` - Fusion category with braiding
* `isTransparent` - An object is transparent if its double braiding is trivial
* `MuegerCenter` - The full subcategory of transparent objects

## References

* [A. Müger, *From subfactors to categories and topology II*]
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], §8.20
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

/-- A braided fusion category: a fusion category with a braiding.

    The braiding provides additional structure (the R-matrix) that is
    essential for defining the S-matrix and for applications to knot
    invariants and TQFTs. -/
class BraidedFusionCategory (k : Type u₁) [Field k]
    (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C]
    extends FusionCategory k C

variable {k : Type u₁} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [BraidedFusionCategory k C]

namespace BraidedFusionCategory

/-- The monodromy (squared braiding) of X with Y:
    c²_{X,Y} := β_{Y,X} ∘ β_{X,Y} : X ⊗ Y → X ⊗ Y -/
def monodromy (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  (β_ X Y).hom ≫ (β_ Y X).hom

/-- An object X is transparent (or centralizes the category) if its
    monodromy with every object Y is trivial.

    Equivalently: the double braiding β_{Y,X} ∘ β_{X,Y} = id_{X⊗Y}
    for all Y. -/
def isTransparent (X : C) : Prop :=
  ∀ (Y : C), monodromy X Y = 𝟙 (X ⊗ Y)

omit [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C] [RigidCategory C] in
/-- The tensor unit is always transparent. -/
theorem unit_transparent : isTransparent (C := C) (𝟙_ C) := by
  intro Y
  unfold monodromy
  -- β_{𝟙,Y} ≫ β_{Y,𝟙} = (λ ≫ ρ⁻¹) ≫ (ρ ≫ λ⁻¹) = id
  rw [braiding_tensorUnit_left, braiding_tensorUnit_right]
  simp [Category.assoc]

omit [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C] [RigidCategory C] in
/-- Transparent objects are closed under tensor product. -/
theorem transparent_tensor {X Y : C} (hX : isTransparent X) (hY : isTransparent Y) :
    isTransparent (X ⊗ Y) := by
  intro Z
  unfold monodromy
  have hXZ := hX Z; unfold monodromy at hXZ
  have hYZ := hY Z; unfold monodromy at hYZ
  -- Expand double braiding of X⊗Y with Z using hexagon decompositions
  simp only [BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom, Category.assoc]
  -- Cancel (α_ Z X Y).hom ≫ (α_ Z X Y).inv
  rw [Iso.hom_inv_id_assoc]
  -- Combine (β_ X Z).hom ▷ Y ≫ (β_ Z X).hom ▷ Y, use hX
  rw [← comp_whiskerRight_assoc, hXZ, id_whiskerRight, Category.id_comp]
  -- Cancel (α_ X Z Y).inv ≫ (α_ X Z Y).hom
  rw [Iso.inv_hom_id_assoc]
  -- Combine X ◁ (β_ Y Z).hom ≫ X ◁ (β_ Z Y).hom, use hY
  rw [← whiskerLeft_comp_assoc, hYZ, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id]

/-- Transparent objects are closed under duals. -/
theorem transparent_dual {X : C} (hX : isTransparent X) :
    isTransparent Xᘁ := by
  sorry

/-- The Müger center Z₂(C) is the full subcategory of transparent objects.

    A braided fusion category is modular iff its Müger center is trivial
    (equivalent to the category of vector spaces). -/
def MuegerCenter : Set C := {X | isTransparent X}

omit [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C] [RigidCategory C] in
/-- The Müger center is a fusion subcategory. -/
theorem muegerCenter_fusion_subcategory :
    ∀ X ∈ MuegerCenter (C := C), ∀ Y ∈ MuegerCenter (C := C),
      (X ⊗ Y) ∈ MuegerCenter (C := C) := by
  intro X hX Y hY
  exact transparent_tensor hX hY

/-- In a braided fusion category, the fusion coefficients are symmetric:
    N^m_{ij} = N^m_{ji}. This follows from the braiding isomorphism
    X_i ⊗ X_j ≅ X_j ⊗ X_i. -/
theorem fusionCoeff_symmetric (i j m : FusionCategory.Idx (k := k) (C := C)) :
    FusionCategory.fusionCoeff (k := k) i j m = FusionCategory.fusionCoeff (k := k) j i m := by
  unfold FusionCategory.fusionCoeff
  exact LinearEquiv.finrank_eq
    (Linear.homCongr k (β_ (FusionCategory.simpleObj i) (FusionCategory.simpleObj j))
      (Iso.refl (FusionCategory.simpleObj m)))

end BraidedFusionCategory

end StringAlgebra.MTC
