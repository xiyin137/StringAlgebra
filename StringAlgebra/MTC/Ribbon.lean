/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.Spherical
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Ribbon Categories

A ribbon category (also called a tortile category) is a braided rigid monoidal
category equipped with a twist (or balancing) natural automorphism θ satisfying
compatibility conditions with the braiding and duals.

Every ribbon category has a canonical pivotal structure and is spherical.

## Main Definitions

* `RibbonCategory` - Braided rigid category with twist
* `RibbonCategory.toPivotalCategory` - Canonical pivotal structure from twist
* `RibbonCategory.toSphericalCategory` - Ribbon categories are spherical

## References

* [V. Turaev, *Quantum Invariants of Knots and 3-Manifolds*]
* [N. Reshetikhin, V. Turaev, *Ribbon graphs and their invariants*]
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*]
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory

universe v₁ u₁

/-- A ribbon category is a braided rigid monoidal category equipped with a
    twist (balancing) θ_X : X ≅ X for each object, satisfying:
    1. Naturality: f ≫ θ_Y = θ_X ≫ f
    2. Tensor compatibility: θ_{X⊗Y} = (β_{Y,X} ∘ β_{X,Y}) ∘ (θ_X ⊗ θ_Y)
    3. Dual compatibility: (θ_X)ᘁ = θ_{Xᘁ}

    The twist encodes the topological spin of anyons in the context of
    topological quantum field theory. -/
class RibbonCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [BraidedCategory C] [RigidCategory C] where
  /-- The twist (or balancing) isomorphism -/
  twist : ∀ (X : C), X ≅ X
  /-- Naturality of the twist -/
  twist_naturality : ∀ {X Y : C} (f : X ⟶ Y),
    f ≫ (twist Y).hom = (twist X).hom ≫ f
  /-- Compatibility with tensor product and braiding:
      θ_{X⊗Y} = β_{Y,X} ∘ β_{X,Y} ∘ (θ_X ⊗ θ_Y) -/
  twist_tensor : ∀ (X Y : C),
    (twist (X ⊗ Y)).hom =
      ((twist X).hom ⊗ₘ (twist Y).hom) ≫
        (β_ X Y).hom ≫ (β_ Y X).hom
  /-- Compatibility with duals: the adjoint mate of the twist on X
      equals the twist on the dual.
      This ensures θ_{X*} = (θ_X)* -/
  twist_dual : ∀ (X : C),
    rightAdjointMate (twist X).hom = (twist Xᘁ).hom

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable [BraidedCategory C] [RigidCategory C] [RibbonCategory C]

namespace RibbonCategory

/-- Shorthand for the twist isomorphism -/
abbrev θ (X : C) : X ≅ X := twist X

/-- The twist on the tensor unit is the identity. -/
theorem twist_unit : (twist (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
  -- Step 1: β²_{𝟙,𝟙} = id (from braiding coherence with unit)
  have hβ_sq : (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 _ := by
    rw [← cancel_mono (λ_ (𝟙_ C)).hom, Category.assoc,
        braiding_leftUnitor, braiding_rightUnitor, Category.id_comp]
  -- Step 2: θ_{𝟙⊗𝟙} = θ_𝟙 ⊗ₘ θ_𝟙 (twist_tensor + β² = id)
  have h_tensor := twist_tensor (𝟙_ C) (𝟙_ C)
  rw [hβ_sq, Category.comp_id] at h_tensor
  -- Step 3: λ ≫ θ = (θ ⊗ₘ θ) ≫ λ (twist_naturality applied to λ)
  have h_nat := twist_naturality (λ_ (𝟙_ C)).hom
  rw [h_tensor] at h_nat
  -- Step 4: (θ ⊗ₘ θ) ≫ λ = λ ≫ θ ≫ θ
  -- Decompose via tensorHom_def', use unitor naturality
  have h_comp : ((twist (𝟙_ C)).hom ⊗ₘ (twist (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom =
      (λ_ (𝟙_ C)).hom ≫ (twist (𝟙_ C)).hom ≫ (twist (𝟙_ C)).hom := by
    rw [tensorHom_def', Category.assoc]
    conv_lhs =>
      rw [unitors_equal, rightUnitor_naturality, ← unitors_equal,
          ← Category.assoc, leftUnitor_naturality, Category.assoc]
  -- Step 5: θ = θ ≫ θ (cancel λ which is epi)
  have h_eq : (twist (𝟙_ C)).hom =
      (twist (𝟙_ C)).hom ≫ (twist (𝟙_ C)).hom := by
    have := h_nat.trans h_comp
    rwa [cancel_epi] at this
  -- Step 6: θ = 𝟙 (idempotent iso is identity)
  have : (twist (𝟙_ C)).hom ≫ (twist (𝟙_ C)).hom =
      (twist (𝟙_ C)).hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact h_eq.symm
  rwa [cancel_epi] at this

/-- The Drinfeld isomorphism u_X : X → (Xᘁ)ᘁ constructed from the braiding.

    u_X is defined as the composition:
      X →[ρ⁻¹] X ⊗ 𝟙 →[id ⊗ coev] X ⊗ (Xᘁ ⊗ (Xᘁ)ᘁ) →[α⁻¹] (X ⊗ Xᘁ) ⊗ (Xᘁ)ᘁ
        →[β ⊗ id] (Xᘁ ⊗ X) ⊗ (Xᘁ)ᘁ →[ev ⊗ id] 𝟙 ⊗ (Xᘁ)ᘁ →[λ] (Xᘁ)ᘁ

    This is a natural isomorphism but NOT monoidal in general. In a ribbon
    category, composing with the inverse twist makes it monoidal. -/
noncomputable def drinfeldIso (X : C) : X ⟶ (Xᘁ)ᘁ :=
  (ρ_ X).inv ≫ (X ◁ η_ Xᘁ (Xᘁ)ᘁ) ≫ (α_ X Xᘁ (Xᘁ)ᘁ).inv ≫
    ((β_ X Xᘁ).hom ▷ (Xᘁ)ᘁ) ≫ (ε_ X Xᘁ ▷ (Xᘁ)ᘁ) ≫ (λ_ (Xᘁ)ᘁ).hom

/-- The inverse of the Drinfeld isomorphism. -/
noncomputable def drinfeldIsoInv (X : C) : (Xᘁ)ᘁ ⟶ X :=
  (ρ_ (Xᘁ)ᘁ).inv ≫ ((Xᘁ)ᘁ ◁ η_ X Xᘁ) ≫ (α_ (Xᘁ)ᘁ X Xᘁ).inv ≫
    ((β_ X (Xᘁ)ᘁ).inv ▷ Xᘁ) ≫ (α_ X (Xᘁ)ᘁ Xᘁ).hom ≫
    (X ◁ ε_ Xᘁ (Xᘁ)ᘁ) ≫ (ρ_ X).hom

/-- A ribbon category has a canonical pivotal structure.

    The pivotal isomorphism j_X : X ≅ (Xᘁ)ᘁ is defined as the composition
    of the inverse twist with the Drinfeld isomorphism:
      j_X = u_X ∘ θ_X⁻¹

    The Drinfeld isomorphism u_X alone is natural but not monoidal. The
    twist correction θ_X⁻¹ is essential: the twist axiom
    θ_{X⊗Y} = c²_{X,Y} ∘ (θ_X ⊗ θ_Y) cancels the monodromy factor in
    u_{X⊗Y}, making j = u ∘ θ⁻¹ monoidal.

    This follows EGNO Proposition 8.10.5 and the nLab: in a braided rigid
    category, there is a canonical bijection between twists and pivotal
    structures, and the pivotal structure corresponding to θ is
    j_X = u_X ∘ θ_X⁻¹. -/
noncomputable instance toPivotalCategory : PivotalCategory C where
  pivotalIso X :=
    { hom := (twist X).inv ≫ drinfeldIso X
      inv := drinfeldIsoInv X ≫ (twist X).hom
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  pivotalIso_naturality f := by sorry
  pivotalIso_leftDuality X := by sorry
  pivotalIso_leftDuality_dual X := by sorry

/-- A ribbon category is spherical with respect to its canonical pivotal structure. -/
noncomputable instance toSphericalCategory : SphericalCategory C where
  spherical f := by
    sorry

/-- The monodromy (double braiding) of X with Y:
    c_{Y,X} ∘ c_{X,Y} : X ⊗ Y → X ⊗ Y -/
def monodromy (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  (β_ X Y).hom ≫ (β_ Y X).hom

/-- The twist satisfies θ_{X⊗Y} = monodromy(X,Y) ∘ (θ_X ⊗ θ_Y) -/
theorem twist_tensor' (X Y : C) :
    (twist (X ⊗ Y)).hom = ((twist X).hom ⊗ₘ (twist Y).hom) ≫ monodromy X Y :=
  twist_tensor X Y

end RibbonCategory

end StringAlgebra.MTC
