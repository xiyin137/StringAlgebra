/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.Spherical
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

-- Disable diamond-causing instances from Rigid.Braided:
-- These create competing RightRigidCategory/LeftRigidCategory instances
-- that conflict with the direct path through RigidCategory.
-- We only need `exactPairing_swap` from that import.
attribute [-instance] CategoryTheory.BraidedCategory.rightRigidCategoryOfLeftRigidCategory
attribute [-instance] CategoryTheory.BraidedCategory.leftRigidCategoryOfRightRigidCategory
attribute [-instance] CategoryTheory.BraidedCategory.rigidCategoryOfRightRigidCategory
attribute [-instance] CategoryTheory.BraidedCategory.rigidCategoryOfLeftRigidCategory

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

open CategoryTheory MonoidalCategory BraidedCategory

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

/-- The Drinfeld isomorphism u_X : X ≅ (Xᘁ)ᘁ constructed from the braiding.

    This is the canonical isomorphism between two right duals of Xᘁ:
    - The standard right dual (Xᘁ)ᘁ (from `HasRightDual Xᘁ`)
    - X itself, which becomes a right dual of Xᘁ via the braiding
      (from `BraidedCategory.exactPairing_swap X Xᘁ : ExactPairing Xᘁ X`)

    Concretely, the forward map u_X : X → (Xᘁ)ᘁ is:
      X →[ρ⁻¹] X ⊗ 𝟙 →[id ⊗ coev] X ⊗ (Xᘁ ⊗ (Xᘁ)ᘁ) →[α⁻¹] (X ⊗ Xᘁ) ⊗ (Xᘁ)ᘁ
        →[β ⊗ id] (Xᘁ ⊗ X) ⊗ (Xᘁ)ᘁ →[ev ⊗ id] 𝟙 ⊗ (Xᘁ)ᘁ →[λ] (Xᘁ)ᘁ

    The isomorphism property (hom_inv_id and inv_hom_id) follows from
    Mathlib's `rightDualIso` applied to the standard and braiding-swapped
    exact pairings for Xᘁ. -/
noncomputable def drinfeldIsoIso (X : C) : X ≅ (Xᘁ)ᘁ :=
  (rightDualIso
    (inferInstance : ExactPairing Xᘁ (Xᘁ)ᘁ)
    (BraidedCategory.exactPairing_swap X Xᘁ)).symm

/-- Injectivity: if two morphisms to (Yᘁ)ᘁ agree after right-whiskering
    with Yᘁ and composing with evaluation, they are equal. This follows
    from the fact that `tensorRightHomEquiv` is an equivalence. -/
private theorem whiskerRight_eval_cancel {Z : C} {Y : C}
    {f g : Z ⟶ (Yᘁ)ᘁ}
    (h : f ▷ Yᘁ ≫ ε_ Yᘁ (Yᘁ)ᘁ = g ▷ Yᘁ ≫ ε_ Yᘁ (Yᘁ)ᘁ) : f = g := by
  have h2 := congr_arg (tensorRightHomEquiv Z Yᘁ (Yᘁ)ᘁ (𝟙_ C)) h
  simp only [tensorRightHomEquiv_whiskerRight_comp_evaluation] at h2
  exact (cancel_mono (λ_ _).inv).mp h2

/-- The Drinfeld isomorphism evaluation property:
    u_X ▷ Xᘁ ≫ ε_{Xᘁ,(Xᘁ)ᘁ} = β_{X,Xᘁ} ≫ ε_{X,Xᘁ}

    This key property says that composing the Drinfeld iso with evaluation
    yields the braiding composed with evaluation. It follows from the
    construction of u_X via `rightAdjointMate (𝟙 Xᘁ)` with mixed
    HasRightDual instances (standard and swap). -/
private theorem drinfeldIsoIso_eval (X : C) :
    (drinfeldIsoIso X).hom ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  -- drinfeldIsoIso X = (rightDualIso p_std p_swap).symm
  -- so .hom = rightDualIso.inv = @rightAdjointMate ... ⟨(Xᘁ)ᘁ, p_std⟩ ⟨X, p_swap⟩ (𝟙 Xᘁ)
  -- rightAdjointMate_comp_evaluation with these instances gives the result
  letI : ExactPairing Xᘁ X := BraidedCategory.exactPairing_swap X Xᘁ
  have key := @rightAdjointMate_comp_evaluation C _ _ Xᘁ Xᘁ
    inferInstance (⟨X⟩ : HasRightDual Xᘁ) (𝟙 Xᘁ)
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp] at key
  exact key

/-- The Drinfeld isomorphism coevaluation property:
    η_{Xᘁ,(Xᘁ)ᘁ} ≫ Xᘁ ◁ u_X⁻¹ = η_swap = η_{X,Xᘁ} ≫ (β_{Xᘁ,X})⁻¹

    Dual to `drinfeldIsoIso_eval`. -/
private theorem drinfeldIsoIso_coeval (X : C) :
    η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ (drinfeldIsoIso X).inv =
      η_ X Xᘁ ≫ (β_ Xᘁ X).inv := by
  letI : ExactPairing Xᘁ X := BraidedCategory.exactPairing_swap X Xᘁ
  have key := @coevaluation_comp_rightAdjointMate C _ _ Xᘁ Xᘁ
    (⟨X⟩ : HasRightDual Xᘁ) inferInstance (𝟙 Xᘁ)
  simp only [id_whiskerRight, Category.comp_id] at key
  exact key

/-- The Drinfeld isomorphism is natural: f ≫ u_Y = u_X ≫ fᘁᘁ.

    Proof strategy (testing + injectivity):
    Both sides, when right-whiskered with Yᘁ and composed with ε_{Yᘁ,(Yᘁ)ᘁ},
    give (β_{X,Yᘁ}).hom ≫ fᘁ ▷ X ≫ ε_{X,Xᘁ}. By `whiskerRight_eval_cancel`,
    the two sides are equal. -/
private theorem drinfeldIsoIso_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (drinfeldIsoIso Y).hom =
      (drinfeldIsoIso X).hom ≫ rightAdjointMate (rightAdjointMate f) := by
  apply whiskerRight_eval_cancel
  simp only [comp_whiskerRight, Category.assoc]
  -- Both sides reduce to (β_ X Yᘁ).hom ≫ fᘁ ▷ X ≫ ε_ X Xᘁ
  trans (β_ X Yᘁ).hom ≫ (rightAdjointMate f) ▷ X ≫ ε_ X Xᘁ
  · -- LHS: f ▷ Yᘁ ≫ u_Y ▷ Yᘁ ≫ ε_ → ... → (β_ X Yᘁ).hom ≫ fᘁ ▷ X ≫ ε_
    rw [drinfeldIsoIso_eval, braiding_naturality_left_assoc,
        ← rightAdjointMate_comp_evaluation]
  · -- RHS: u_X ▷ Yᘁ ≫ fᘁᘁ ▷ Yᘁ ≫ ε_ → ... → (β_ X Yᘁ).hom ≫ fᘁ ▷ X ≫ ε_
    symm
    rw [rightAdjointMate_comp_evaluation (rightAdjointMate f),
        ← whisker_exchange_assoc, drinfeldIsoIso_eval,
        braiding_naturality_right_assoc]

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
  pivotalIso X := (twist X).symm ≪≫ drinfeldIsoIso X
  pivotalIso_naturality {X Y} f := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    have twist_inv_nat : f ≫ (twist Y).inv = (twist X).inv ≫ f := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact (twist_naturality f).symm
    conv_lhs => rw [← Category.assoc, twist_inv_nat, Category.assoc]
    rw [drinfeldIsoIso_naturality]
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
