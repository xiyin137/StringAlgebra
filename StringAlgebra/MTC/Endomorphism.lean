/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.FusionCategory
import Mathlib.CategoryTheory.Preadditive.Schur

/-!
# Scalar Extraction for Endomorphisms of Simple Objects

For a simple object X in a k-linear category over an algebraically closed field k,
Schur's lemma implies that every endomorphism f : X → X is of the form c • id_X
for a unique scalar c ∈ k (since End(X) is 1-dimensional over k).

This module provides the scalar extraction function and its basic properties.

## Main Definitions

* `scalarOfEndo` - Extract the scalar c such that f = c • id_X
* `scalarOfEndUnit` - Specialization to the tensor unit
* `scalarOfEndSimple` - Specialization to fusion category simple objects

## References

* Schur's lemma: `CategoryTheory.endomorphism_simple_eq_smul_id`
* `CategoryTheory.finrank_endomorphism_simple_eq_one`
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

section ScalarExtraction

variable {k : Type u₁} [Field k] [IsAlgClosed k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [HasKernels C]

/-- Extract the unique scalar from an endomorphism of a simple object.

    By Schur's lemma over an algebraically closed field, every endomorphism
    f : X → X of a simple object X equals c • id_X for a unique c ∈ k.
    This function extracts that c. -/
noncomputable def scalarOfEndo {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (f : X ⟶ X) : k :=
  (endomorphism_simple_eq_smul_id k f).choose

/-- The scalar extraction satisfies f = (scalarOfEndo f) • id_X. -/
theorem scalarOfEndo_spec {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (f : X ⟶ X) :
    scalarOfEndo (k := k) f • 𝟙 X = f :=
  (endomorphism_simple_eq_smul_id k f).choose_spec

/-- The scalar of the identity is 1. -/
theorem scalarOfEndo_id {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] :
    scalarOfEndo (k := k) (𝟙 X : X ⟶ X) = 1 := by
  have h := scalarOfEndo_spec (k := k) (𝟙 X : X ⟶ X)
  by_contra hne
  have h1 : (scalarOfEndo (k := k) (𝟙 X : X ⟶ X) - 1) • 𝟙 X = (0 : X ⟶ X) := by
    rw [sub_smul, one_smul, h, sub_self]
  rw [smul_eq_zero] at h1
  cases h1 with
  | inl h => exact hne (sub_eq_zero.mp h)
  | inr h => exact id_nonzero X h

end ScalarExtraction

section FusionScalars

variable {k : Type u₁} [Field k] [IsAlgClosed k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [HasKernels C]
variable [FusionCategory k C]

/-- Scalar extraction for endomorphisms of the tensor unit.
    The unit is simple in a fusion category, so Schur's lemma applies. -/
noncomputable def scalarOfEndUnit (f : 𝟙_ C ⟶ 𝟙_ C) : k :=
  letI : Simple (𝟙_ C) := FusionCategory.unit_simple (k := k)
  letI : FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C) :=
    FusionCategory.finiteDimensionalHom (k := k) (𝟙_ C) (𝟙_ C)
  scalarOfEndo f

/-- Scalar extraction for endomorphisms of a fusion category simple object. -/
noncomputable def scalarOfEndSimple
    (i : FusionCategory.Idx (k := k) (C := C))
    (f : FusionCategory.simpleObj i ⟶ FusionCategory.simpleObj i) : k :=
  letI : Simple (FusionCategory.simpleObj i) :=
    FusionCategory.simpleObj_simple (k := k) i
  letI : FiniteDimensional k
      (FusionCategory.simpleObj i ⟶ FusionCategory.simpleObj i) :=
    FusionCategory.finiteDimensionalHom (k := k)
      (FusionCategory.simpleObj i) (FusionCategory.simpleObj i)
  scalarOfEndo f

/-- The scalar extraction for the unit satisfies the expected equation:
    scalarOfEndUnit f • 𝟙 (𝟙_ C) = f -/
theorem scalarOfEndUnit_spec (f : 𝟙_ C ⟶ 𝟙_ C) :
    (scalarOfEndUnit f : k) • 𝟙 (𝟙_ C) = f := by
  letI : Simple (𝟙_ C) := FusionCategory.unit_simple (k := k)
  letI : FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C) :=
    FusionCategory.finiteDimensionalHom (k := k) (𝟙_ C) (𝟙_ C)
  exact scalarOfEndo_spec f

/-- The scalar extraction for simples satisfies the expected equation:
    scalarOfEndSimple i f • 𝟙 (simpleObj i) = f -/
theorem scalarOfEndSimple_spec
    (i : FusionCategory.Idx (k := k) (C := C))
    (f : FusionCategory.simpleObj (k := k) i ⟶ FusionCategory.simpleObj (k := k) i) :
    (scalarOfEndSimple i f : k) • 𝟙 (FusionCategory.simpleObj (k := k) i) = f := by
  letI : Simple (FusionCategory.simpleObj i) :=
    FusionCategory.simpleObj_simple (k := k) i
  letI : FiniteDimensional k
      (FusionCategory.simpleObj i ⟶ FusionCategory.simpleObj i) :=
    FusionCategory.finiteDimensionalHom (k := k)
      (FusionCategory.simpleObj i) (FusionCategory.simpleObj i)
  exact scalarOfEndo_spec f

end FusionScalars

end StringAlgebra.MTC
