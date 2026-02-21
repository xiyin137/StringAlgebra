/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.Trace

/-!
# Spherical Categories

A spherical category is a pivotal category in which the left and right
categorical traces agree for all endomorphisms. This is the key condition
that makes the graphical calculus for pivotal categories fully isotopy-invariant.

## Main Definitions

* `SphericalCategory` - Pivotal category with left trace = right trace

## Main Results

* `spherical_dim` - Left and right quantum dimensions agree
* `dim_dual` - dim(X*) = dim(X) in a spherical category

## References

* [J. Barrett, B. Westbury, *Spherical Categories*]
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], §4.7
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory

universe v₁ u₁

/-- A spherical category is a pivotal category where the left and right
    categorical traces agree for all endomorphisms. This ensures full
    isotopy invariance of the graphical calculus.

    In a spherical category, we can speak of THE trace and THE quantum
    dimension without ambiguity. -/
class SphericalCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [PivotalCategory C] where
  /-- The left and right traces agree for all endomorphisms -/
  spherical : ∀ {X : C} (f : X ⟶ X), leftTrace f = rightTrace f

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
variable [PivotalCategory C] [SphericalCategory C]

/-- The categorical trace in a spherical category (left = right). -/
def trace {X : C} (f : X ⟶ X) : (𝟙_ C ⟶ 𝟙_ C) := leftTrace f

/-- The quantum dimension of an object in a spherical category. -/
def dim (X : C) : (𝟙_ C ⟶ 𝟙_ C) := trace (𝟙 X)

/-- In a spherical category, left and right quantum dimensions agree. -/
theorem spherical_dim (X : C) : leftDim X = rightDim X :=
  SphericalCategory.spherical (𝟙 X)

/-- The quantum dimension of a dual equals the quantum dimension of the object. -/
theorem qdim_dual (X : C) : dim Xᘁ = dim X := by
  sorry

/-- The quantum dimension of the tensor unit is the identity. -/
theorem qdim_unit : dim (𝟙_ C) = 𝟙 (𝟙_ C) := by
  sorry

/-- The quantum dimension is multiplicative under tensor product. -/
theorem qdim_tensor (X Y : C) : dim (X ⊗ Y) = dim X ≫ dim Y := by
  sorry

end StringAlgebra.MTC
