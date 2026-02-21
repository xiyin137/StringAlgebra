/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.Semisimple
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Fusion Categories

A fusion category is a k-linear semisimple rigid monoidal category with finitely
many isomorphism classes of simple objects, finite-dimensional Hom spaces, and
simple tensor unit.

## Main Definitions

* `FusionCategory` - The main class combining all axioms
* `FusionCategory.fusionCoeff` - The fusion coefficients N^m_{ij} = dim_k Hom(X_i ⊗ X_j, X_m)

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], Ch. 4
* [P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*]
-/

namespace StringAlgebra.MTC

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ u₁

/-- A fusion category over a field k is a k-linear, semisimple, rigid monoidal
    category with finitely many simple isoclasses, finite-dimensional Homs,
    and simple tensor unit.

    The data includes:
    - A finite type `Idx` indexing the simple isoclasses
    - Representative simple objects `simpleObj i` for each index
    - A distinguished unit index with an explicit isomorphism to the unit
    - A duality operation on indices with explicit isomorphisms to duals -/
class FusionCategory (k : Type u₁) [Field k]
    (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [Preadditive C] [Linear k C]
    [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C] where
  /-- The finite type indexing simple isoclasses -/
  Idx : Type
  /-- The indexing type is finite -/
  [idx_fintype : Fintype Idx]
  /-- Decidable equality on the indexing type -/
  [idx_decidableEq : DecidableEq Idx]
  /-- Representative simple object for each index -/
  simpleObj : Idx → C
  /-- Each representative is simple -/
  simpleObj_simple : ∀ (i : Idx), Simple (simpleObj i)
  /-- Every simple is isomorphic to some representative -/
  simpleObj_exhaustive : ∀ (X : C), Simple X → ∃ (i : Idx), Nonempty (X ≅ simpleObj i)
  /-- Hom spaces are finite-dimensional k-vector spaces -/
  finiteDimensionalHom : ∀ (X Y : C), Module.Finite k (X ⟶ Y)
  /-- The tensor unit is a simple object -/
  unit_simple : Simple (𝟙_ C)
  /-- Distinguished index for the unit -/
  unitIdx : Idx
  /-- An isomorphism between the unit representative and the tensor unit -/
  unitIdx_iso : simpleObj unitIdx ≅ 𝟙_ C
  /-- Duality operation on indices -/
  dualIdx : Idx → Idx
  /-- The dual of X_i is isomorphic to X_{dualIdx i} -/
  dualIdx_iso : ∀ (i : Idx), (simpleObj i)ᘁ ≅ simpleObj (dualIdx i)

-- Explicit instances to help typeclass resolution
noncomputable instance instFintypeFusionIdx {k : Type u₁} [Field k]
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C]
    [FusionCategory k C] :
    Fintype (FusionCategory.Idx (k := k) (C := C)) :=
  FusionCategory.idx_fintype

instance instDecidableEqFusionIdx {k : Type u₁} [Field k]
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C]
    [FusionCategory k C] :
    DecidableEq (FusionCategory.Idx (k := k) (C := C)) :=
  FusionCategory.idx_decidableEq

variable {k : Type u₁} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [FusionCategory k C]

namespace FusionCategory

/-- The rank of the fusion category (number of simple isoclasses). -/
noncomputable def rank : ℕ := Fintype.card (Idx (k := k) (C := C))

/-- The fusion coefficients N^m_{ij} = dim_k Hom(X_i ⊗ X_j, X_m).

    This is the dimension of the space of morphisms from the tensor product
    of simple objects X_i and X_j to the simple object X_m. By semisimplicity,
    this equals the multiplicity of X_m in the decomposition of X_i ⊗ X_j. -/
noncomputable def fusionCoeff (i j m : Idx (k := k) (C := C)) : ℕ :=
  Module.finrank k (simpleObj i ⊗ simpleObj j ⟶ simpleObj m)

/-- The dual of a simple object is simple. -/
theorem dual_simple (i : Idx (k := k) (C := C)) : Simple (simpleObj i)ᘁ := by
  haveI := simpleObj_simple (k := k) (C := C) (dualIdx i)
  exact Simple.of_iso (dualIdx_iso i)

section FusionVacuum

variable [IsAlgClosed k] [HasKernels C]

/-- Module.Finite instance for Hom spaces in a fusion category. -/
instance instFiniteDimensionalHom (X Y : C) : Module.Finite k (X ⟶ Y) :=
  finiteDimensionalHom X Y

/-- Fusion with the vacuum: N^m_{0,j} = δ_{m,j}.
    More precisely, if X_j ≅ X_m then N^m_{0j} = 1, otherwise 0. -/
theorem fusionCoeff_vacuum_eq (j : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) unitIdx j j = 1 := by
  unfold fusionCoeff
  -- simpleObj unitIdx ⊗ simpleObj j ≅ 𝟙 ⊗ simpleObj j ≅ simpleObj j
  have iso : simpleObj (k := k) unitIdx ⊗ simpleObj j ≅ simpleObj j :=
    (whiskerRightIso unitIdx_iso (simpleObj j)) ≪≫ (λ_ (simpleObj j))
  -- Transfer finrank via linear equiv
  rw [LinearEquiv.finrank_eq (Linear.homCongr k iso (Iso.refl (simpleObj j)))]
  -- Now finrank k (simpleObj j ⟶ simpleObj j) = 1 by Schur
  haveI := simpleObj_simple (k := k) (C := C) j
  exact finrank_endomorphism_simple_eq_one k (simpleObj j)

omit [IsAlgClosed k] in
theorem fusionCoeff_vacuum_ne (j m : Idx (k := k) (C := C))
    (h : ¬Nonempty (simpleObj j ≅ simpleObj m)) :
    fusionCoeff (k := k) unitIdx j m = 0 := by
  unfold fusionCoeff
  have iso : simpleObj (k := k) unitIdx ⊗ simpleObj j ≅ simpleObj j :=
    (whiskerRightIso unitIdx_iso (simpleObj j)) ≪≫ (λ_ (simpleObj j))
  rw [LinearEquiv.finrank_eq (Linear.homCongr k iso (Iso.refl (simpleObj m)))]
  haveI := simpleObj_simple (k := k) (C := C) j
  haveI := simpleObj_simple (k := k) (C := C) m
  apply finrank_hom_simple_simple_eq_zero_of_not_iso
  intro i; exact h ⟨i⟩

end FusionVacuum

/-- Fusion is associative:
    ∑_p N^p_{ij} · N^m_{pk} = ∑_q N^q_{jk} · N^m_{iq} -/
theorem fusionCoeff_assoc (i j l m : Idx (k := k) (C := C)) :
    ∑ p, fusionCoeff (k := k) i j p * fusionCoeff p l m =
    ∑ q, fusionCoeff (k := k) j l q * fusionCoeff i q m := by
  sorry

/-- Frobenius reciprocity: N^m_{ij} = N^i_{m, j*} where j* = dualIdx j.

    This follows from the tensor-hom adjunction for right duals:
    Hom(X_i ⊗ X_j, X_m) ≅ Hom(X_i, X_m ⊗ (X_j)ᘁ) ≅ Hom(X_i, X_m ⊗ X_{j*})
    and in a semisimple category, dim Hom(X_i, Y) = dim Hom(Y, X_i)
    (both count the multiplicity of X_i in Y). -/
theorem fusionCoeff_frobenius (i j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i j m = fusionCoeff m (dualIdx j) i := by
  sorry

/-- Duality symmetry: N^m_{ij} = N^{m*}_{j*,i*}, where all indices are dualized
    and i, j are swapped.

    This follows from the contravariant duality functor (-)ᘁ:
    Hom(X_i ⊗ X_j, X_m) ≅ Hom(X_mᘁ, (X_i ⊗ X_j)ᘁ) ≅ Hom(X_mᘁ, X_jᘁ ⊗ X_iᘁ)
    = Hom(X_{m*}, X_{j*} ⊗ X_{i*}) and in a semisimple category the two directions
    of Hom give the same dimension. -/
theorem fusionCoeff_dual_swap (i j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i j m = fusionCoeff (dualIdx j) (dualIdx i) (dualIdx m) := by
  sorry

end FusionCategory

end StringAlgebra.MTC
