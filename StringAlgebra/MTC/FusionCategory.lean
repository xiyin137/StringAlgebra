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

/-- Optional coherence assumption for indexing simples:
isomorphic chosen representatives have equal indices. -/
class CanonicalSimpleIndex : Prop where
  eq_of_iso :
    ∀ {i j : Idx (k := k) (C := C)},
      Nonempty (simpleObj (k := k) i ≅ simpleObj (k := k) j) → i = j

theorem simpleObj_iso_of_eq
    {i j : Idx (k := k) (C := C)} (h : i = j) :
    Nonempty (simpleObj (k := k) i ≅ simpleObj (k := k) j) := by
  subst h
  exact ⟨Iso.refl _⟩

@[simp] theorem simpleObj_iso_iff_eq
    [CanonicalSimpleIndex (k := k) (C := C)]
    (i j : Idx (k := k) (C := C)) :
    Nonempty (simpleObj (k := k) i ≅ simpleObj (k := k) j) ↔ i = j := by
  constructor
  · intro h
    exact CanonicalSimpleIndex.eq_of_iso (k := k) (C := C) h
  · intro h
    exact simpleObj_iso_of_eq (k := k) (C := C) h

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

/-- If `X_j` and `X_m` are isomorphic simples, then `N^m_{0,j} = 1`. -/
theorem fusionCoeff_vacuum_iso
    (j m : Idx (k := k) (C := C))
    (h : Nonempty (simpleObj j ≅ simpleObj m)) :
    fusionCoeff (k := k) unitIdx j m = 1 := by
  unfold fusionCoeff
  have iso : simpleObj (k := k) unitIdx ⊗ simpleObj j ≅ simpleObj j :=
    (whiskerRightIso unitIdx_iso (simpleObj j)) ≪≫ (λ_ (simpleObj j))
  rw [LinearEquiv.finrank_eq (Linear.homCongr k iso (Iso.refl (simpleObj m)))]
  haveI := simpleObj_simple (k := k) (C := C) j
  haveI := simpleObj_simple (k := k) (C := C) m
  exact (finrank_hom_simple_simple_eq_one_iff k (simpleObj j) (simpleObj m)).2 h

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

/-- Vacuum fusion as a Kronecker delta on indices, under canonical indexing. -/
theorem fusionCoeff_vacuum_kronecker
    [CanonicalSimpleIndex (k := k) (C := C)]
    (j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) unitIdx j m = if j = m then 1 else 0 := by
  by_cases hEq : j = m
  · subst hEq
    simp [fusionCoeff_vacuum_eq]
  · have hIso : ¬Nonempty (simpleObj j ≅ simpleObj m) := by
      intro h
      exact hEq (CanonicalSimpleIndex.eq_of_iso (k := k) (C := C) h)
    simp [hEq, fusionCoeff_vacuum_ne (k := k) (C := C) j m hIso]

end FusionVacuum

/-! ### Placeholder proof obligations (explicit assumptions) -/

/-- Temporary proof-debt contract for deep fusion-rule identities.
    Replace this class with actual proofs and remove downstream assumptions. -/
class FusionRuleAxioms (k : Type u₁) [Field k]
    (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C] [FusionCategory k C] where
  fusionCoeff_assoc :
    ∀ (i j l m : Idx (k := k) (C := C)),
      ∑ p, fusionCoeff (k := k) i j p * fusionCoeff p l m =
      ∑ q, fusionCoeff (k := k) j l q * fusionCoeff i q m
  fusionCoeff_frobenius :
    ∀ (i j m : Idx (k := k) (C := C)),
      fusionCoeff (k := k) i j m = fusionCoeff m (dualIdx j) i
  fusionCoeff_dual_swap :
    ∀ (i j m : Idx (k := k) (C := C)),
      fusionCoeff (k := k) i j m = fusionCoeff (dualIdx j) (dualIdx i) (dualIdx m)

/-- Placeholder assumption for associativity of fusion coefficients. -/
theorem fusionCoeff_assoc [FusionRuleAxioms (k := k) (C := C)]
    (i j l m : Idx (k := k) (C := C)) :
    ∑ p, fusionCoeff (k := k) i j p * fusionCoeff p l m =
    ∑ q, fusionCoeff (k := k) j l q * fusionCoeff i q m :=
  FusionRuleAxioms.fusionCoeff_assoc (k := k) (C := C) i j l m

/-- Placeholder assumption for Frobenius reciprocity of fusion coefficients. -/
theorem fusionCoeff_frobenius [FusionRuleAxioms (k := k) (C := C)]
    (i j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i j m = fusionCoeff m (dualIdx j) i :=
  FusionRuleAxioms.fusionCoeff_frobenius (k := k) (C := C) i j m

/-- Placeholder assumption for duality/swap symmetry of fusion coefficients. -/
theorem fusionCoeff_dual_swap [FusionRuleAxioms (k := k) (C := C)]
    (i j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i j m = fusionCoeff (dualIdx j) (dualIdx i) (dualIdx m) :=
  FusionRuleAxioms.fusionCoeff_dual_swap (k := k) (C := C) i j m

end FusionCategory

end StringAlgebra.MTC
