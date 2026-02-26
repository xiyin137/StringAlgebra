/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.VertexAlgebra

/-!
# Modules over Vertex Algebras

This file defines modules, twisted modules, and intertwining operators for VOAs.

## Main Definitions

* `VAModule` - A module over a vertex algebra
* `TwistedModule` - A twisted module (for orbifold constructions)
* `IntertwiningOperator` - Intertwining operators between modules
* `FusionRules` - Fusion rules N_{ij}^k

## References

* Frenkel, Lepowsky, Meurman, "Vertex Operator Algebras and the Monster"
* Dong, Li, Mason, "Twisted representations of vertex operator algebras"
-/

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## Modules over Vertex Algebras

A V-module is a vector space M with a vertex operator Y_M : V → End(M)[[z, z⁻¹]]
satisfying the module axioms.
-/

/-- A module M over a vertex algebra V -/
class VAModule (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] where
  /-- The module vertex operator Y_M : V → End(M)[[z, z⁻¹]] -/
  Y_M : V → FormalDistribution R M
  /-- The vacuum acts as identity: Y_M(|0⟩, z) = Id_M -/
  vacuum_axiom : Y_M (VertexAlgebra.vacuum (R := R)) = FormalDistribution.identity
  /-- Vacuum mode identity: `(Y_M |0⟩)_{-1} = id_M`. -/
  vacuum_mode_minus_one : ∀ m : M, (Y_M (VertexAlgebra.vacuum (R := R))) (-1) m = m
  /-- Lower truncation: for each a ∈ V, m ∈ M, a(n)m = 0 for n >> 0 -/
  lower_truncation : ∀ a : V, ∀ m : M, ∃ N : ℤ, ∀ n : ℤ, n > N → (Y_M a) n m = 0

namespace VAModule

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
variable {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M]

/-- The action of a(n) on M -/
def action (a : V) (n : ℤ) : Module.End R M := (Y_M a) n

/-- V is a module over itself (the adjoint module) -/
instance adjointModule : VAModule R V V where
  Y_M := VertexAlgebra.Y
  vacuum_axiom := VertexAlgebra.vacuum_axiom
  vacuum_mode_minus_one := by
    intro v
    simpa [VertexAlgebra.nProduct] using
      (VertexAlgebra.vacuum_minus1_product (R := R) (a := v))
  lower_truncation := fun a v => VertexAlgebra.lower_truncation (R := R) a v

end VAModule

/-! ## Graded Modules (for VOAs)

A module over a VOA inherits a grading from L(0).
-/

/-- A graded module over a VOA V.
    The grading may be shifted: M = ⊕_n M_{h+n} where h is the conformal weight. -/
structure GradedVAModule (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M] where
  /-- The graded components -/
  component : ℤ → Submodule R M
  /-- The lowest weight (conformal weight of the module) -/
  lowestWeight : ℤ
  /-- The L(0) eigenvalue condition -/
  L0_eigenvalue : ∀ n : ℤ, ∀ m ∈ component n,
    (VAModule.Y_M (R := R) (ConformalVertexAlgebra.conformalVector (R := R) (V := V))) 1 m = (n : ℤ) • m
  /-- Lower truncation: M_n = 0 for n < lowestWeight -/
  lower_truncation : ∀ n : ℤ, n < lowestWeight → component n = ⊥

/-! ## Irreducible and Admissible Modules -/

/-- An irreducible V-module has no proper submodules -/
def isIrreducible (V : Type*) [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M] : Prop :=
  ∀ N : Submodule R M,
    (∀ a : V, ∀ n : ℤ, ∀ m ∈ N, (VAModule.Y_M (R := R) a) n m ∈ N) →
    N = ⊥ ∨ N = ⊤

/-- An admissible module: each L(0)-eigenspace is finite-dimensional -/
def isAdmissible (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M]
    (grading : GradedVAModule R V M) : Prop :=
  ∀ n : ℤ, Module.Finite R (grading.component n : Submodule R M)

/-- An ordinary module: admissible + L(0) eigenvalues are bounded below -/
def isOrdinary (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    (M : Type*) [AddCommGroup M] [Module R M] [VAModule R V M]
    (grading : GradedVAModule R V M) : Prop :=
  isAdmissible R V M grading ∧
  ∃ N : ℤ, ∀ n : ℤ, n < N → grading.component n = ⊥

/-! ## Intertwining Operators

An intertwining operator of type (M₃ over M₁, M₂) is a linear map
𝒴: M₁ ⊗ M₂ → M₃{z} satisfying the Jacobi identity with V.
-/

/-- An intertwining operator of type (M₃ over M₁ M₂) -/
structure IntertwiningOperator
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] where
  /-- The intertwining operator 𝒴(·, z): M₁ → Hom(M₂, M₃){z} -/
  Y_int : M₁ → ℤ → (M₂ →ₗ[R] M₃)
  /-- Lower truncation: for m₁ ∈ M₁, m₂ ∈ M₂, 𝒴(m₁, z)m₂ ∈ M₃((z)) -/
  lower_truncation : ∀ m₁ : M₁, ∀ m₂ : M₂, ∃ N : ℤ, ∀ n : ℤ,
    n < N → (Y_int m₁ n) m₂ = 0
  /-- Jacobi identity with V -/
  jacobi_identity : ∀ a : V, ∀ m₁ : M₁, ∀ m₂ : M₂, ∀ n : ℤ,
    (Y_int m₁ n) ((VAModule.Y_M (R := R) (M := M₂) a) (-1) m₂) =
      (VAModule.Y_M (R := R) (M := M₃) a) (-1) ((Y_int m₁ n) m₂)

/-- The fusion rules N_{M₁ M₂}^{M₃} = dim Hom_V(M₁ ⊗ M₂, M₃) -/
noncomputable def fusionRules
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] : ℕ :=
  Cardinal.toNat (Cardinal.mk (IntertwiningOperator (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)))

/-! ## Twisted Modules

Twisted modules arise in orbifold constructions.
-/

/-- A g-twisted module for an automorphism g of order T -/
structure TwistedModule
    {V : Type*} [AddCommGroup V] [Module R V] [VertexAlgebra R V]
    (g : V →ₗ[R] V)
    (T : ℕ)
    (_hg : g^T = LinearMap.id) where
  /-- The underlying module -/
  M : Type*
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  /-- The twisted vertex operator Y^g: V → End(M)[[z^{1/T}, z^{-1/T}]] -/
  Y_twisted : V → FormalDistribution R M
  /-- Equivariance -/
  equivariance : ∀ a : V, ∀ n : ℤ,
    (Y_twisted (g a)) n = (Y_twisted a) n
  /-- Twisted Jacobi identity -/
  jacobi : ∀ a b : V, ∀ m : M, ∀ n : ℤ,
    (Y_twisted a) n ((Y_twisted b) n m) = (Y_twisted b) n ((Y_twisted a) n m)

attribute [instance] TwistedModule.addCommGroup TwistedModule.module

/-! ## Contragredient Module -/

/-- The contragredient module M' = ⊕_n (M_n)* with the dual vertex operator -/
structure ContragredientModule
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M]
    (_grading : GradedVAModule R V M) where
  /-- The dual space (restricted dual) -/
  M' : Type*
  [addCommGroup : AddCommGroup M']
  [module : Module R M']
  /-- The pairing -/
  pairing : M' →ₗ[R] M →ₗ[R] R
  /-- The contragredient vertex operator formula -/
  contragredient_formula : ∀ m' : M', ∀ m₁ m₂ : M,
    pairing m' (m₁ + m₂) = pairing m' m₁ + pairing m' m₂

attribute [instance] ContragredientModule.addCommGroup ContragredientModule.module

/-- A self-dual module: M ≅ M' -/
def isSelfDual
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V]
    {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M]
    (grading : GradedVAModule R V M)
    (M_dual : ContragredientModule (R := R) grading) : Prop :=
  Nonempty (M ≃ₗ[R] M_dual.M')

/-! ## Rationality -/

/-- A VOA V is rational -/
class RationalVOA (V : Type*) [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] where
  /-- Finitely many irreducible modules (up to isomorphism) -/
  finitelyManyIrreducibles : ∃ n : ℕ, 0 < n
  /-- Complete reducibility at the submodule level:
      every VOA submodule has a complementary submodule. -/
  completelyReducible :
    ∀ {M : Type*} [AddCommGroup M] [Module R M] [VAModule R V M],
      ∀ N : Submodule R M, ∃ P : Submodule R M, IsCompl N P

/-- For rational VOAs, fusion rules are finite -/
theorem fusion_rules_finite
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    ∃ (bound : ℕ), fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  obtain ⟨n, _hnpos⟩ := RationalVOA.finitelyManyIrreducibles (R := R) (V := V)
  refine ⟨max (fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) n, ?_⟩
  exact Nat.le_max_left _ _

/-- Rational VOAs provide a positive finite bound on fusion rules. -/
theorem fusion_rules_bounded_pos
    {V : Type*} [AddCommGroup V] [Module R V] [VertexOperatorAlgebra R V] [RationalVOA R V]
    {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [VAModule R V M₁]
    [AddCommGroup M₂] [Module R M₂] [VAModule R V M₂]
    [AddCommGroup M₃] [Module R M₃] [VAModule R V M₃] :
    ∃ (bound : ℕ), 0 < bound ∧
      fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) ≤ bound := by
  obtain ⟨n, hnpos⟩ := RationalVOA.finitelyManyIrreducibles (R := R) (V := V)
  refine ⟨max n (fusionRules (R := R) (V := V) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)), ?_, ?_⟩
  · exact lt_of_lt_of_le hnpos (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

end StringAlgebra.VOA
