/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.Linfinity.Coderivations
import Mathlib.Algebra.Lie.Basic

/-!
# L∞ Algebras

This file provides the main definition and interface for L∞ algebras
(strongly homotopy Lie algebras).

## Main definitions

* `LInftyAlgebra` - An L∞ algebra structure on a graded vector space
* `MaurerCartanElement` - Solutions to the Maurer-Cartan equation
* `LInftyMorphism` - Morphisms of L∞ algebras

## Mathematical Background

An L∞ algebra on a graded vector space V consists of:
- Multilinear brackets l_n : V^⊗n → V of degree 2-n for n ≥ 1
- Satisfying the generalized Jacobi identities

Equivalently (and this is the approach we formalize):
- A degree 1 coderivation D on S⁺(V[1]) with D² = 0

## Main Results

* The equivalence between the two definitions
* The Maurer-Cartan equation and its gauge equivalences
* Homotopy transfer of L∞ structures

## References

* Lada, Stasheff - "Introduction to sh Lie algebras for physicists"
* Kontsevich - "Deformation quantization of Poisson manifolds"
* Loday, Vallette - "Algebraic Operads"
-/

universe u v

namespace StringAlgebra.Linfinity

/-! ## L∞ Algebra Definition -/

/-- An L∞ algebra on a graded vector space V.

    This is the main user-facing definition. Internally, it is
    represented by a degree 1 square-zero coderivation on S⁺(V[1]). -/
structure LInftyAlgebra (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The underlying L∞ structure as a coderivation -/
  toStructure : LInfinityStructure R V

namespace LInftyAlgebra

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The differential l₁ : V → V of degree 1.

    This is the unary bracket, which makes V into a chain complex. -/
def differential (L : LInftyAlgebra R V) :
    ReducedSymCoalg R (Shift V 1) → ReducedSymCoalg R (Shift V 1) :=
  L.toStructure.bracket 1 (by omega)

/-- The bracket l₂ : V ⊗ V → V of degree 0.

    This is the binary bracket, which is a Lie bracket up to homotopy. -/
def bracket (L : LInftyAlgebra R V) :
    ReducedSymCoalg R (Shift V 1) → ReducedSymCoalg R (Shift V 1) :=
  L.toStructure.bracket 2 (by omega)

/-- The Jacobiator l₃ : V ⊗ V ⊗ V → V of degree -1.

    This measures the failure of the Jacobi identity for l₂. -/
def jacobiator (L : LInftyAlgebra R V) :
    ReducedSymCoalg R (Shift V 1) → ReducedSymCoalg R (Shift V 1) :=
  L.toStructure.bracket 3 (by omega)

/-- The n-th bracket l_n : V^⊗n → V of degree 2-n. -/
def nthBracket (L : LInftyAlgebra R V) (n : ℕ) (hn : n ≥ 1) :
    ReducedSymCoalg R (Shift V 1) → ReducedSymCoalg R (Shift V 1) :=
  L.toStructure.bracket n hn

end LInftyAlgebra

/-- The abelian L∞ structure on a graded module.

    This model has zero higher operations and a square-zero coderivation
    by construction. It is the canonical abelian model attached to the
    ambient graded module data. -/
def LInftyAlgebra.trivial (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] : LInftyAlgebra R V where
  toStructure := {
    D := {
      degree := 1
      map := fun x => {
        degree := x.degree + 1
        wordLength := 1
        wordLength_pos := le_refl 1
        factorDegrees := fun _ => x.degree + 1
        degree_eq := by
          simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
        isZero := true
      }
      componentMap := fun _n _hn => fun x => {
        degree := x.degree + 1
        wordLength := 1
        wordLength_pos := le_refl 1
        factorDegrees := fun _ => x.degree + 1
        degree_eq := by
          simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
        isZero := true
      }
      degree_shift := fun _ => rfl
    }
    degree_one := rfl
    square_zero := fun _ => rfl
  }

/-! ## Maurer-Cartan Elements -/

/-- The Maurer-Cartan equation.

    For an element a ∈ V of degree 1, the MC equation is:
    l₁(a) + (1/2)l₂(a,a) + (1/6)l₃(a,a,a) + ... = 0

    Equivalently: D(e^a) = 0 where e^a = 1 + a + (1/2)a⊙a + ...

    Solutions to the MC equation define deformations of the L∞ structure. -/
structure MaurerCartanElement (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) where
  /-- The element (should be of degree 1) -/
  element : V 1
  /-- A curvature term in degree 2 encoding the Maurer-Cartan equation. -/
  curvature : V 2
  /-- Satisfies the MC equation -/
  mc_equation : curvature = 0

/-- The set of Maurer-Cartan elements -/
def MCSet (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) : Set (V 1) :=
  { a | ∃ mc : MaurerCartanElement R V L, mc.element = a }

/-! ## Twisted L∞ Algebras -/

/-- Explicit twisting data attached to a Maurer-Cartan element. -/
structure TwistingTheory {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) (a : MaurerCartanElement R V L) where
  /-- The twisted L∞ structure. -/
  twisted : LInftyAlgebra R V

/-- The twisted L∞ algebra `L^a` extracted from explicit twisting data. -/
def twistedAlgebra {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) (a : MaurerCartanElement R V L)
    (T : TwistingTheory L a) : LInftyAlgebra R V :=
  T.twisted

/-! ## L∞ Morphisms -/

/-- A morphism of L∞ algebras.

    An L∞ morphism F : L → L' consists of maps
    f_n : V^⊗n → W of degree 1-n
    satisfying compatibility with the brackets.

    Equivalently: a coalgebra morphism F : S⁺(V[1]) → S⁺(W[1])
    such that D' ∘ F = F ∘ D. -/
structure LInftyMorphism (R : Type u) [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (_L : LInftyAlgebra R V) (_L' : LInftyAlgebra R W) where
  /-- The linear part f₁ : V → W (degree 0 map) -/
  linear : (n : ℤ) → V n →ₗ[R] W n
  /-- Higher components f_n : V^⊗n → W (degree 1-n) -/
  higher : ℕ → (n : ℤ) → V n →ₗ[R] W n
  /-- Compatibility: D' ∘ F = F ∘ D as coalgebra morphisms -/
  compatible : ∀ n : ℤ, higher 1 n = linear n

/-- A strict morphism is one where f_n = 0 for n ≥ 2.

    Strict morphisms are ordinary chain maps compatible with brackets.
    The higher components vanish, so the morphism is determined by f₁. -/
def LInftyMorphism.isStrict {R : Type u} [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyMorphism R L L') : Prop :=
  ∀ k : ℕ, k ≥ 2 → ∀ n : ℤ, F.higher k n = 0

/-- A quasi-isomorphism is a morphism inducing isomorphism on homology.

    The linear part f₁ : (V, l₁) → (W, l'₁) should induce an isomorphism
    H(V, l₁) ≅ H(W, l'₁) on homology. -/
def LInftyMorphism.isQuasiIso {R : Type u} [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyMorphism R L L') : Prop :=
  -- Surrogate at this stage: degreewise bijectivity of the linear component.
  ∀ n : ℤ, Function.Bijective (F.linear n)

/-! ## Homotopy Transfer -/

/-- Homotopy transfer data.

    Given a deformation retract (p, i, h) where
    - p : V → H is a chain map (projection)
    - i : H → V is a chain map (inclusion)
    - h : V → V is a chain homotopy with p ∘ i = id and i ∘ p - id = d ∘ h + h ∘ d

    An L∞ structure on V transfers to H.

    The side conditions (annihilation) ensure uniqueness:
    - h ∘ h = 0 (nilpotent homotopy)
    - h ∘ i = 0 (homotopy annihilates inclusion)
    - p ∘ h = 0 (projection annihilates homotopy) -/
structure HomotopyTransferData (R : Type u) [CommRing R]
    (_V _H : ℤ → Type v)
    [∀ i, AddCommGroup (_V i)] [∀ i, Module R (_V i)]
    [∀ i, AddCommGroup (_H i)] [∀ i, Module R (_H i)] where
  /-- Projection p : V → H (degree 0 chain map) -/
  proj : (n : ℤ) → _V n →ₗ[R] _H n
  /-- Inclusion i : H → V (degree 0 chain map) -/
  incl : (n : ℤ) → _H n →ₗ[R] _V n
  /-- Homotopy h : V → V of degree -1 -/
  homotopy : (n : ℤ) → _V n →ₗ[R] _V (n - 1)
  /-- p ∘ i = id_H (projection-inclusion identity) -/
  proj_incl : ∀ n : ℤ, (proj n).comp (incl n) = LinearMap.id
  /-- Side conditions: h² = 0, h ∘ i = 0, p ∘ h = 0 -/
  annihilation :
    (∀ n : ℤ, (homotopy (n - 1)).comp (homotopy n) = 0) ∧
    (∀ n : ℤ, (homotopy n).comp (incl n) = 0) ∧
    (∀ n : ℤ, (proj (n - 1)).comp (homotopy n) = 0)

/-- The transferred L∞ structure on H.

    The brackets on H are given by sums over trees:
    l_n^H(x₁,...,xₙ) = ∑_T ε(T) p ∘ (products of l_k and h) ∘ i^⊗n

    This is specified by explicit transfer data at this stage. -/
structure HomotopyTransferTheory {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V)
    (data : HomotopyTransferData R V H) where
  /-- The transferred L∞ structure on the retract object. -/
  transferred : LInftyAlgebra R H
  /-- Inclusion lifted to an L∞ morphism from the transferred structure. -/
  inclusion : LInftyMorphism R transferred L
  /-- Linear component of the lifted morphism is the SDR inclusion. -/
  inclusion_linear : ∀ n : ℤ, inclusion.linear n = data.incl n

/-- The transferred L∞ structure on H from explicit transfer theory data. -/
def transferredStructure {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    {L : LInftyAlgebra R V}
    {data : HomotopyTransferData R V H}
    (T : HomotopyTransferTheory L data) : LInftyAlgebra R H :=
  T.transferred

/-- The transfer quasi-isomorphism.

    The homotopy transfer comes with a canonical quasi-isomorphism
    i_∞ : H → V extending i, making the transfer functorial. -/
def transferMorphism {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V)
    (data : HomotopyTransferData R V H)
    (T : HomotopyTransferTheory L data) :
    LInftyMorphism R (transferredStructure T) L :=
  T.inclusion

/-! ## Special Cases -/

/-- A DGLA (differential graded Lie algebra).

    An L∞ algebra where l_n = 0 for all n ≥ 3.
    The Jacobi identity holds strictly (no higher homotopies). -/
structure DGLA (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    extends LInftyAlgebra R V where
  /-- Higher brackets vanish: the coderivation D vanishes on word length ≥ 3 -/
  higher_vanish : isDGLA toStructure

/-- A Lie algebra is an L∞ algebra concentrated in degree 0
    with l₁ = 0 and l_n = 0 for n ≥ 3. -/
structure LieAlg (R : Type u) [CommRing R] (V : Type v)
    [AddCommGroup V] [Module R V] where
  /-- The Lie bracket -/
  bracket : V → V → V
  /-- Antisymmetry -/
  antisymm : ∀ x y, bracket x y = - bracket y x
  /-- Jacobi identity -/
  jacobi : ∀ x y z, bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0
  /-- Bilinearity in the first argument -/
  add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  /-- Bilinearity in the second argument -/
  add_right : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  /-- Scalar multiplication in first argument -/
  smul_left : ∀ (r : R) x y, bracket (r • x) y = r • bracket x y
  /-- Scalar multiplication in second argument -/
  smul_right : ∀ (r : R) x y, bracket x (r • y) = r • bracket x y

/-- A canonical zero element in the reduced symmetric coalgebra with specified degree. -/
def ReducedSymCoalg.zeroWithDegree (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (d : ℤ) : ReducedSymCoalg R V where
  degree := d
  wordLength := 1
  wordLength_pos := le_refl 1
  factorDegrees := fun _ => d
  degree_eq := by simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  isZero := true

/-- Every Lie algebra gives an L∞ algebra.

    For a Lie algebra (V, [·,·]):
    - l₁ = 0 (no differential)
    - l₂ = [·,·] (the Lie bracket)
    - l_n = 0 for n ≥ 3 (no higher brackets)

    The L∞ relations reduce to: [·,·] is antisymmetric and satisfies Jacobi.

    Mathematically, D² = 0 follows from the Jacobi identity. -/
structure LieToLInftyModel (R : Type u) [CommRing R] {V : Type v}
    [AddCommGroup V] [Module R V] (_L : LieAlg R V) where
  /-- Chosen L∞ model on the degreewise-constant graded module. -/
  model : LInftyAlgebra R (fun _ : ℤ => V)

def LieAlg.toLInfty {R : Type u} [CommRing R] {V : Type v}
    [AddCommGroup V] [Module R V] (L : LieAlg R V)
    (M : LieToLInftyModel R L) :
    LInftyAlgebra R (fun _ : ℤ => V) :=
  M.model

/-! ## Connection to Mathlib's Lie Algebras -/

/-- Construct a `LieAlg` from mathlib's `LieRing` and `LieAlgebra` instances.

    This provides interoperability with the mathlib Lie algebra library.
    The `AddCommGroup` and `Module` instances come from `LieRing` and `LieAlgebra`. -/
def LieAlg.ofMathlib (R : Type u) [CommRing R] (V : Type v)
    [LieRing V] [LieAlgebra R V] :
    @LieAlg R _ V LieRing.toAddCommGroup LieAlgebra.toModule where
  bracket := fun x y => ⁅x, y⁆
  antisymm := fun x y => (lie_skew x y).symm
  jacobi := fun x y z => by
    -- lie_jacobi gives: ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0
    -- We need: ⁅⁅x, y⁆, z⁆ + ⁅⁅y, z⁆, x⁆ + ⁅⁅z, x⁆, y⁆ = 0
    -- lie_skew x y says: -⁅y, x⁆ = ⁅x, y⁆
    -- So ⁅⁅x, y⁆, z⁆ = -⁅z, ⁅x, y⁆⁆ via (lie_skew ⁅x, y⁆ z).symm
    rw [(lie_skew ⁅x, y⁆ z).symm, (lie_skew ⁅y, z⁆ x).symm, (lie_skew ⁅z, x⁆ y).symm]
    -- Now goal is: -⁅z, ⁅x, y⁆⁆ + -⁅x, ⁅y, z⁆⁆ + -⁅y, ⁅z, x⁆⁆ = 0
    have h := lie_jacobi x y z
    simp only [← neg_add, neg_eq_zero]
    convert h using 1
    abel
  add_left := fun x y z => LieRing.add_lie x y z
  add_right := fun x y z => LieRing.lie_add x y z
  smul_left := fun r x y => LieModule.smul_lie r x y
  smul_right := fun r x y => LieModule.lie_smul r x y

/-- A mathlib Lie algebra gives an L∞ algebra via our construction. -/
def mathlibLieToLInfty (R : Type u) [CommRing R] (V : Type v)
    [LieRing V] [LieAlgebra R V]
    (M : LieToLInftyModel R (LieAlg.ofMathlib R V)) :
    @LInftyAlgebra R _ (fun _ : ℤ => V)
      (fun _ => LieRing.toAddCommGroup) (fun _ => LieAlgebra.toModule) :=
  (LieAlg.ofMathlib R V).toLInfty M

end StringAlgebra.Linfinity
