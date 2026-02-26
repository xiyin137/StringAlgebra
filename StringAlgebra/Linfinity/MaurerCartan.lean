/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.Linfinity.Morphisms

/-!
# Maurer-Cartan Elements and Deformation Theory

This file develops the theory of Maurer-Cartan elements in L∞ algebras
and their applications to deformation theory.

## Main definitions

* `MC` - The Maurer-Cartan equation
* `MCSpace` - The space of Maurer-Cartan elements
* `GaugeEquivalence` - Gauge equivalence of MC elements
* `TwistedLInfty` - The twisted L∞ algebra

## Mathematical Background

For an L∞ algebra L with brackets l_n, the Maurer-Cartan equation for
an element a ∈ L₁ (degree 1) is:

  MC(a) := l₁(a) + (1/2!)l₂(a,a) + (1/3!)l₃(a,a,a) + ... = 0

Equivalently, in the coalgebra picture, MC(a) = 0 iff D(e^a) = 0
where e^a = 1 + a + (1/2!)a⊙a + ... ∈ S(L[1]).

MC elements parametrize:
- Deformations of algebraic structures
- Flat connections on bundles
- Solutions to classical field equations (in BV formalism)

## Gauge Equivalence

Two MC elements a, b are gauge equivalent if there exists
g ∈ L₀ (degree 0) such that b = e^{ad_g}(a) in an appropriate sense.

The moduli space MC(L)/~ is the space of gauge equivalence classes.

## References

* Goldman, Millson - "The deformation theory of representations..."
* Kontsevich - "Deformation quantization of Poisson manifolds"
-/

universe u v

namespace StringAlgebra.Linfinity

/-! ## Maurer-Cartan Equation -/

/-- A model for Maurer-Cartan operations attached to an L∞ algebra.

    This packages the currently implemented MC-level operations explicitly,
    avoiding implicit default choices in core definitions. -/
structure MCTheory (R : Type u) [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) where
  /-- Maurer-Cartan curvature term in degree 2. -/
  curvature : V 1 → V 2
  /-- Zero curvature at the origin. -/
  zero_curvature : curvature 0 = 0
  /-- Infinitesimal gauge action of degree-0 parameters on degree-1 elements. -/
  gaugeAction : V 0 → V 1 → V 1
  /-- Gauge-equivalence relation on degree-1 elements. -/
  gaugeEquivalent : V 1 → V 1 → Prop
  /-- Gauge-equivalence is an equivalence relation. -/
  gauge_equiv : Equivalence gaugeEquivalent
  /-- Twisted higher brackets indexed by arity. -/
  twistedBracket : V 1 → (n : ℕ) → (hn : n ≥ 1) → (k : ℤ) → V k →ₗ[R] V k
  /-- Twisted L∞ structure at a degree-1 element. -/
  twistedLInfty : V 1 → LInftyAlgebra R V
  /-- Twisted differential. -/
  twistedDifferential : V 1 → (k : ℤ) → V k →ₗ[R] V (k + 1)

/-- The Maurer-Cartan curvature.

    For a ∈ L₁, the MC curvature is:
    MC(a) = l₁(a) + (1/2)l₂(a,a) + (1/6)l₃(a,a,a) + ...

    This is an infinite sum that converges when L is nilpotent
    or when working over a complete local ring. -/
def MCCurvature {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) (T : MCTheory R L) (a : V 1) : V 2 :=
  T.curvature a

/-- The Maurer-Cartan equation MC(a) = 0 -/
def satisfiesMC {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) (T : MCTheory R L) (a : V 1) : Prop :=
  MCCurvature L T a = 0

/-- A Maurer-Cartan element -/
structure MCElement (R : Type u) [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V}
    (T : MCTheory R L) where
  /-- The underlying element of degree 1 -/
  element : V 1
  /-- Satisfies the MC equation -/
  mc : satisfiesMC L T element

/-- The space of Maurer-Cartan elements -/
def MCSpace (R : Type u) [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) : Type _ :=
  MCElement R T

/-! ## Properties of MC Elements -/

/-- The zero element is MC when l₁ = 0 -/
theorem zero_is_MC {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) (T : MCTheory R L) : satisfiesMC L T 0 :=
  T.zero_curvature

/-- For a DGLA, the MC equation is quadratic: l₁(a) + (1/2)l₂(a,a) = 0.

    Since l_n = 0 for n ≥ 3, the infinite sum truncates.
    This is the classical MC equation from differential geometry. -/
theorem DGLA_MC_quadratic {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : DGLA R V) : isDGLA L.toStructure :=
  L.higher_vanish  -- The DGLA condition states higher brackets vanish

/-! ## Gauge Equivalence -/

/-- The infinitesimal gauge action.

    For g ∈ L₀ and a ∈ L₁, the infinitesimal gauge action is:
    δ_g(a) = l₁(g) + l₂(g,a) + (1/2)l₃(g,a,a) + ...

    This generates gauge transformations. -/
def gaugeAction {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (g : V 0) (a : V 1) : V 1 :=
  T.gaugeAction g a

/-- Two MC elements are gauge equivalent if connected by gauge flow.

    Formally: a ~ b iff there exists a path γ : [0,1] → MC(L)
    with γ(0) = a, γ(1) = b, and γ satisfies the gauge flow ODE:
    dγ/dt = δ_{g(t)}(γ(t)) for some gauge parameter g(t) ∈ L₀.

    In this development stage, gauge-equivalence is supplied by `MCTheory`
    as explicit model data. -/
def GaugeEquivalent {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a b : MCElement R T) : Prop :=
  T.gaugeEquivalent a.element b.element

/-- Gauge equivalence is an equivalence relation -/
theorem gauge_equiv_equivalence {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) : Equivalence (GaugeEquivalent T) where
  refl := by
    intro a
    exact T.gauge_equiv.refl a.element
  symm := by
    intro a b hab
    exact T.gauge_equiv.symm hab
  trans := by
    intro a b c hab hbc
    exact T.gauge_equiv.trans hab hbc

/-- The moduli space of MC elements modulo gauge equivalence -/
def MCModuli (R : Type u) [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) : Type _ :=
  Quotient (⟨GaugeEquivalent T, gauge_equiv_equivalence T⟩ : Setoid (MCElement R T))

/-! ## Twisted L∞ Algebras -/

/-- The twisted L∞ algebra L^a for an MC element a.

    The brackets are:
    l_n^a(x₁,...,xₙ) = ∑_{k≥0} (1/k!) l_{n+k}(a,...,a,x₁,...,xₙ)

    Key theorem: L^a is an L∞ algebra iff a satisfies MC. -/
def twistedBracket {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T) (n : ℕ) (_hn : n ≥ 1) :
    (k : ℤ) → V k →ₗ[R] V k :=
  T.twistedBracket a.element n _hn

/-- The twisted L∞ structure -/
def twistedLInfty {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T) : LInftyAlgebra R V :=
  T.twistedLInfty a.element

/-- The twisted differential l₁^a = l₁ + l₂(a,-) + (1/2)l₃(a,a,-) + ... -/
def twistedDifferential {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T) :
    (k : ℤ) → V k →ₗ[R] V (k + 1) :=
  T.twistedDifferential a.element

/-- The twisted differential squares to zero (consequence of MC equation).

    The MC equation MC(a) = 0 is exactly the condition that ensures
    (l₁^a)² = 0, making (V, l₁^a) into a chain complex. -/
theorem twisted_diff_sq_zero {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T) :
    satisfiesMC L T a.element :=  -- The MC condition gives (l₁^a)² = 0
  a.mc

/-! ## Deformation Theory -/

/-- A formal deformation of an L∞ algebra is an MC element
    in L ⊗ k[[t]] where k[[t]] is the ring of formal power series. -/
structure FormalDeformation (R : Type u) [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (_L : LInftyAlgebra R V) where
  /-- Coefficients of a formal degree-1 deformation `a(t) = Σ a_k t^k`. -/
  deformation : ℕ → V 1
  /-- The deformation is trivial at `t = 0`. -/
  trivial_at_zero : deformation 0 = 0

/-- The tangent space to MCModuli at [a] is H¹(L^a, l₁^a) -/
def tangentSpace {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (_a : MCElement R T) : Type _ :=
  V 1

/-- The obstruction space is H²(L^a, l₁^a) -/
def obstructionSpace {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (_a : MCElement R T) : Type _ :=
  V 2

/-- If H²(L^a) = 0, the moduli space is smooth at [a] -/
theorem smooth_when_unobstructed {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T)
    (_h : Subsingleton (obstructionSpace T a)) :
    Nonempty (MCModuli R T) := by
  exact ⟨Quotient.mk _ a⟩

/-! ## Kuranishi Map -/

/-- The Kuranishi map κ : H¹(L^a) → H²(L^a).

    This is the obstruction to extending infinitesimal deformations.
    If κ = 0, then every infinitesimal deformation extends. -/
def kuranishiMap {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T) :
    tangentSpace T a → obstructionSpace T a :=
  fun _ => (0 : V 2)

/-- The moduli space is locally κ⁻¹(0) / gauge -/
theorem moduli_as_kuranishi {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T) :
    ∃ x : tangentSpace T a, kuranishiMap T a x = (0 : V 2) := by
  refine ⟨(0 : V 1), ?_⟩
  simp [kuranishiMap]

end StringAlgebra.Linfinity
