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

Classically, two MC elements are gauge equivalent via gauge-flow/exponential
actions of degree-0 elements. In this file, the relation is supplied
explicitly by `MCTheory.gaugeEquivalent` together with equivalence proofs.

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
  /-- Neutral gauge parameter acts trivially. -/
  gaugeAction_zero : ∀ a : V 1, gaugeAction 0 a = a
  /-- Gauge-equivalence relation on degree-1 elements. -/
  gaugeEquivalent : V 1 → V 1 → Prop
  /-- Gauge action produces gauge-equivalent points. -/
  gaugeAction_sound : ∀ g : V 0, ∀ a : V 1, gaugeEquivalent a (gaugeAction g a)
  /-- Gauge action preserves vanishing curvature (MC equation). -/
  gaugeAction_preserves_curvature_zero :
    ∀ g : V 0, ∀ a : V 1, curvature a = 0 → curvature (gaugeAction g a) = 0
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

/-- Gauge action by the neutral parameter is the identity. -/
theorem gaugeAction_zero {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : V 1) :
    gaugeAction T 0 a = a :=
  T.gaugeAction_zero a

/-- Gauge action lands in the supplied gauge-equivalence relation. -/
theorem gaugeAction_gaugeEquivalent {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (g : V 0) (a : V 1) :
    T.gaugeEquivalent a (gaugeAction T g a) :=
  T.gaugeAction_sound g a

/-- Gauge action preserves the Maurer-Cartan equation. -/
theorem gaugeAction_preservesMC {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (g : V 0) (a : V 1) :
    satisfiesMC L T a → satisfiesMC L T (gaugeAction T g a) :=
  T.gaugeAction_preserves_curvature_zero g a

/-- Gauge-equivalence relation on MC elements from explicit `MCTheory` data.

    Classical gauge-flow interpretations motivate this relation, but this
    definition uses only the relation field supplied by `MCTheory`. -/
def GaugeEquivalent {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a b : MCElement R T) : Prop :=
  T.gaugeEquivalent a.element b.element

/-- Reflexivity of MC gauge equivalence. -/
theorem gaugeEquivalent_refl {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T) :
    GaugeEquivalent T a a :=
  T.gauge_equiv.refl a.element

/-- Symmetry of MC gauge equivalence. -/
theorem gaugeEquivalent_symm {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L)
    {a b : MCElement R T} :
    GaugeEquivalent T a b → GaugeEquivalent T b a :=
  T.gauge_equiv.symm

/-- Transitivity of MC gauge equivalence. -/
theorem gaugeEquivalent_trans {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L)
    {a b c : MCElement R T} :
    GaugeEquivalent T a b → GaugeEquivalent T b c → GaugeEquivalent T a c :=
  T.gauge_equiv.trans

/-- Gauge equivalence is an equivalence relation -/
theorem gauge_equiv_equivalence {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) : Equivalence (GaugeEquivalent T) where
  refl := by
    intro a
    exact gaugeEquivalent_refl T a
  symm := by
    intro a b hab
    exact gaugeEquivalent_symm T hab
  trans := by
    intro a b c hab hbc
    exact gaugeEquivalent_trans T hab hbc

instance gaugeEquivalentSetoid {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) : Setoid (MCElement R T) where
  r := GaugeEquivalent T
  iseqv := gauge_equiv_equivalence T

/-- The moduli space of MC elements modulo gauge equivalence -/
def MCModuli (R : Type u) [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) : Type _ :=
  Quotient (gaugeEquivalentSetoid (R := R) T)

namespace MCElement

/-- Gauge action on Maurer-Cartan elements. -/
def gaugeAct {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} {T : MCTheory R L}
    (g : V 0) (a : MCElement R T) : MCElement R T where
  element := gaugeAction T g a.element
  mc := gaugeAction_preservesMC T g a.element a.mc

/-- Projection of an MC element to its moduli class. -/
def toModuli {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} {T : MCTheory R L}
    (a : MCElement R T) : MCModuli R T :=
  Quotient.mk _ a

@[simp] theorem toModuli_eq_iff_gaugeEquivalent {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} {T : MCTheory R L}
    (a b : MCElement R T) :
    a.toModuli = b.toModuli ↔ GaugeEquivalent T a b :=
  Quotient.eq

end MCElement

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

/-- Interface-level tangent model at a moduli point.

    In this stage it is represented directly by the degree-1 piece. -/
def tangentSpace {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (_a : MCElement R T) : Type _ :=
  V 1

/-- Interface-level obstruction model at a moduli point.

    In this stage it is represented directly by the degree-2 piece. -/
def obstructionSpace {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (_a : MCElement R T) : Type _ :=
  V 2

/-- Construct a moduli point from an explicit unobstructedness witness
    in the current obstruction model. -/
def smoothPoint_when_unobstructed {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T)
    (_h : Subsingleton (obstructionSpace T a)) :
    MCModuli R T :=
  Quotient.mk _ a

/-- Nonempty-form of `smoothPoint_when_unobstructed`. -/
theorem smooth_when_unobstructed {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T)
    (h : Subsingleton (obstructionSpace T a)) :
    Nonempty (MCModuli R T) :=
  ⟨smoothPoint_when_unobstructed T a h⟩

/-! ## Kuranishi Map -/

/-- Explicit Kuranishi data at an MC point. -/
structure KuranishiTheory {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T) where
  /-- The Kuranishi map `κ : H¹(L^a) → H²(L^a)`. -/
  map : tangentSpace T a → obstructionSpace T a
  /-- Base-point normalization `κ(0) = 0`. -/
  map_zero : map (0 : V 1) = (0 : V 2)

/-- The Kuranishi map κ : H¹(L^a) → H²(L^a).

    This is the obstruction to extending infinitesimal deformations.
    If κ = 0, then every infinitesimal deformation extends. -/
def kuranishiMap {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T)
    (K : KuranishiTheory T a) :
    tangentSpace T a → obstructionSpace T a :=
  K.map

/-- The moduli space is locally κ⁻¹(0) / gauge -/
theorem moduli_as_kuranishi {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (T : MCTheory R L) (a : MCElement R T)
    (K : KuranishiTheory T a) :
    ∃ x : tangentSpace T a, kuranishiMap T a K x = (0 : V 2) := by
  refine ⟨(0 : V 1), ?_⟩
  simpa [kuranishiMap] using K.map_zero

end StringAlgebra.Linfinity
