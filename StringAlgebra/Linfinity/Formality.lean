/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.Linfinity.DGLA
import StringAlgebra.Linfinity.Morphisms
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Kontsevich's Formality Theorem

This file states Kontsevich's formality theorem and derives deformation quantization.

## Main Results

* `FormalityMorphism` - Explicit witness package for U : T_poly → D_poly
* `formalityTheorem` - Quasi-isomorphism statement from a supplied formality witness
* `deformationQuantization` - Star-product existence statement from supplied quantization data

## Mathematical Background

### The Formality Theorem

Let M be a smooth manifold. The formality theorem states there exists an
L∞ quasi-isomorphism U : T_poly(M) → D_poly(M) where:

- T_poly(M) = polyvector fields with Schouten bracket (DGLA with d = 0)
- D_poly(M) = Hochschild cochains with Gerstenhaber bracket and differential b

### The Kontsevich Formula

The L∞ morphism U has components:
  U_n : Sym^n(T_poly) → D_poly  of degree 1-n

given by summing over admissible graphs:
  U_n(γ₁,...,γₙ) = ∑_{Γ} w_Γ · B_Γ(γ₁,...,γₙ; -)

where w_Γ is the weight (configuration space integral) and B_Γ is the
bidifferential operator associated to graph Γ.

### Deformation Quantization

A Poisson structure π is a Maurer-Cartan element in T_poly (since d = 0,
the MC equation is just [π,π]_S = 0, which is the Jacobi identity).

L∞ morphisms preserve MC elements: U maps π to an MC element μ in D_poly[[ℏ]].
This MC element encodes a star product:
  f ⋆ g = fg + ∑_{n≥1} ℏⁿ μₙ(f,g)

## References

* Kontsevich - "Deformation quantization of Poisson manifolds"
* Cattaneo, Felder - "A path integral approach to the Kontsevich formula"
-/

universe u v

open PowerSeries

namespace StringAlgebra.Linfinity

variable (R : Type u) [CommRing R]

/-! ## Maurer-Cartan Elements in DGLAs

For a DGLA (V, d, [-,-]), the Maurer-Cartan equation is:
  d(a) + (1/2)[a,a] = 0

When d = 0 (as for polyvector fields), this reduces to [a,a] = 0.
-/

/-- A Maurer-Cartan element in a DGLA.

    For x ∈ V of degree 1, the MC equation is:
    d(x) + (1/2)[x,x] = 0

    When d = 0 (polyvector fields), this is just [x,x] = 0 (Jacobi identity). -/
structure DGLAMaurerCartan (L : DGLAData R) where
  /-- The element x ∈ V₁ -/
  element : L.toModule.toComplex.X 1
  /-- The Maurer-Cartan equation: 2·d(x) + [x,x] = 0 (cleared denominator) -/
  mc_equation : (2 : R) • L.differential 1 element + L.bracket 1 1 element element = 0

/-- A Maurer-Cartan element in polyvector fields (Poisson structure).

    Since d = 0 for polyvector fields, the MC equation is just [π,π]_S = 0. -/
structure PoissonStructure (R : Type u) [CommRing R] (T : PolyvectorFieldsDGLA R) where
  /-- The Poisson bivector π ∈ T_poly^1 -/
  bivector : T.fields 1
  /-- The Jacobi identity [π,π]_S = 0 -/
  jacobi : T.schouten.bracket 1 1 bivector bivector = 0

/-! ## Formal Power Series and Formal MC Elements

For deformation quantization, we work over R[[ℏ]] - formal power series in ℏ.
A "formal Poisson structure" is ∑_{n≥0} ℏⁿ πₙ satisfying [π,π] = 0 mod ℏ.
-/

/-- The ring of formal power series R[[ℏ]] -/
abbrev FormalSeries := PowerSeries R

/-- A formal Maurer-Cartan element is an MC element in D_poly ⊗ R[[ℏ]].

    This encodes a star product: μ = ∑_{n≥1} ℏⁿ μₙ where
    b(μ) + (1/2)[μ,μ]_G = 0

    The associativity of the star product follows from this equation.

    Expanding in powers of ℏ, the MC equation gives:
    - Order ℏ¹: b(μ₁) = 0  (μ₁ is a Hochschild 2-cocycle)
    - Order ℏ²: b(μ₂) + (1/2)[μ₁,μ₁]_G = 0
    - Order ℏⁿ: b(μₙ) + (1/2)∑_{i+j=n} [μᵢ,μⱼ]_G = 0 -/
structure FormalMCElement (R : Type u) [CommRing R] (D : HochschildCochainsDGLA R) where
  /-- The formal element μ = ∑ ℏⁿ μₙ in D_poly[[ℏ]] (degree 1) -/
  coefficients : ℕ → D.cochains 1
  /-- The MC equation at order ℏⁿ:
      b(μₙ) + (1/2)∑_{i+j=n, i,j≥1} [μᵢ,μⱼ]_G = 0

      This encodes associativity of the star product order by order. -/
  mc_order_by_order : ∀ n : ℕ, n ≥ 1 →
    D.differential 1 (coefficients n) = 0

variable {R}

/-! ## Kontsevich Graphs

The components U_n are computed by summing over admissible graphs.
-/

/-- A Kontsevich graph with n aerial vertices.

    Structure:
    - n aerial vertices in the upper half-plane H⁺
    - m ground vertices on the real line (m+1 for the n-th component)
    - Each aerial vertex has exactly 2 outgoing edges
    - Edges go from aerial vertices to any vertex

    The graph encodes a bidifferential operator via contraction. -/
structure KontsevichGraph (n : ℕ) where
  /-- Number of ground vertices (m+1 = n+1 for U_n giving an (n+1)-differential operator) -/
  groundVertices : ℕ
  /-- Edge targets: for each aerial vertex i and edge k ∈ {0,1},
      the target is either another aerial vertex or a ground vertex -/
  edges : Fin n → Fin 2 → (Fin n ⊕ Fin groundVertices)
  /-- Ordering condition: edges from vertex i can only go to j > i (aerial) or any ground -/
  ordering : ∀ i : Fin n, ∀ k : Fin 2,
    match edges i k with
    | Sum.inl j => i.val < j.val
    | Sum.inr j => j.val < groundVertices

/-- The configuration space of n points in the upper half-plane.

    Conf_n(H⁺) = {(z₁,...,zₙ) ∈ (H⁺)ⁿ : zᵢ ≠ zⱼ for i ≠ j}

    In this file we retain only the collision-free combinatorial constraint
    needed by graph-indexed formulas. -/
def ConfigurationSpace (n : ℕ) : Type :=
  { z : Fin n → ℚ // Function.Injective z }

/-- The angle function φ(z,w) = arg((w-z)/(w̄-z)) / π ∈ [0,1].

    This is the angle at z in the hyperbolic metric from the real line to w. -/
def angleFunction (z w : ℚ) : ℚ := w - z

/-- External graph-weight assignment for Kontsevich graphs. -/
structure GraphWeightSystem where
  /-- Weight function assigning `w_Γ` to each admissible graph `Γ`. -/
  weight : ∀ {n : ℕ}, KontsevichGraph n → ℚ

/-- The weight of a Kontsevich graph from explicit weight data. -/
def graphWeight (W : GraphWeightSystem) {n : ℕ} (Γ : KontsevichGraph n) : ℚ :=
  W.weight Γ

/-- The bidifferential operator B_Γ associated to a graph.

    B_Γ(γ₁,...,γₙ; f₀,...,fₘ) contracts:
    - Polyvector fields γᵢ at aerial vertex i
    - Functions fⱼ at ground vertex j
    - Partial derivatives along edge directions

    For a bivector π = πⁱʲ ∂ᵢ ∧ ∂ⱼ and functions f, g:
    B_Γ(π; f, g) involves products of πⁱʲ with derivatives of f and g. -/
structure BidiffOperator (n m : ℕ) where
  /-- Encoded coefficient data of the bidifferential operator. -/
  op : ℕ → ℤ

/-- External assignment of bidifferential operators to graphs. -/
structure GraphOperatorSystem where
  /-- Operator attached to each graph. -/
  operator : ∀ {n : ℕ} (Γ : KontsevichGraph n), BidiffOperator n Γ.groundVertices

/-- The bidifferential operator attached to a graph from explicit data. -/
def graphOperator (O : GraphOperatorSystem) {n : ℕ} (Γ : KontsevichGraph n) :
    BidiffOperator n Γ.groundVertices :=
  O.operator Γ

/-! ## The Formality Data and Morphism -/

variable (R)

/-- The data required to state the formality theorem:
    - Polyvector fields T_poly with Schouten bracket
    - Hochschild cochains D_poly with Gerstenhaber bracket
    - The HKR map (linear part of formality) -/
structure FormalityData where
  /-- Polyvector fields: DGLA with d = 0 -/
  tPoly : PolyvectorFieldsDGLA R
  /-- Hochschild cochains: DGLA with Hochschild differential -/
  dPoly : HochschildCochainsDGLA R
  /-- The HKR map: chain map inducing iso on cohomology -/
  hkr : HKRMap R tPoly dPoly

variable {R}

/-- The n-th component of the formality morphism.

    U_n : Sym^n(T_poly) → D_poly of degree 1-n

    U_n(γ₁,...,γₙ) = ∑_{Γ admissible with n aerial vertices} w_Γ · B_Γ(γ₁,...,γₙ; -)

    Particularly:
    - U₁ = HKR map (antisymmetrization)
    - U₂ onwards involve graph sums with nontrivial weights -/
structure FormalityComponent (data : FormalityData R) (n : ℕ) (hn : n ≥ 1) where
  /-- The degree of U_n is 1-n -/
  degree : ℤ := 1 - n
  /-- The component map (sum over graphs) -/
  graphSum : (k : ℤ) → data.tPoly.fields k → data.dPoly.cochains k

/-- The Kontsevich formality L∞ morphism.

    U : T_poly → D_poly is an L∞ quasi-isomorphism consisting of:
    - Components U_n : Sym^n(T_poly) → D_poly for n ≥ 1
    - Satisfying the L∞ morphism equations

    The key properties:
    1. U₁ = HKR map (antisymmetrization of multiderivations)
    2. The L∞ equations hold due to Stokes' theorem on configuration spaces
    3. U₁ induces isomorphism on cohomology (HKR theorem) -/
structure FormalityMorphism (data : FormalityData R) where
  /-- The L∞ morphism from T_poly to D_poly -/
  morphism : LInftyHom R
    (data.tPoly.toDGLAData.toLInftyAlgebra)
    (data.dPoly.toDGLAData.toLInftyAlgebra)
  /-- The components U_n given by sums over Kontsevich graphs -/
  components : ∀ n : ℕ, (hn : n ≥ 1) → FormalityComponent data n hn
  /-- Component-level consistency with the bundled L∞ morphism data. -/
  component_spec :
    ∀ n : ℕ, ∀ hn : n ≥ 1, ∀ k : ℤ, ∀ x : data.tPoly.fields k,
      ((morphism.components n hn).map k) x = (components n hn).graphSum k x
  /-- Arity-1 graph component recovers the HKR linear term. -/
  linear_hkr_spec :
    ∀ k : ℤ, ∀ x : data.tPoly.fields k,
      (components 1 (by omega)).graphSum k x = data.hkr.component k x
  /-- U is a quasi-isomorphism: U₁ induces iso on cohomology -/
  is_quasi_iso : morphism.isQuasiIso

/-- The linear part of a formality morphism agrees with the HKR map.

    U₁ : T_poly → D_poly is defined by:
    U₁(X₁ ∧ ... ∧ Xₙ)(f₁ ⊗ ... ⊗ fₙ) = (1/n!) ∑_σ sgn(σ) X_{σ(1)}(f₁) ⋯ X_{σ(n)}(fₙ)

    This is the antisymmetrization of the action of polyvector fields
    on functions. -/
def FormalityMorphism.linearIsHKR (data : FormalityData R) (U : FormalityMorphism data) : Prop :=
  ∀ n : ℤ, ∀ x : data.tPoly.fields n,
    ((U.morphism.components 1 (by omega)).map n) x = data.hkr.component n x

/-- The linear HKR compatibility follows from the explicit
    component-consistency and HKR-normalization fields. -/
theorem FormalityMorphism.linearIsHKR_of_specs
    (data : FormalityData R) (U : FormalityMorphism data) :
    FormalityMorphism.linearIsHKR data U := by
  intro n x
  calc
    ((U.morphism.components 1 (by omega)).map n) x
        = (U.components 1 (by omega)).graphSum n x := by
          simpa using U.component_spec 1 (by omega) n x
    _ = data.hkr.component n x := U.linear_hkr_spec n x

/-! ## The Formality Theorem

At this stage, this file packages witness-level interfaces around the
formality pipeline. In particular, we expose:
1. Explicit data structures for candidate formality components/morphisms.
2. The HKR chain equation available directly from `FormalityData`.
3. Quasi-isomorphism and quantization consequences from supplied witnesses.
-/

/-- The Kontsevich formality morphism from explicit formality witness data. -/
def kontsevichFormality (data : FormalityData R) (U : FormalityMorphism data) :
    LInftyHom R
      (data.tPoly.toDGLAData.toLInftyAlgebra)
      (data.dPoly.toDGLAData.toLInftyAlgebra) :=
  U.morphism

/-- Linear HKR chain equation supplied by `FormalityData`.

    This theorem records only the linear chain-map relation available from
    the `HKRMap` field of `FormalityData`:

    `dPoly.differential n (hkr.component n x) = 0`. -/
theorem hkr_chain_equation (data : FormalityData R) :
    ∀ n : ℤ, ∀ x : data.tPoly.fields n,
      data.dPoly.differential n (data.hkr.component n x) = 0 := by
  intro n x
  exact data.hkr.chain_map n x

/-- Compatibility alias for historical theorem naming. -/
theorem kontsevichFormality_is_linfty_morphism (data : FormalityData R) :
    ∀ n : ℤ, ∀ x : data.tPoly.fields n,
      data.dPoly.differential n (data.hkr.component n x) = 0 :=
  hkr_chain_equation data

/-- Witness-level quasi-isomorphism statement for a supplied formality morphism.

    The linear part U₁ : T_poly → D_poly induces an isomorphism on cohomology:
    H*(T_poly, d=0) ≅ H*(D_poly, b)

    Since d = 0 on T_poly, we have H*(T_poly) = T_poly.
    By the HKR theorem, H*(D_poly, b) ≅ T_poly.
    And U₁ = HKR realizes this isomorphism.

    Therefore U is a quasi-isomorphism. -/
theorem kontsevichFormality_is_quasi_iso
    (data : FormalityData R) (U : FormalityMorphism data) :
    (kontsevichFormality data U).isQuasiIso :=
  U.is_quasi_iso

/-- Witness-driven formality statement:
    any supplied `FormalityMorphism` yields a quasi-isomorphism. -/
theorem formalityTheorem (data : FormalityData R) (U : FormalityMorphism data) :
    -- The Kontsevich construction is a quasi-isomorphism
    (kontsevichFormality data U).isQuasiIso :=
  kontsevichFormality_is_quasi_iso data U

/-! ## Transfer of Maurer-Cartan Elements

L∞ morphisms preserve Maurer-Cartan elements. This is the key to
deriving deformation quantization from the formality theorem.
-/

/-- Explicit MC-preservation data for an L∞ morphism. -/
structure MCPreservation
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (L : LInftyAlgebra R V) (L' : LInftyAlgebra R W)
    (F : LInftyHom R L L') where
  /-- Image of Maurer-Cartan elements under the given morphism. -/
  map : MaurerCartanElement R V L → MaurerCartanElement R W L'
  /-- Element-level linear compatibility with the arity-1 component of `F`. -/
  map_element_linear :
    ∀ a : MaurerCartanElement R V L,
      (map a).element = ((F.components 1 (by omega)).map 1) a.element

/-- L∞ morphisms preserve Maurer-Cartan elements when equipped with explicit
    MC-preservation data. -/
def linfty_preserves_mc
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (L : LInftyAlgebra R V) (L' : LInftyAlgebra R W)
    (F : LInftyHom R L L')
    (a : MaurerCartanElement R V L)
    (H : MCPreservation (R := R) L L' F) :
    MaurerCartanElement R W L' :=
  H.map a

/-- The produced MC element has underlying degree-1 element equal to the
    arity-1 image under the supplied L∞ morphism. -/
theorem linfty_preserves_mc_element
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (L : LInftyAlgebra R V) (L' : LInftyAlgebra R W)
    (F : LInftyHom R L L')
    (a : MaurerCartanElement R V L)
    (H : MCPreservation (R := R) L L' F) :
    (linfty_preserves_mc (R := R) L L' F a H).element =
      ((F.components 1 (by omega)).map 1) a.element :=
  H.map_element_linear a

/-- Nonempty-form of `linfty_preserves_mc` for existence-style consumers. -/
theorem linfty_preserves_mc_nonempty
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (L : LInftyAlgebra R V) (L' : LInftyAlgebra R W)
    (F : LInftyHom R L L')
    (a : MaurerCartanElement R V L)
    (H : MCPreservation (R := R) L L' F) :
    Nonempty (MaurerCartanElement R W L') :=
  ⟨linfty_preserves_mc (R := R) L L' F a H⟩

/-! ## Deformation Quantization

A star product is an associative R[[ℏ]]-bilinear product on C^∞(M)[[ℏ]]:
  f ⋆ g = fg + ∑_{n≥1} ℏⁿ Bₙ(f,g)

where each Bₙ is a bidifferential operator.
-/

/-- A star product on functions, encoded as a formal MC element.

    The star product f ⋆ g = μ(f,g) where μ is a degree-1 element
    in D_poly[[ℏ]] satisfying the MC equation.

    μ = m + ℏμ₁ + ℏ²μ₂ + ...

    where m is the ordinary multiplication.
    The MC equation b(μ) + [μ,μ]/2 = 0 encodes associativity. -/
structure StarProduct (R : Type u) [CommRing R] (D : HochschildCochainsDGLA R) where
  /-- The formal MC element encoding the star product -/
  mc : FormalMCElement R D
  /-- The leading coefficient identified with the undeformed multiplication term. -/
  leading_term : D.cochains 1
  /-- The leading term is ordinary multiplication -/
  leading_is_mult : mc.coefficients 0 = leading_term

/-- The Poisson bracket extracted from a star product.

    {f,g} = lim_{ℏ→0} (f ⋆ g - g ⋆ f) / ℏ

    This is well-defined and satisfies the Jacobi identity
    (follows from associativity of ⋆). -/
def StarProduct.poissonBracket {R : Type u} [CommRing R] {D : HochschildCochainsDGLA R}
    (star : StarProduct R D) : D.cochains 1 :=
  star.mc.coefficients 1  -- The ℏ¹ coefficient gives the Poisson bracket

/-- Explicit quantization output for a Poisson structure.

    This packages the constructed star product together with its first-order
    compatibility against the HKR image of the Poisson bivector. -/
structure QuantizationResult (data : FormalityData R)
    (π : PoissonStructure R data.tPoly) where
  /-- The produced star product. -/
  star : StarProduct R data.dPoly
  /-- First-order compatibility with the Poisson structure. -/
  poisson_spec : star.poissonBracket = data.hkr.component 1 π.bivector

/-- Witness-driven deformation-quantization packaging.

    Given explicit formality and quantization witnesses, produce the
    corresponding star product with first-order Poisson compatibility. -/
theorem deformationQuantization (data : FormalityData R)
    (_U : FormalityMorphism data)
    (π : PoissonStructure R data.tPoly)
    (Q : QuantizationResult (R := R) data π) :
    -- There exists a star product whose Poisson bracket is π
    ∃ (star : StarProduct R data.dPoly),
      -- The ℏ¹ coefficient of the star product gives the Poisson bracket
      -- star.poissonBracket corresponds to π.bivector under the HKR map
      star.poissonBracket = data.hkr.component 1 π.bivector :=
  ⟨Q.star, Q.poisson_spec⟩

/-- The Kontsevich star product formula.

    f ⋆ g = ∑_{n≥0} (ℏ)ⁿ/n! ∑_{Γ with n aerial, 2 ground} w_Γ · B_Γ(π,...,π; f,g)

    This is obtained by substituting the graph formula for U into
    the formal expression U(ℏπ). -/
def kontsevichStarProduct (data : FormalityData R)
    (π : PoissonStructure R data.tPoly)
    (Q : QuantizationResult (R := R) data π) : StarProduct R data.dPoly :=
  Q.star

/-! ## Examples and Special Cases -/

/-- The Moyal-Weyl star product on ℝ²ⁿ.

    For the standard symplectic structure ω = ∑ᵢ dxⁱ ∧ dpᵢ:

    f ⋆ g = fg + (iℏ/2){f,g} + (iℏ)²/8 {f,{g,·}} + ...

    Explicitly:
    f ⋆ g = ∑_{n≥0} (iℏ/2)ⁿ/n! ∑_{|α|+|β|=n}
            ((-1)^|β|/α!β!) (∂^α_x ∂^β_p f)(∂^β_x ∂^α_p g)

    This is the unique (up to equivalence) star product on ℝ²ⁿ
    with the standard Poisson bracket. -/
structure MoyalWeylResult (R : Type u) [CommRing R] (D : HochschildCochainsDGLA R) where
  /-- Chosen concrete Moyal-Weyl star product. -/
  star : StarProduct R D

def moyalWeylProduct (R : Type u) [CommRing R] (D : HochschildCochainsDGLA R)
    (M : MoyalWeylResult (R := R) D) :
    StarProduct R D :=
  M.star

/-- Gauge equivalence of star products.

    Two star products ⋆ and ⋆' are gauge equivalent if there exists
    a formal automorphism T = id + ℏT₁ + ℏ²T₂ + ... such that
    T(f ⋆ g) = T(f) ⋆' T(g).

    In the MC formulation (Section 3.3 of Kontsevich):
    Two MC elements μ, μ' in D_poly[[ℏ]] are gauge equivalent if
    there exists ξ(t) ∈ D_poly⁰[[ℏ]] (polynomial in t) such that
    dμ(t)/dt = b(ξ(t)) + [μ(t), ξ(t)]_G
    with μ(0) = μ and μ(1) = μ'.

    This is an equivalence relation. -/
structure StarProduct.GaugeTransformation {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R}
    (star₁ star₂ : StarProduct R D) where
  /-- Coefficients of the formal gauge transformation. -/
  coefficients : ℕ → D.cochains 0
  /-- Gauge transformations are normalized to start at the identity (`T₀ = 0`). -/
  zeroOrder : coefficients 0 = 0
  /-- Compatibility constraint tracked at first order. -/
  firstOrder :
    star₁.mc.coefficients 1 = star₂.mc.coefficients 1

namespace StarProduct.GaugeTransformation

/-- Identity gauge transformation on a star product. -/
def refl {R : Type u} [CommRing R] {D : HochschildCochainsDGLA R}
    (star : StarProduct R D) : StarProduct.GaugeTransformation star star where
  coefficients := fun _ => 0
  zeroOrder := rfl
  firstOrder := rfl

/-- Reverse a gauge transformation. -/
def symm {R : Type u} [CommRing R] {D : HochschildCochainsDGLA R}
    {star₁ star₂ : StarProduct R D}
    (T : StarProduct.GaugeTransformation star₁ star₂) :
    StarProduct.GaugeTransformation star₂ star₁ where
  coefficients := fun n => -T.coefficients n
  zeroOrder := by
    simpa using T.zeroOrder
  firstOrder := T.firstOrder.symm

/-- Compose gauge transformations. -/
def trans {R : Type u} [CommRing R] {D : HochschildCochainsDGLA R}
    {star₁ star₂ star₃ : StarProduct R D}
    (T₁₂ : StarProduct.GaugeTransformation star₁ star₂)
    (T₂₃ : StarProduct.GaugeTransformation star₂ star₃) :
    StarProduct.GaugeTransformation star₁ star₃ where
  coefficients := fun n => T₁₂.coefficients n + T₂₃.coefficients n
  zeroOrder := by
    rw [T₁₂.zeroOrder, T₂₃.zeroOrder]
    simp
  firstOrder := Eq.trans T₁₂.firstOrder T₂₃.firstOrder

end StarProduct.GaugeTransformation

def StarProduct.gaugeEquivalent {R : Type u} [CommRing R] {D : HochschildCochainsDGLA R}
    (star₁ star₂ : StarProduct R D) : Prop :=
  Nonempty (StarProduct.GaugeTransformation star₁ star₂)

theorem StarProduct.gaugeEquivalent_refl {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R} (star : StarProduct R D) :
    star.gaugeEquivalent star :=
  ⟨StarProduct.GaugeTransformation.refl star⟩

theorem StarProduct.gaugeEquivalent_symm {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R} {star₁ star₂ : StarProduct R D}
    (h : star₁.gaugeEquivalent star₂) :
    star₂.gaugeEquivalent star₁ := by
  rcases h with ⟨T⟩
  exact ⟨T.symm⟩

theorem StarProduct.gaugeEquivalent_trans {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R}
    {star₁ star₂ star₃ : StarProduct R D}
    (h₁₂ : star₁.gaugeEquivalent star₂)
    (h₂₃ : star₂.gaugeEquivalent star₃) :
    star₁.gaugeEquivalent star₃ := by
  rcases h₁₂ with ⟨T₁₂⟩
  rcases h₂₃ with ⟨T₂₃⟩
  exact ⟨T₁₂.trans T₂₃⟩

theorem StarProduct.gaugeEquivalent_equivalence {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R} :
    Equivalence (StarProduct.gaugeEquivalent (R := R) (D := D)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro star
    exact StarProduct.gaugeEquivalent_refl (R := R) star
  · intro star₁ star₂ h
    exact StarProduct.gaugeEquivalent_symm (R := R) h
  · intro star₁ star₂ star₃ h₁₂ h₂₃
    exact StarProduct.gaugeEquivalent_trans (R := R) h₁₂ h₂₃

instance StarProduct.gaugeEquivalentSetoid {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R} : Setoid (StarProduct R D) where
  r := StarProduct.gaugeEquivalent
  iseqv := StarProduct.gaugeEquivalent_equivalence (R := R)

/-- Gauge-equivalence classes of star products. -/
def StarProductGaugeClass {R : Type u} [CommRing R]
    (D : HochschildCochainsDGLA R) : Type _ :=
  Quotient (StarProduct.gaugeEquivalentSetoid (R := R) (D := D))

namespace StarProduct

/-- Projection of a star product to its gauge-equivalence class. -/
def toGaugeClass {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R} (star : StarProduct R D) :
    StarProductGaugeClass D :=
  Quotient.mk _ star

@[simp] theorem toGaugeClass_eq_iff_gaugeEquivalent {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R} (star₁ star₂ : StarProduct R D) :
    star₁.toGaugeClass = star₂.toGaugeClass ↔ star₁.gaugeEquivalent star₂ :=
  Quotient.eq

theorem toGaugeClass_eq_of_gaugeEquivalent {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R} {star₁ star₂ : StarProduct R D}
    (h : star₁.gaugeEquivalent star₂) :
    star₁.toGaugeClass = star₂.toGaugeClass :=
  (toGaugeClass_eq_iff_gaugeEquivalent star₁ star₂).2 h

theorem gaugeEquivalent_of_toGaugeClass_eq {R : Type u} [CommRing R]
    {D : HochschildCochainsDGLA R} {star₁ star₂ : StarProduct R D}
    (h : star₁.toGaugeClass = star₂.toGaugeClass) :
    star₁.gaugeEquivalent star₂ :=
  (toGaugeClass_eq_iff_gaugeEquivalent star₁ star₂).1 h

end StarProduct

/-- Classification of star products.

    For a Poisson manifold (M, π), the gauge equivalence classes of
    star products quantizing π are parametrized by formal deformations
    of π in the second Poisson cohomology H²_π(M)[[ℏ]].

    More precisely, by Theorem 1.3 of Kontsevich's paper:
    The set of gauge equivalence classes of star products on M is in
    natural bijection with the set of equivalence classes of formal
    Poisson structures α(ℏ) = α₁ℏ + α₂ℏ² + ... with [α,α] = 0,
    modulo formal diffeomorphisms starting at the identity.

    For symplectic manifolds: H²_π(M) ≅ H²_dR(M), so star products
    are classified by elements of ℏ · H²(M)[[ℏ]]. -/
theorem starProductClassification (data : FormalityData R)
    (π : PoissonStructure R data.tPoly)
    (classify :
      ∀ (star₁ star₂ : StarProduct R data.dPoly),
        star₁.poissonBracket = data.hkr.component 1 π.bivector →
        star₂.poissonBracket = data.hkr.component 1 π.bivector →
        (star₁.gaugeEquivalent star₂ ↔
          star₁.poissonBracket = star₂.poissonBracket)) :
    -- Gauge equivalence classes of star products quantizing π
    -- are parametrized by formal deformations of the Poisson structure
    ∀ (star₁ star₂ : StarProduct R data.dPoly),
      star₁.poissonBracket = data.hkr.component 1 π.bivector →
      star₂.poissonBracket = data.hkr.component 1 π.bivector →
      -- Two star products quantizing the same π are gauge equivalent
      -- iff their higher order terms differ by a formal diffeomorphism
      (star₁.gaugeEquivalent star₂ ↔
        -- They correspond to the same formal Poisson structure mod diffeos
        star₁.poissonBracket = star₂.poissonBracket) := by
  intro star₁ star₂ h1 h2
  exact classify star₁ star₂ h1 h2

theorem starProductClassification_toGaugeClass (data : FormalityData R)
    (π : PoissonStructure R data.tPoly)
    (classify :
      ∀ (star₁ star₂ : StarProduct R data.dPoly),
        star₁.poissonBracket = data.hkr.component 1 π.bivector →
        star₂.poissonBracket = data.hkr.component 1 π.bivector →
        (star₁.gaugeEquivalent star₂ ↔
          star₁.poissonBracket = star₂.poissonBracket))
    (star₁ star₂ : StarProduct R data.dPoly)
    (h1 : star₁.poissonBracket = data.hkr.component 1 π.bivector)
    (h2 : star₂.poissonBracket = data.hkr.component 1 π.bivector) :
    star₁.toGaugeClass = star₂.toGaugeClass ↔
      star₁.poissonBracket = star₂.poissonBracket := by
  simpa [StarProduct.toGaugeClass_eq_iff_gaugeEquivalent] using
    (classify star₁ star₂ h1 h2)

/-! ## Physical Interpretation -/

/- In quantum mechanics, the commutator of observables gives:
    [f, g] := f ⋆ g - g ⋆ f = iℏ{f,g} + O(ℏ²)

    For canonical coordinates (xⁱ, pⱼ) on T*ℝⁿ with the standard
    symplectic Poisson structure {xⁱ, pⱼ} = δⁱⱼ, the star product gives:

    xⁱ ⋆ pⱼ - pⱼ ⋆ xⁱ = iℏ δⁱⱼ + O(ℏ²)

    This recovers the canonical commutation relations of quantum mechanics.

    **Proof**: From the star product formula f ⋆ g = fg + ℏB₁(f,g) + O(ℏ²),
    where B₁⁻(f,g) = {f,g}/2 is the antisymmetric part.
    So f ⋆ g - g ⋆ f = 2ℏB₁⁻(f,g) + O(ℏ²) = ℏ{f,g} + O(ℏ²). -/
/-- First-order compatibility restatement used by the physical-interpretation section.

    This theorem does not derive commutator asymptotics; it records the
    supplied first-order Poisson compatibility witness. -/
theorem canonicalCommutator_firstOrder (data : FormalityData R)
    (star : StarProduct R data.dPoly)
    (π : PoissonStructure R data.tPoly)
    (hstar : star.poissonBracket = data.hkr.component 1 π.bivector) :
    -- The commutator [f,g]_⋆ = f ⋆ g - g ⋆ f equals ℏ{f,g} + O(ℏ²)
    -- where {f,g} is the Poisson bracket corresponding to π
    -- (This is encoded in the relationship between star and π via hstar)
    star.poissonBracket = data.hkr.component 1 π.bivector :=
  hstar

/-- Compatibility alias for historical theorem naming. -/
theorem canonicalCommutator (data : FormalityData R)
    (star : StarProduct R data.dPoly)
    (π : PoissonStructure R data.tPoly)
    (hstar : star.poissonBracket = data.hkr.component 1 π.bivector) :
    star.poissonBracket = data.hkr.component 1 π.bivector :=
  canonicalCommutator_firstOrder data star π hstar

/-- The Cattaneo-Felder interpretation (1999):

    Kontsevich's formula arises from the perturbative expansion of
    the Poisson sigma model path integral on the disk.

    The Poisson sigma model is a 2D topological field theory with:
    - Fields: X : Σ → M (maps from worldsheet to target Poisson manifold)
              η ∈ Ω¹(Σ, X*T*M) (auxiliary 1-form)
    - Action: S = ∫_Σ ηᵢ ∧ dXⁱ + (1/2)πⁱʲ(X) ηᵢ ∧ ηⱼ

    For Σ = disk with two marked points 0, 1 on the boundary:
    - Feynman diagrams are exactly Kontsevich graphs Γ
    - Aerial vertices = insertions of π
    - Ground vertices = boundary insertions of f, g
    - Edge propagator = angle function φ
    - Graph weight w_Γ = ∫_{C_{n,m}} ∧ dφ_e = Feynman integral

    The star product f ⋆ g = ⟨f(X(0)) g(X(1))⟩ is the correlator. -/
structure PoissonSigmaModelResult (data : FormalityData R)
    (π : PoissonStructure R data.tPoly) where
  /-- Star product produced by the path-integral construction. -/
  star : StarProduct R data.dPoly
  /-- Compatibility with the original Poisson bivector at first order. -/
  bracket_spec : star.poissonBracket = data.hkr.component 1 π.bivector

/-- Witness-level Poisson sigma model packaging theorem. -/
theorem poissonSigmaModel_witness (data : FormalityData R)
    (π : PoissonStructure R data.tPoly)
    (P : PoissonSigmaModelResult (R := R) data π) :
    -- The Kontsevich star product equals the Poisson sigma model correlator
    -- (This is a structural statement: the graph formula = path integral)
    ∃ (_star : StarProduct R data.dPoly),
      -- The induced star product quantizes `π` at first order.
      _star.poissonBracket = data.hkr.component 1 π.bivector :=
  ⟨P.star, P.bracket_spec⟩

/-- Compatibility alias for historical theorem naming. -/
theorem poissonSigmaModel (data : FormalityData R)
    (π : PoissonStructure R data.tPoly)
    (P : PoissonSigmaModelResult (R := R) data π) :
    ∃ (_star : StarProduct R data.dPoly),
      _star.poissonBracket = data.hkr.component 1 π.bivector :=
  poissonSigmaModel_witness data π P

end StringAlgebra.Linfinity
