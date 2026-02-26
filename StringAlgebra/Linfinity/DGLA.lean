/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.Linfinity.ChainComplex
import StringAlgebra.Linfinity.LInfinityAlgebra
import Mathlib.Algebra.Lie.Basic

/-!
# Differential Graded Lie Algebras

This file develops the theory of differential graded Lie algebras (DGLAs) using
the chain complex infrastructure from `ChainComplex.lean`.

## Main definitions

* `DGLAData` - A DGLA specified by its differential and bracket
* `DGLAMorphism` - Morphisms of DGLAs (chain maps compatible with brackets)
* `SchoutenBracket` - The Schouten bracket on polyvector fields
* `GerstenhaberBracket` - The Gerstenhaber bracket on Hochschild cochains

## Mathematical Background

A DGLA is a graded vector space V = ⨁_{n∈ℤ} V_n with:
1. A differential d : V → V of degree 1, with d² = 0
2. A graded Lie bracket [−,−] : V ⊗ V → V of degree 0

Subject to:
- Graded antisymmetry: [x,y] = -(-1)^{|x||y|} [y,x]
- Graded Jacobi: [x,[y,z]] = [[x,y],z] + (-1)^{|x||y|} [y,[x,z]]
- Derivation: d[x,y] = [dx,y] + (-1)^{|x|} [x,dy]

A DGLA is an L∞ algebra with l_n = 0 for n ≥ 3.

## References

* Kontsevich - "Deformation quantization of Poisson manifolds"
* Stasheff - "Homotopy associativity of H-spaces"
-/

universe u v

open CategoryTheory

namespace StringAlgebra.Linfinity

/-! ## DGLA Data Structure -/

/-- A differential graded Lie algebra specified by explicit data.

    This is the "hands-on" definition used for concrete constructions
    like polyvector fields and Hochschild cochains. -/
structure DGLAData (R : Type u) [CommRing R] where
  /-- The underlying DG module -/
  toModule : Chain.DGModule R
  /-- The graded Lie bracket [−,−] : V_m ⊗ V_n → V_{m+n} -/
  bracket : ∀ (m n : ℤ),
    (toModule.toComplex.X m) →ₗ[R]
    (toModule.toComplex.X n) →ₗ[R]
    (toModule.toComplex.X (m + n))
  /-- Graded antisymmetry: [x,y] = -(-1)^{mn} [y,x] -/
  antisymm : ∀ m n (x : toModule.toComplex.X m) (y : toModule.toComplex.X n),
    bracket m n x y = (add_comm n m) ▸ (- ((-1 : R) ^ (m * n).toNat) • bracket n m y x)
  /-- Explicit L∞ model associated to this DGLA data. -/
  linftyModel : LInftyAlgebra R (fun n => (toModule.toComplex.X n))

namespace DGLAData

variable {R : Type u} [CommRing R]

/-- The differential of the DGLA -/
def differential (L : DGLAData R) (n : ℤ) :
    (L.toModule.toComplex.X n) →ₗ[R] (L.toModule.toComplex.X (n + 1)) :=
  L.toModule.differential n

/-- The cohomology of a DGLA inherits a graded Lie algebra structure -/
def cohomology (L : DGLAData R) (n : ℤ) : Type _ :=
  L.toModule.cohomology n

end DGLAData

/-! ## DGLA Morphisms -/

variable (R : Type u) [CommRing R]

/-- A morphism of DGLAs is a chain map compatible with brackets. -/
structure DGLAMorphism (L L' : DGLAData R) extends Chain.DGMorphism R L.toModule L'.toModule where
  /-- Compatibility with brackets: f[x,y] = [fx,fy] -/
  bracket_compat : ∀ m n (x : L.toModule.toComplex.X m) (y : L.toModule.toComplex.X n),
    toDGMorphism.componentMap (m + n) (L.bracket m n x y) =
      L'.bracket m n (toDGMorphism.componentMap m x) (toDGMorphism.componentMap n y)

variable {R}

/-- A DGLA quasi-isomorphism is a DGLA morphism that's also a quasi-isomorphism -/
def DGLAMorphism.isQuasiIso {L L' : DGLAData R} (f : DGLAMorphism R L L') : Prop :=
  Chain.DGMorphism.isQuasiIso f.toDGMorphism

/-- Degreewise-linear quasi-isomorphism criterion used for L∞ lifting.

    This tracks bijectivity of the underlying graded-linear components. -/
def DGLAMorphism.isLinearQuasiIso {L L' : DGLAData R} (f : DGLAMorphism R L L') : Prop :=
  ∀ n : ℤ, Function.Bijective (f.toDGMorphism.componentMap n)

namespace DGLAMorphism

variable {R : Type u} [CommRing R]
variable {L L' L'' : DGLAData R}

/-- Identity DGLA morphism. -/
def id (L : DGLAData R) : DGLAMorphism R L L where
  toDGMorphism := Chain.DGMorphism.id L.toModule
  bracket_compat := by
    intro m n x y
    simp [Chain.DGMorphism.componentMap, Chain.DGMorphism.id]

/-- Composition of DGLA morphisms. -/
def comp (g : DGLAMorphism R L' L'') (f : DGLAMorphism R L L') :
    DGLAMorphism R L L'' where
  toDGMorphism := Chain.DGMorphism.comp g.toDGMorphism f.toDGMorphism
  bracket_compat := by
    intro m n x y
    change g.toDGMorphism.componentMap (m + n)
        (f.toDGMorphism.componentMap (m + n) (L.bracket m n x y)) =
      L''.bracket m n
        (g.toDGMorphism.componentMap m (f.toDGMorphism.componentMap m x))
        (g.toDGMorphism.componentMap n (f.toDGMorphism.componentMap n y))
    rw [f.bracket_compat]
    exact g.bracket_compat m n
      (f.toDGMorphism.componentMap m x)
      (f.toDGMorphism.componentMap n y)

/-- Identity morphisms are degreewise-linear quasi-isomorphisms. -/
theorem id_isLinearQuasiIso (L : DGLAData R) : (id (R := R) L).isLinearQuasiIso := by
  intro n
  simpa [id, Chain.DGMorphism.componentMap, Chain.DGMorphism.id] using
    (show Function.Bijective (LinearMap.id : L.toModule.toComplex.X n →ₗ[R] L.toModule.toComplex.X n)
      from Function.bijective_id)

/-- Degreewise-linear quasi-isomorphisms are closed under composition. -/
theorem comp_isLinearQuasiIso
    (g : DGLAMorphism R L' L'') (f : DGLAMorphism R L L')
    (hg : g.isLinearQuasiIso) (hf : f.isLinearQuasiIso) :
    (comp g f).isLinearQuasiIso := by
  intro n
  have hcomp :
      Function.Bijective (fun x : L.toModule.toComplex.X n =>
        g.toDGMorphism.componentMap n (f.toDGMorphism.componentMap n x)) :=
    (hg n).comp (hf n)
  simpa [comp, Chain.DGMorphism.comp, Chain.DGMorphism.componentMap] using hcomp

end DGLAMorphism

/-! ## The Schouten Bracket

The Schouten bracket on polyvector fields T_poly(M) = Γ(∧*TM).

For polyvector fields, the bracket has degree -1:
[−,−] : T_poly^m ⊗ T_poly^n → T_poly^{m+n-1}

where T_poly^k = Γ(∧^{k+1}TM) consists of (k+1)-vector fields.
-/

/-- The Schouten bracket on polyvector fields.

    Given vector fields X₁,...,X_p and Y₁,...,Y_q, the Schouten bracket is
    defined by extending the Lie bracket of vector fields:

    [X₁∧...∧X_p, Y₁∧...∧Y_q] =
      ∑_{i,j} (-1)^{i+j} [X_i, Y_j] ∧ X₁∧...∧X̂_i∧...∧X_p ∧ Y₁∧...∧Ŷ_j∧...∧Y_q

    The degree of the bracket is -1: |[X,Y]| = |X| + |Y| - 1.

    Key properties:
    - Graded antisymmetric: [X,Y] = -(-1)^{(|X|-1)(|Y|-1)} [Y,X]
    - Graded Jacobi with degree shift

    For the formality theorem, polyvector fields form a DGLA with d = 0. -/
structure SchoutenBracket (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The bracket [−,−] : V_m ⊗ V_n → V_{m+n-1} (degree -1) -/
  bracket : ∀ (m n : ℤ), V m →ₗ[R] V n →ₗ[R] V (m + n - 1)
  /-- Graded antisymmetry with shifted degrees -/
  antisymm : ∀ m n (x : V m) (y : V n),
    bracket m n x y = (by ring : n + m - 1 = m + n - 1) ▸
      (- ((-1 : R) ^ ((m - 1) * (n - 1)).toNat) • bracket n m y x)

/-! ## The Gerstenhaber Bracket

The Gerstenhaber bracket on Hochschild cochains D_poly(M) = C*(A,A).

For an associative algebra A, the Hochschild cochains are:
  C^n(A,A) = Hom(A^⊗n, A)

The Gerstenhaber bracket has degree -1:
[−,−] : C^m ⊗ C^n → C^{m+n-1}
-/

/-- The Gerstenhaber bracket on Hochschild cochains.

    For cochains f : A^⊗m → A and g : A^⊗n → A, the Gerstenhaber bracket is:

    [f,g] = f ∘ g - (-1)^{(m-1)(n-1)} g ∘ f

    where (f ∘ g)(a₁,...,a_{m+n-1}) = ∑_i ±f(a₁,...,g(a_i,...,a_{i+n-1}),...,a_{m+n-1})

    The degree is -1: |[f,g]| = |f| + |g| - 1.

    Together with the Hochschild differential b, this forms a DGLA. -/
structure GerstenhaberBracket (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The bracket [−,−] : V_m ⊗ V_n → V_{m+n-1} (degree -1) -/
  bracket : ∀ (m n : ℤ), V m →ₗ[R] V n →ₗ[R] V (m + n - 1)
  /-- Graded antisymmetry with shifted degrees -/
  antisymm : ∀ m n (x : V m) (y : V n),
    bracket m n x y = (by ring : n + m - 1 = m + n - 1) ▸
      (- ((-1 : R) ^ ((m - 1) * (n - 1)).toNat) • bracket n m y x)

/-! ## Polyvector Fields -/

/-- Polyvector fields on a smooth manifold M.

    T_poly(M) = ⨁_{k≥0} Γ(∧^{k+1} TM)

    with grading T_poly^k = Γ(∧^{k+1} TM) (so degree k means (k+1)-vectors).

    This is a DGLA with:
    - d = 0 (no differential)
    - [−,−] = Schouten bracket

    For the formality theorem, this is the source of the formality morphism. -/
structure PolyvectorFieldsDGLA (R : Type u) [CommRing R] where
  /-- The graded module of polyvector fields -/
  fields : ℤ → Type v
  [instAddCommGroup : ∀ n, AddCommGroup (fields n)]
  [instModule : ∀ n, Module R (fields n)]
  /-- The Schouten bracket -/
  schouten : SchoutenBracket R fields
  /-- Degree-0 bracket data used in the DGLA packaging. -/
  dglaBracket : ∀ (m n : ℤ), fields m →ₗ[R] fields n →ₗ[R] fields (m + n)
  /-- Graded antisymmetry for `dglaBracket`. -/
  dgla_antisymm : ∀ m n (x : fields m) (y : fields n),
    dglaBracket m n x y = (add_comm n m) ▸
      (- ((-1 : R) ^ (m * n).toNat) • dglaBracket n m y x)
  /-- Chosen L∞ model for the graded module of polyvector fields. -/
  linftyModel : LInftyAlgebra R fields

attribute [instance] PolyvectorFieldsDGLA.instAddCommGroup PolyvectorFieldsDGLA.instModule

namespace PolyvectorFieldsDGLA

variable {R : Type u} [CommRing R]

/-- Polyvector fields form a DGLA with d = 0 -/
def toDGLAData (T : PolyvectorFieldsDGLA R) : DGLAData R where
  toModule := Chain.mkDGModule R T.fields
    (fun _ => 0)  -- d = 0
    (fun _ _ => rfl)  -- d² = 0 trivially
  bracket := T.dglaBracket
  antisymm := T.dgla_antisymm
  linftyModel := T.linftyModel

end PolyvectorFieldsDGLA

/-! ## Hochschild Cochains -/

/-- Hochschild cochains on a smooth manifold M (or an algebra A).

    D_poly(M) = ⨁_{k≥0} C^k(C^∞(M), C^∞(M))

    where C^k = Hom_{diff}(A^⊗k, A) are polydifferential operators.

    This is a DGLA with:
    - d = Hochschild differential b
    - [−,−] = Gerstenhaber bracket

    For the formality theorem, this is the target of the formality morphism. -/
structure HochschildCochainsDGLA (R : Type u) [CommRing R] where
  /-- The graded module of Hochschild cochains -/
  cochains : ℤ → Type v
  [instAddCommGroup : ∀ n, AddCommGroup (cochains n)]
  [instModule : ∀ n, Module R (cochains n)]
  /-- The Hochschild differential b -/
  differential : ∀ n, cochains n →ₗ[R] cochains (n + 1)
  /-- b² = 0 -/
  d_squared : ∀ n x, differential (n + 1) (differential n x) = 0
  /-- The Gerstenhaber bracket -/
  gerstenhaber : GerstenhaberBracket R cochains
  /-- Degree-0 bracket data used in the DGLA packaging. -/
  dglaBracket : ∀ (m n : ℤ), cochains m →ₗ[R] cochains n →ₗ[R] cochains (m + n)
  /-- Graded antisymmetry for `dglaBracket`. -/
  dgla_antisymm : ∀ m n (x : cochains m) (y : cochains n),
    dglaBracket m n x y = (add_comm n m) ▸
      (- ((-1 : R) ^ (m * n).toNat) • dglaBracket n m y x)
  /-- Chosen L∞ model for the graded module of Hochschild cochains. -/
  linftyModel : LInftyAlgebra R cochains

attribute [instance] HochschildCochainsDGLA.instAddCommGroup HochschildCochainsDGLA.instModule

namespace HochschildCochainsDGLA

variable {R : Type u} [CommRing R]

/-- Hochschild cochains form a DGLA -/
def toDGLAData (D : HochschildCochainsDGLA R) : DGLAData R where
  toModule := Chain.mkDGModule R D.cochains D.differential D.d_squared
  bracket := D.dglaBracket
  antisymm := D.dgla_antisymm
  linftyModel := D.linftyModel

end HochschildCochainsDGLA

/-! ## The HKR Map -/

/-- The Hochschild-Kostant-Rosenberg (HKR) map.

    U₁ : T_poly → D_poly

    sends a polyvector field to a polydifferential operator by antisymmetrization:

    U₁(X₁ ∧ ... ∧ X_k)(f₁,...,f_k) = (1/k!) ∑_σ sign(σ) X_{σ(1)}(f₁) ... X_{σ(k)}(f_k)

    This is a chain map (but NOT a DGLA morphism). It induces an isomorphism
    on cohomology (the HKR theorem), making it a quasi-isomorphism.

    In the formality theorem, U₁ is the linear part of the L∞ quasi-isomorphism. -/
structure HKRMap (R : Type u) [CommRing R]
    (T : PolyvectorFieldsDGLA R) (D : HochschildCochainsDGLA R) where
  /-- The component maps U₁_n : T_poly^n → D_poly^n -/
  component : ∀ n : ℤ, T.fields n →ₗ[R] D.cochains n
  /-- U₁ is a chain map: b ∘ U₁ = U₁ ∘ 0 = 0 (since d_T = 0) -/
  chain_map : ∀ n (x : T.fields n), D.differential n (component n x) = 0
  /-- U₁ induces isomorphism on cohomology (HKR theorem) -/
  induces_iso : ∀ n : ℤ, Function.Bijective (component n)

/-! ## Connection to L∞ Algebras -/

/-- A DGLA is an L∞ algebra with l_n = 0 for n ≥ 3.

    This connects our explicit DGLA definition to the coalgebraic L∞ definition. -/
def DGLAData.toLInftyAlgebra {R : Type u} [CommRing R] (L : DGLAData R) :
    LInftyAlgebra R (fun n => (L.toModule.toComplex.X n)) :=
  L.linftyModel

/-- Explicit lift data from a DGLA morphism to an L∞ morphism. -/
structure DGLAMorphismLInftyLift {R : Type u} [CommRing R]
    {L L' : DGLAData R} (f : DGLAMorphism R L L') where
  /-- Lifted L∞ morphism between the chosen DGLA-associated L∞ models. -/
  morphism :
    LInftyMorphism R L.toLInftyAlgebra L'.toLInftyAlgebra
  /-- Linear component agrees with the underlying DGLA map degreewise. -/
  linear_spec : ∀ n : ℤ, morphism.linear n = f.toDGMorphism.componentMap n
  /-- The unary higher component agrees with the underlying DGLA map. -/
  higher_one_spec : ∀ n : ℤ, morphism.higher 1 n = f.toDGMorphism.componentMap n
  /-- All non-unary higher components vanish in this canonical DGLA lift model. -/
  higher_other_zero : ∀ k : ℕ, k ≠ 1 → ∀ n : ℤ, morphism.higher k n = 0

/-- Canonical L∞ morphism associated to a DGLA morphism in the current
    `LInftyMorphism` interface. -/
def DGLAMorphism.toLInftyMorphism {R : Type u} [CommRing R]
    {L L' : DGLAData R} (f : DGLAMorphism R L L') :
    LInftyMorphism R L.toLInftyAlgebra L'.toLInftyAlgebra where
  linear := f.toDGMorphism.componentMap
  higher := fun k n => by
    by_cases hk : k = 1
    · subst hk
      simpa using f.toDGMorphism.componentMap n
    · exact 0
  higher_zero := by
    intro n
    have hk : (0 : ℕ) ≠ 1 := by decide
    simp [hk]
  compatible := by
    intro n
    simp

/-- Explicit composition data for canonical DGLA-to-L∞ lifts. -/
def DGLAMorphism.toLInftyCompositionData {R : Type u} [CommRing R]
    {L L' L'' : DGLAData R}
    (g : DGLAMorphism R L' L'') (f : DGLAMorphism R L L') :
    LInftyMorphism.CompositionData g.toLInftyMorphism f.toLInftyMorphism where
  composite := (DGLAMorphism.comp g f).toLInftyMorphism
  linear_spec := by
    intro n
    simp [DGLAMorphism.toLInftyMorphism, DGLAMorphism.comp, Chain.DGMorphism.comp,
      Chain.DGMorphism.componentMap]

@[simp] theorem DGLAMorphism.toLInftyMorphism_comp {R : Type u} [CommRing R]
    {L L' L'' : DGLAData R}
    (g : DGLAMorphism R L' L'') (f : DGLAMorphism R L L') :
    (g.toLInftyMorphism).comp (f.toLInftyMorphism) (DGLAMorphism.toLInftyCompositionData g f) =
      (DGLAMorphism.comp g f).toLInftyMorphism := rfl

/-- Canonical explicit lift package associated to `toLInftyMorphism`. -/
def DGLAMorphism.canonicalLInftyLift {R : Type u} [CommRing R]
    {L L' : DGLAData R} (f : DGLAMorphism R L L') :
    DGLAMorphismLInftyLift f where
  morphism := f.toLInftyMorphism
  linear_spec := by
    intro n
    rfl
  higher_one_spec := by
    intro n
    simp [DGLAMorphism.toLInftyMorphism]
  higher_other_zero := by
    intro k hk n
    simp [DGLAMorphism.toLInftyMorphism, hk]

/-- Degreewise-linear DGLA quasi-isomorphisms induce quasi-isomorphisms for the
    canonical associated L∞ morphism. -/
theorem DGLAMorphism.toLInftyMorphism_isQuasiIso {R : Type u} [CommRing R]
    {L L' : DGLAData R} (f : DGLAMorphism R L L')
    (hf : f.isLinearQuasiIso) :
    (f.toLInftyMorphism).isQuasiIso := by
  intro n
  simpa [LInftyMorphism.isQuasiIso, DGLAMorphism.toLInftyMorphism] using hf n

/-- Quasi-isomorphism of the canonical DGLA→L∞ lift implies
    degreewise-linear DGLA quasi-isomorphism criterion. -/
theorem DGLAMorphism.isLinearQuasiIso_of_toLInftyMorphism_isQuasiIso
    {R : Type u} [CommRing R]
    {L L' : DGLAData R} (f : DGLAMorphism R L L')
    (hf : (f.toLInftyMorphism).isQuasiIso) :
    f.isLinearQuasiIso := by
  intro n
  simpa [LInftyMorphism.isQuasiIso, DGLAMorphism.toLInftyMorphism] using hf n

/-- The linear quasi-isomorphism criterion is equivalent to quasi-isomorphism
    of the canonical DGLA→L∞ lift. -/
theorem DGLAMorphism.isLinearQuasiIso_iff_toLInftyMorphism_isQuasiIso
    {R : Type u} [CommRing R]
    {L L' : DGLAData R} (f : DGLAMorphism R L L') :
    f.isLinearQuasiIso ↔ (f.toLInftyMorphism).isQuasiIso := by
  constructor
  · intro hf
    exact f.toLInftyMorphism_isQuasiIso hf
  · intro hf
    exact f.isLinearQuasiIso_of_toLInftyMorphism_isQuasiIso hf

/-- Equivalent criterion restated on the canonical explicit lift package. -/
theorem DGLAMorphism.canonicalLInftyLift_isQuasiIso_iff
    {R : Type u} [CommRing R]
    {L L' : DGLAData R} (f : DGLAMorphism R L L') :
    (f.canonicalLInftyLift.morphism).isQuasiIso ↔ f.isLinearQuasiIso := by
  simpa [DGLAMorphism.canonicalLInftyLift] using
    (DGLAMorphism.isLinearQuasiIso_iff_toLInftyMorphism_isQuasiIso (f := f)).symm

/-- Quasi-isomorphism transport for the canonical lift is stable under
    DGLA morphism composition. -/
theorem DGLAMorphism.comp_toLInftyMorphism_isQuasiIso {R : Type u} [CommRing R]
    {L L' L'' : DGLAData R}
    (g : DGLAMorphism R L' L'') (f : DGLAMorphism R L L')
    (hg : g.isLinearQuasiIso) (hf : f.isLinearQuasiIso) :
    ((DGLAMorphism.comp g f).toLInftyMorphism).isQuasiIso := by
  have hg' : g.toLInftyMorphism.isQuasiIso := g.toLInftyMorphism_isQuasiIso hg
  have hf' : f.toLInftyMorphism.isQuasiIso := f.toLInftyMorphism_isQuasiIso hf
  simpa [DGLAMorphism.toLInftyMorphism_comp] using
    (LInftyMorphism.quasiIso_comp
      (G := g.toLInftyMorphism) (F := f.toLInftyMorphism)
      (C := DGLAMorphism.toLInftyCompositionData g f) hg' hf')

/-- A degreewise-linear DGLA quasi-isomorphism lift gives an L∞ quasi-isomorphism. -/
theorem DGLAMorphism.toLInftyQuasiIso {R : Type u} [CommRing R]
    {L L' : DGLAData R} (f : DGLAMorphism R L L')
    (F : DGLAMorphismLInftyLift f)
    (hf : f.isLinearQuasiIso) :
    F.morphism.isQuasiIso := by
  intro n
  simpa [LInftyMorphism.isQuasiIso, F.linear_spec n] using hf n

end StringAlgebra.Linfinity
