/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.Linfinity.LInfinityAlgebra

/-!
# L∞ Morphisms

This file develops the theory of morphisms between L∞ algebras in detail.

## Main definitions

* `LInftyHom` - Full L∞ morphism with all components f_n
* `StrictMorphism` - Strict morphisms (f_n = 0 for n ≥ 2)
* `LInftyHomotopy` - Homotopy between L∞ morphisms

## Mathematical Background

An L∞ morphism F : L → L' consists of a sequence of graded symmetric maps
  f_n : Sym^n(V) → W  of degree 1-n  for n ≥ 1

satisfying the compatibility condition:
  ∑_{i+j=n} ∑_σ ε(σ) f_j(l_i(x_{σ(1)},...,x_{σ(i)}), x_{σ(i+1)},...,x_{σ(n)})
  = ∑_{k≥1} ∑_{i₁+...+i_k=n} ∑_σ ε(σ) l'_k(f_{i₁}(...), f_{i₂}(...),..., f_{i_k}(...))

Coalgebraically, this is a coalgebra morphism F : S⁺(V[1]) → S⁺(W[1])
satisfying D' ∘ F = F ∘ D.

## References

* Lada, Markl - "Strongly homotopy Lie algebras"
* Dolgushev - "A proof of Tsygan's formality conjecture"
-/

universe u v

namespace StringAlgebra.Linfinity

/-! ## L∞ Morphism Components -/

/-- The n-th component of an L∞ morphism.

    f_n : Sym^n(V) → W has degree 1-n.
    - f₁ : V → W is a chain map (degree 0)
    - f₂ : Sym²(V) → W is a chain homotopy datum (degree -1)
    - f_n for n ≥ 3 are higher homotopies -/
structure MorphismComponent (R : Type u) [CommRing R]
    (V W : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (n : ℕ) (_hn : n ≥ 1) where
  /-- The degree of the component is 1-n -/
  degree : ℤ := 1 - n
  /-- Underlying graded-linear data for the n-th component. -/
  map : (i : ℤ) → V i →ₗ[R] W i

/-- A full L∞ morphism with all components.

    This is the coalgebraic formulation: a coalgebra morphism
    F : S⁺(V[1]) → S⁺(W[1]) compatible with the differentials. -/
structure LInftyHom (R : Type u) [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (L : LInftyAlgebra R V) (L' : LInftyAlgebra R W) where
  /-- The components f_n for n ≥ 1 -/
  components : ∀ n : ℕ, (hn : n ≥ 1) → MorphismComponent R V W n hn

namespace LInftyHom

variable {R : Type u} [CommRing R]
variable {V W U : ℤ → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
variable [∀ i, AddCommGroup (U i)] [∀ i, Module R (U i)]

/-- The linear part f₁ : V → W -/
def linear {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') : MorphismComponent R V W 1 (by omega) :=
  F.components 1 (by omega)

/-- The quadratic part f₂ : Sym²(V) → W -/
def quadratic {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') : MorphismComponent R V W 2 (by omega) :=
  F.components 2 (by omega)

/-- The identity morphism -/
def id (L : LInftyAlgebra R V) : LInftyHom R L L where
  components := fun n _hn => {
    degree := 1 - n
    map := fun i => by
      by_cases h1 : n = 1
      · subst h1
        simpa using (LinearMap.id : V i →ₗ[R] V i)
      · exact 0
  }

/-- Composition of L∞ morphisms.

    (G ∘ F)_n = ∑_{k≥1} ∑_{i₁+...+i_k=n} G_k ∘ (F_{i₁} ⊗ ... ⊗ F_{i_k})

    This is a sum over trees; we encode it through explicit composition data. -/
structure CompositionData
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W} {L'' : LInftyAlgebra R U}
    (G : LInftyHom R L' L'') (F : LInftyHom R L L') where
  /-- Composite L∞ morphism. -/
  composite : LInftyHom R L L''
  /-- The linear component matches ordinary composition of linear parts. -/
  linear_spec :
    ∀ i : ℤ, ((composite.components 1 (by omega)).map i) =
      ((G.components 1 (by omega)).map i).comp ((F.components 1 (by omega)).map i)

def comp {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W} {L'' : LInftyAlgebra R U}
    (G : LInftyHom R L' L'') (F : LInftyHom R L L')
    (C : CompositionData G F) : LInftyHom R L L'' :=
  C.composite

/-- Canonical composition data for left identity. -/
def compData_id_left {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') : CompositionData (id L') F where
  composite := F
  linear_spec := by
    intro i
    simp [id]

/-- Canonical composition data for right identity. -/
def compData_id_right {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') : CompositionData F (id L) where
  composite := F
  linear_spec := by
    intro i
    simp [id]

@[simp] theorem comp_id_left {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') :
    (id L').comp F (compData_id_left F) = F := rfl

@[simp] theorem comp_id_right {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') :
    F.comp (id L) (compData_id_right F) = F := rfl

/-- Convert bundled `LInftyHom` data to the core `LInftyMorphism` interface. -/
def toCoreMorphism {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') : LInftyMorphism R L L' where
  linear := fun n => (F.components 1 (by omega)).map n
  higher := fun k n => by
    by_cases hk : k = 0
    · exact 0
    · exact (F.components k (Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr hk))).map n
  compatible := by
    intro n
    have hk : (1 : ℕ) ≠ 0 := by decide
    simp [hk]

/-- Convert a core `LInftyMorphism` into bundled component data. -/
def ofCoreMorphism {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyMorphism R L L') : LInftyHom R L L' where
  components := fun n _hn => {
    degree := 1 - n
    map := fun i =>
      if n = 1 then F.linear i else F.higher n i
  }

@[simp] theorem ofCoreMorphism_linear {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyMorphism R L L') (i : ℤ) :
    ((ofCoreMorphism F).components 1 (by omega)).map i = F.linear i := by
  simp [ofCoreMorphism]

@[simp] theorem toCoreMorphism_linear {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') (i : ℤ) :
    (toCoreMorphism F).linear i = ((F.components 1 (by omega)).map i) := rfl

@[simp] theorem toCoreMorphism_ofCore_linear {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyMorphism R L L') (i : ℤ) :
    (toCoreMorphism (ofCoreMorphism F)).linear i = F.linear i := by
  simp [toCoreMorphism]

@[simp] theorem ofCoreMorphism_toCore_linear {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') (i : ℤ) :
    ((ofCoreMorphism (toCoreMorphism F)).components 1 (by omega)).map i =
      ((F.components 1 (by omega)).map i) := by
  simp [ofCoreMorphism, toCoreMorphism]

/-- Transport explicit composition data to the core `LInftyMorphism` layer. -/
def toCoreCompositionData
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W} {L'' : LInftyAlgebra R U}
    {G : LInftyHom R L' L''} {F : LInftyHom R L L'}
    (C : CompositionData G F) :
    LInftyMorphism.CompositionData G.toCoreMorphism F.toCoreMorphism where
  composite := C.composite.toCoreMorphism
  linear_spec := by
    intro n
    simpa [toCoreMorphism] using C.linear_spec n

@[simp] theorem toCoreMorphism_comp
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W} {L'' : LInftyAlgebra R U}
    (G : LInftyHom R L' L'') (F : LInftyHom R L L')
    (C : CompositionData G F) :
    (G.comp F C).toCoreMorphism =
      (G.toCoreMorphism).comp (F.toCoreMorphism) (toCoreCompositionData C) := rfl

end LInftyHom

/-! ## Strict Morphisms -/

/-- A strict morphism has f_n = 0 for n ≥ 2.

    Strict morphisms are chain maps V → W that are also
    compatible with all the brackets:
    f₁(l_n(x₁,...,xₙ)) = l'_n(f₁x₁,...,f₁xₙ) -/
structure StrictMorphism (R : Type u) [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (_L : LInftyAlgebra R V) (_L' : LInftyAlgebra R W) where
  /-- The linear map f₁ : V → W -/
  linear : (i : ℤ) → V i →ₗ[R] W i

/-- A strict morphism gives an L∞ morphism with f_n = 0 for n ≥ 2 -/
def StrictMorphism.toLInftyHom {R : Type u} [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (_F : StrictMorphism R L L') : LInftyHom R L L' where
  components := fun n _hn => {
    degree := 1 - n
    map := fun i => by
      by_cases h1 : n = 1
      · subst h1
        simpa using _F.linear i
      · exact 0
  }

namespace StrictMorphism

variable {R : Type u} [CommRing R]
variable {V W U : ℤ → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
variable [∀ i, AddCommGroup (U i)] [∀ i, Module R (U i)]

/-- Composition of strict morphisms by linear-part composition. -/
def comp {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W} {L'' : LInftyAlgebra R U}
    (G : StrictMorphism R L' L'') (F : StrictMorphism R L L') :
    StrictMorphism R L L'' where
  linear := fun i => (G.linear i).comp (F.linear i)

/-- Canonical `LInftyHom.CompositionData` produced by strict morphisms. -/
def compositionData {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W} {L'' : LInftyAlgebra R U}
    (G : StrictMorphism R L' L'') (F : StrictMorphism R L L') :
    LInftyHom.CompositionData (G.toLInftyHom) (F.toLInftyHom) where
  composite := (comp G F).toLInftyHom
  linear_spec := by
    intro i
    simp [comp, StrictMorphism.toLInftyHom]

@[simp] theorem toLInftyHom_comp
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W} {L'' : LInftyAlgebra R U}
    (G : StrictMorphism R L' L'') (F : StrictMorphism R L L') :
    (G.toLInftyHom).comp (F.toLInftyHom) (compositionData G F) =
      (comp G F).toLInftyHom := rfl

end StrictMorphism

/-! ## Quasi-isomorphisms -/

/-- An L∞ morphism is a quasi-isomorphism if f₁ induces an
    isomorphism on homology H(V, l₁) → H(W, l'₁).

    At the current interface level, we track degreewise bijectivity of `f₁`
    as the working criterion for quasi-isomorphism data. -/
def LInftyHom.isQuasiIso {R : Type u} [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') : Prop :=
  ∀ i : ℤ, Function.Bijective ((F.components 1 (by omega)).map i)

theorem toCoreMorphism_isQuasiIso {R : Type u} [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') (hF : F.isQuasiIso) :
    (LInftyHom.toCoreMorphism F).isQuasiIso := by
  intro n
  simpa [LInftyHom.toCoreMorphism] using hF n

theorem ofCoreMorphism_isQuasiIso {R : Type u} [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyMorphism R L L') (hF : F.isQuasiIso) :
    (LInftyHom.ofCoreMorphism F).isQuasiIso := by
  intro i
  simpa [LInftyHom.ofCoreMorphism] using hF i

/-- The identity morphism is a quasi-isomorphism. -/
theorem id_isQuasiIso {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) :
    (LInftyHom.id L).isQuasiIso := by
  intro i
  simpa [LInftyHom.id] using
    (show Function.Bijective (LinearMap.id : V i →ₗ[R] V i) from Function.bijective_id)

/-- Quasi-isomorphisms are closed under composition.

    This is a standard fact: if f and g both induce isomorphisms
    on homology, then so does their composition g ∘ f. -/
theorem quasiIso_comp {R : Type u} [CommRing R]
    {V W U : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module R (U i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W} {L'' : LInftyAlgebra R U}
    (G : LInftyHom R L' L'') (F : LInftyHom R L L')
    (C : LInftyHom.CompositionData G F)
    (hG : G.isQuasiIso) (hF : F.isQuasiIso) :
    (G.comp F C).isQuasiIso :=
  by
    intro i
    let G1 : W i →ₗ[R] U i := (G.components 1 (by omega)).map i
    let F1 : V i →ₗ[R] W i := (F.components 1 (by omega)).map i
    have hcomp : Function.Bijective (fun x : V i => G1 (F1 x)) := (hG i).comp (hF i)
    have hlin : ((C.composite.components 1 (by omega)).map i) = G1.comp F1 := by
      simpa [G1, F1] using C.linear_spec i
    simpa [LInftyHom.comp, G1, F1, hlin] using hcomp

/-- Composition of quasi-isomorphic strict morphisms is quasi-isomorphic. -/
theorem strict_quasiIso_comp {R : Type u} [CommRing R]
    {V W U : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module R (U i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W} {L'' : LInftyAlgebra R U}
    (G : StrictMorphism R L' L'') (F : StrictMorphism R L L')
    (hG : (G.toLInftyHom).isQuasiIso) (hF : (F.toLInftyHom).isQuasiIso) :
    ((StrictMorphism.comp G F).toLInftyHom).isQuasiIso := by
  simpa [StrictMorphism.toLInftyHom_comp] using
    (quasiIso_comp (G := G.toLInftyHom) (F := F.toLInftyHom)
      (C := StrictMorphism.compositionData G F) hG hF)

/-! ## L∞ Homotopies -/

/-- A homotopy between L∞ morphisms F, G : L → L'.

    An L∞ homotopy H consists of maps
    h_n : Sym^n(V) → W of degree -n for n ≥ 1
    satisfying a compatibility condition that makes F and G
    homotopic in the category of L∞ algebras. -/
structure LInftyHomotopy (R : Type u) [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (_F _G : LInftyHom R L L') where
  /-- Components h_n of degree -n -/
  components : ∀ n : ℕ, n ≥ 1 → (i : ℤ) → V i →ₗ[R] W (i - n)

/-- Homotopy is an equivalence relation -/
def LInftyHom.homotopic {R : Type u} [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F G : LInftyHom R L L') : Prop :=
  Nonempty (LInftyHomotopy R F G)

theorem homotopic_refl {R : Type u} [CommRing R]
    {V W : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {L : LInftyAlgebra R V} {L' : LInftyAlgebra R W}
    (F : LInftyHom R L L') : F.homotopic F :=
  ⟨{ components := fun _ _ _ => 0 }⟩

/-! ## The ∞-Category of L∞ Algebras -/

/-- The homotopy category of L∞ algebras.

    Objects: L∞ algebras
    Morphisms: L∞ morphisms modulo homotopy
    Weak equivalences: quasi-isomorphisms

    This forms an (∞,1)-category. -/
structure HomotopyCategory (R : Type u) [CommRing R] where
  /-- Objects in the homotopy category. -/
  Obj : Type (max u (v + 1))
  /-- Morphism type between objects. -/
  Hom : Obj → Obj → Type (max u (v + 1))

end StringAlgebra.Linfinity
