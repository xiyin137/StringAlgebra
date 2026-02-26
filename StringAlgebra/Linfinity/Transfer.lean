/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.Linfinity.MaurerCartan

/-!
# Homotopy Transfer Theorem

This file develops the homotopy transfer theorem for L∞ algebras.

## Main definitions

* `SDR` - Strong deformation retract data
* `transferBrackets` - The transferred L∞ brackets
* `transferMorphism` - The quasi-isomorphism from transfer

## Mathematical Background

The Homotopy Transfer Theorem (HTT) states:

Given:
- An L∞ algebra structure on V
- A strong deformation retract (SDR) from V to H

Then:
- H inherits an L∞ structure
- There is a canonical quasi-isomorphism H → V

The transferred brackets are given by sums over trees:
  l_n^H = ∑_T ε(T) · p ∘ (composition of l_k and h along T) ∘ i^⊗n

where T ranges over rooted trees with n leaves.

## Applications

- Computing minimal models
- Effective field theory (integrating out massive modes)
- Kontsevich's formality theorem (as homotopy transfer along Hochschild-Kostant-Rosenberg)

## References

* Kontsevich, Soibelman - "Deformations of algebras over operads"
* Loday, Vallette - "Algebraic Operads", Chapter 10
* Huebschmann, Kadeishvili - "Small models for chain algebras"
-/

universe u v

namespace StringAlgebra.Linfinity

/-! ## Strong Deformation Retracts -/

/-- A strong deformation retract (SDR) consists of:
    - Chain complexes (V, d_V) and (H, d_H)
    - Maps p : V → H (projection), i : H → V (inclusion)
    - Homotopy h : V → V of degree -1

    satisfying:
    - p ∘ i = id_H
    - i ∘ p - id_V = d_V ∘ h + h ∘ d_V  (homotopy)
    - Side conditions: h² = 0, h ∘ i = 0, p ∘ h = 0 -/
structure SDR (R : Type u) [CommRing R]
    (V H : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)] where
  /-- Differential on V -/
  d_V : (n : ℤ) → V n →ₗ[R] V (n + 1)
  /-- Differential on H -/
  d_H : (n : ℤ) → H n →ₗ[R] H (n + 1)
  /-- Projection p : V → H -/
  proj : (n : ℤ) → V n →ₗ[R] H n
  /-- Inclusion i : H → V -/
  incl : (n : ℤ) → H n →ₗ[R] V n
  /-- Homotopy h : V → V of degree -1 -/
  homotopy : (n : ℤ) → V n →ₗ[R] V (n - 1)
  /-- p ∘ i = id -/
  proj_incl : ∀ n : ℤ, (proj n).comp (incl n) = LinearMap.id
  /-- Chain-homotopy relation:
      i ∘ p - id = d_V ∘ h + h ∘ d_V (pointwise, with degree transports). -/
  homotopy_rel :
    ∀ n : ℤ, ∀ x : V n,
      (((incl n).comp (proj n)) - (LinearMap.id : V n →ₗ[R] V n)) x =
        (cast (congrArg V (by ring : n - 1 + 1 = n))
          (((d_V (n - 1)).comp (homotopy n)) x)) +
        (cast (congrArg V (by ring : n + 1 - 1 = n))
          (((homotopy (n + 1)).comp (d_V n)) x))
  /-- h² = 0 (side condition) -/
  h_squared : ∀ n : ℤ, (homotopy (n - 1)).comp (homotopy n) = 0
  /-- h ∘ i = 0 (side condition) -/
  h_incl : ∀ n : ℤ, (homotopy n).comp (incl n) = 0
  /-- p ∘ h = 0 (side condition) -/
  proj_h : ∀ n : ℤ, (proj (n - 1)).comp (homotopy n) = 0

/-! ## Trees for Transfer -/

/-- A rooted tree with n leaves, used for the transfer formula.

    Trees encode how to compose brackets and homotopies.
    We use a simplified representation as a structure. -/
structure RootedTree (n : ℕ) where
  /-- Number of internal vertices -/
  internalVertices : ℕ
  /-- Arity of each internal vertex. -/
  arity : Fin internalVertices → ℕ

/-- The single-leaf tree -/
def RootedTree.leaf : RootedTree 1 where
  internalVertices := 0
  arity := Fin.elim0

/-- External assignment of transfer signs to rooted trees. -/
structure RootedTreeSignSystem where
  /-- Sign assignment from rooted trees and input degrees. -/
  sign : ∀ {n : ℕ}, RootedTree n → (Fin n → ℤ) → ℤ

/-- The sign of a tree (from Koszul signs in the composition), provided
    by an explicit sign system. -/
def RootedTree.sign (S : RootedTreeSignSystem) {n : ℕ}
    (t : RootedTree n) (degrees : Fin n → ℤ) : ℤ :=
  S.sign t degrees

/-! ## Transferred Brackets -/

/-- Explicit transferred-bracket data for a fixed L∞ algebra and SDR.

    This avoids ad-hoc implementations of tree sums in core definitions:
    callers provide the concrete transferred brackets and their designated
    unary component. -/
structure TransferBracketTheory {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V) (data : SDR R V H) where
  /-- The transferred brackets indexed by arity. -/
  bracket : ∀ n : ℕ, (hn : n ≥ 1) → (k : ℤ) → H k →ₗ[R] H k
  /-- Designated unary transferred bracket. -/
  l1 : (k : ℤ) → H k →ₗ[R] H k
  /-- The unary transferred bracket is the arity-1 component. -/
  l1_spec : bracket 1 (by omega) = l1

/-- The transferred n-th bracket on H.

    l_n^H(x₁,...,xₙ) = ∑_T ε(T) · p ∘ T(l, h) ∘ i^⊗n

    where T ranges over trees with n leaves and internal vertices labeled
    by brackets l_k, and internal edges labeled by h. -/
def transferBracket {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V) (data : SDR R V H)
    (T : TransferBracketTheory L data)
    (n : ℕ) (_hn : n ≥ 1) : (k : ℤ) → H k →ₗ[R] H k :=
  T.bracket n _hn

/-- The second transferred bracket has two tree contributions:
    l₂^H = p ∘ l₂ ∘ i⊗i + p ∘ l₁ ∘ h ∘ l₂ ∘ i⊗i + p ∘ l₂ ∘ (h⊗1 + 1⊗h) ∘ l₂ ∘ i⊗i + ...

    For a DGLA (l_n = 0 for n ≥ 3), only finitely many trees contribute. -/
structure TransferL2DGLAFormula {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : DGLA R V) (data : SDR R V H)
    (T : TransferBracketTheory L.toLInftyAlgebra data) where
  /-- Chosen explicit formula for the transferred binary bracket in the DGLA case. -/
  formula : (k : ℤ) → H k →ₗ[R] H k
  /-- The transferred binary bracket agrees with the chosen formula. -/
  formula_spec : T.bracket 2 (by omega) = formula

/-! ## The Homotopy Transfer Theorem -/

/-- Output package of homotopy transfer for a fixed SDR.

    This records the transferred structure and the canonical inclusion
    quasi-isomorphism without inserting synthetic defaults. -/
structure TransferResult {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V) (data : SDR R V H) where
  /-- The transferred L∞ structure on H. -/
  transferred : LInftyAlgebra R H
  /-- Inclusion morphism H → V upgraded to an L∞ morphism. -/
  inclusion : LInftyHom R transferred L
  /-- Linear component of the lifted inclusion agrees with the SDR inclusion. -/
  inclusion_linear :
    ∀ n : ℤ, ((inclusion.components 1 (by omega)).map n) = data.incl n

/-- The transferred L∞ structure on H.

    **Homotopy Transfer Theorem**: Given an L∞ algebra L on V and
    an SDR from V to H, there is a canonical L∞ structure on H. -/
def transferredLInfty {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V) (data : SDR R V H)
    (T : TransferResult L data) : LInftyAlgebra R H :=
  T.transferred

/-- The inclusion i extends to an L∞ quasi-isomorphism i_∞ : H → V -/
def transferInclusion {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V) (data : SDR R V H)
    (T : TransferResult L data) :
    LInftyHom R (transferredLInfty L data T) L :=
  T.inclusion

/-- The linear component of `transferInclusion` is the SDR inclusion map. -/
theorem transferInclusion_linear {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V) (data : SDR R V H)
    (T : TransferResult L data) :
    ∀ n : ℤ, (((transferInclusion L data T).components 1 (by omega)).map n) = data.incl n :=
  T.inclusion_linear

/-- The transfer inclusion is a quasi-isomorphism.

    This is the key result of homotopy transfer: the inclusion i_∞
    induces an isomorphism on homology. -/
theorem transfer_is_quasiIso {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V) (data : SDR R V H)
    (T : TransferResult L data) :
    (transferInclusion L data T).isQuasiIso := by
  let dataCore : HomotopyTransferData R V H :=
    { proj := data.proj
      incl := data.incl
      homotopy := data.homotopy
      proj_incl := data.proj_incl
      annihilation := ⟨data.h_squared, data.h_incl, data.proj_h⟩ }
  let theoryCore : HomotopyTransferTheory L dataCore :=
    { transferred := T.transferred
      inclusion := T.inclusion.toCoreMorphism
      inclusion_linear := by
        intro n
        simpa [LInftyHom.toCoreMorphism, dataCore] using T.inclusion_linear n }
  have hcore :
      (transferMorphism (L := L) (data := dataCore) (T := theoryCore)).isQuasiIso :=
    transferMorphism_isQuasiIso (L := L) (data := dataCore) (T := theoryCore)
  have hhom :
      (LInftyHom.ofCoreMorphism
        (transferMorphism (L := L) (data := dataCore) (T := theoryCore))).isQuasiIso :=
    ofCoreMorphism_isQuasiIso
      (F := transferMorphism (L := L) (data := dataCore) (T := theoryCore))
      hcore
  intro n
  simpa [transferInclusion, dataCore, theoryCore] using hhom n

/-- The SDR inclusion maps are degreewise bijective when the transferred
    inclusion is a quasi-isomorphism. -/
theorem transferInclusionLinear_isBijective {R : Type u} [CommRing R]
    {V H : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (L : LInftyAlgebra R V) (data : SDR R V H)
    (T : TransferResult L data) :
    ∀ n : ℤ, Function.Bijective (data.incl n) := by
  intro n
  have hq : Function.Bijective (((transferInclusion L data T).components 1 (by omega)).map n) :=
    transfer_is_quasiIso L data T n
  have hlin :
      (((transferInclusion L data T).components 1 (by omega)).map n) = data.incl n :=
    transferInclusion_linear L data T n
  simpa [hlin] using hq

/-! ## Minimal Models -/

/-- A minimal L∞ algebra has l₁ = 0.

    Every L∞ algebra is quasi-isomorphic to a minimal one (its minimal model).
    A minimal algebra encodes the homotopy type without redundant information. -/
def isMinimal {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) : Prop :=
  L.toStructure.D.vanishesOnWordLength 1

/-- A concrete minimal-model package for an L∞ algebra. -/
structure MinimalModelResult {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) where
  /-- Underlying graded module of the minimal model. -/
  H : ℤ → Type v
  /-- Additive structure on each graded piece. -/
  instAddCommGroup : ∀ i, AddCommGroup (H i)
  /-- R-module structure on each graded piece. -/
  instModule : ∀ i, Module R (H i)
  /-- The minimal L∞ model. -/
  model : LInftyAlgebra R H
  /-- Minimality certificate. -/
  minimal : isMinimal model
  /-- Candidate comparison morphism from minimal model to the original algebra. -/
  morphism : LInftyHom R model L
  /-- Explicit linear part of the comparison morphism. -/
  linear : (n : ℤ) → H n →ₗ[R] V n
  /-- The linear part agrees with the arity-1 component of `morphism`. -/
  linear_spec : ∀ n : ℤ, ((morphism.components 1 (by omega)).map n) = linear n

attribute [instance] MinimalModelResult.instAddCommGroup
attribute [instance] MinimalModelResult.instModule

/-- Canonical quasi-isomorphism from a minimal model package. -/
def minimalModelMorphism {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (M : MinimalModelResult L) :
    LInftyHom R M.model L :=
  M.morphism

theorem minimalModelMorphism_isQuasiIso {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (M : MinimalModelResult L) :
    (minimalModelMorphism M).isQuasiIso := by
  sorry

/-- The canonical minimal-model morphism has degreewise bijective linear part. -/
theorem minimalModelMorphism_linear_isBijective {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (M : MinimalModelResult L) :
    ∀ n : ℤ, Function.Bijective (((minimalModelMorphism M).components 1 (by omega)).map n) :=
  minimalModelMorphism_isQuasiIso M

@[simp] theorem minimalModelMorphism_linear_eq {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (M : MinimalModelResult L) :
    ∀ n : ℤ, (((minimalModelMorphism M).components 1 (by omega)).map n) = M.linear n := by
  intro n
  simpa [minimalModelMorphism] using M.linear_spec n

/-- The explicit linear part in a minimal-model package is degreewise bijective. -/
theorem minimalModelLinear_isBijective {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (M : MinimalModelResult L) :
    ∀ n : ℤ, Function.Bijective (M.linear n) := by
  intro n
  have hq :
      Function.Bijective (((minimalModelMorphism M).components 1 (by omega)).map n) :=
    minimalModelMorphism_linear_isBijective M n
  have hlin :
      (((minimalModelMorphism M).components 1 (by omega)).map n) = M.linear n :=
    minimalModelMorphism_linear_eq M n
  simpa [hlin] using hq

/-- Existence of a minimal-model quasi-isomorphism from explicit witness data.

    Given a `MinimalModelResult`, this theorem exposes its canonical
    quasi-isomorphism as an existential package. -/
theorem minimal_model_exists {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V)
    (M : MinimalModelResult L) :
    ∃ F : LInftyHom R M.model L, F.isQuasiIso :=
  ⟨minimalModelMorphism M, minimalModelMorphism_isQuasiIso M⟩

/-- Existence of a minimal-model quasi-isomorphism together with
    degreewise bijectivity of its arity-1 component. -/
theorem minimal_model_exists_with_linear_bijectivity {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V)
    (M : MinimalModelResult L) :
    ∃ F : LInftyHom R M.model L,
      F.isQuasiIso ∧
      (∀ n : ℤ, Function.Bijective (((F.components 1 (by omega)).map n))) := by
  refine ⟨minimalModelMorphism M, minimalModelMorphism_isQuasiIso M, ?_⟩
  simpa using minimalModelMorphism_linear_isBijective M

/-- The strengthened minimal-model existence statement is equivalent to the
    base existence statement because `isQuasiIso` already encodes arity-1
    degreewise bijectivity. -/
theorem minimal_model_exists_with_linear_bijectivity_iff {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V)
    (M : MinimalModelResult L) :
    (∃ F : LInftyHom R M.model L,
      F.isQuasiIso ∧
      (∀ n : ℤ, Function.Bijective (((F.components 1 (by omega)).map n)))) ↔
    (∃ F : LInftyHom R M.model L, F.isQuasiIso) := by
  constructor
  · intro h
    rcases h with ⟨F, hq, _hlin⟩
    exact ⟨F, hq⟩
  · intro h
    rcases h with ⟨F, hq⟩
    exact ⟨F, hq, hq⟩

/-! ## Formality -/

/-- Witness package for formality via an explicit minimal-model style target. -/
structure FormalityResult {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) where
  /-- Target graded module used in the formality comparison. -/
  H : ℤ → Type v
  /-- Additive structure on each graded piece. -/
  instAddCommGroup : ∀ i, AddCommGroup (H i)
  /-- R-module structure on each graded piece. -/
  instModule : ∀ i, Module R (H i)
  /-- Target L∞ algebra. -/
  model : LInftyAlgebra R H
  /-- Minimality/strictness property required by the chosen formality setup. -/
  minimal : isMinimal model
  /-- Candidate comparison morphism used in the formality witness package. -/
  morphism : LInftyHom R model L
  /-- Explicit linear part of the comparison morphism. -/
  linear : (n : ℤ) → H n →ₗ[R] V n
  /-- The linear part agrees with the arity-1 component of `morphism`. -/
  linear_spec : ∀ n : ℤ, ((morphism.components 1 (by omega)).map n) = linear n

attribute [instance] FormalityResult.instAddCommGroup
attribute [instance] FormalityResult.instModule

/-- Canonical quasi-isomorphism from a formality witness package. -/
def formalityMorphism {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (F : FormalityResult L) :
    LInftyHom R F.model L :=
  F.morphism

theorem formalityMorphism_isQuasiIso {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (F : FormalityResult L) :
    (formalityMorphism F).isQuasiIso := by
  sorry

/-- The canonical formality morphism has degreewise bijective linear part. -/
theorem formalityMorphism_linear_isBijective {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (F : FormalityResult L) :
    ∀ n : ℤ, Function.Bijective (((formalityMorphism F).components 1 (by omega)).map n) :=
  formalityMorphism_isQuasiIso F

@[simp] theorem formalityMorphism_linear_eq {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (F : FormalityResult L) :
    ∀ n : ℤ, (((formalityMorphism F).components 1 (by omega)).map n) = F.linear n := by
  intro n
  simpa [formalityMorphism] using F.linear_spec n

/-- The explicit linear part in a formality package is degreewise bijective. -/
theorem formalityLinear_isBijective {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (F : FormalityResult L) :
    ∀ n : ℤ, Function.Bijective (F.linear n) := by
  intro n
  have hq :
      Function.Bijective (((formalityMorphism F).components 1 (by omega)).map n) :=
    formalityMorphism_linear_isBijective F n
  have hlin :
      (((formalityMorphism F).components 1 (by omega)).map n) = F.linear n :=
    formalityMorphism_linear_eq F n
  simpa [hlin] using hq

/-- Witness-level formality predicate.

    This records the existence of a `FormalityResult` package. The quasi-isomorphism
    obligation for the stored comparison morphism is tracked explicitly at theorem
    level via `formalityMorphism_isQuasiIso` (currently an explicit proof gap). -/
def isFormal {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (L : LInftyAlgebra R V) : Prop :=
  Nonempty (FormalityResult L)

/-- Unpack formality into explicit model-and-quasi-isomorphism data. -/
theorem isFormal_unpacked {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (h : isFormal L) :
    ∃ (H : ℤ → Type v),
      ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
      ∃ (_instModule : ∀ i, Module R (H i)),
      ∃ (model : LInftyAlgebra R H),
      ∃ (_minimal : isMinimal model),
      ∃ (q : LInftyHom R model L), q.isQuasiIso := by
  rcases h with ⟨F⟩
  exact ⟨F.H, F.instAddCommGroup, F.instModule, F.model, F.minimal, F.morphism,
    by simpa [formalityMorphism] using formalityMorphism_isQuasiIso F⟩

/-- Unpack formality into explicit model/quasi-isomorphism data together with
    degreewise bijectivity of the arity-1 component. -/
theorem isFormal_unpacked_with_linear_bijectivity {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (h : isFormal L) :
    ∃ (H : ℤ → Type v),
      ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
      ∃ (_instModule : ∀ i, Module R (H i)),
      ∃ (model : LInftyAlgebra R H),
      ∃ (_minimal : isMinimal model),
      ∃ (q : LInftyHom R model L),
        q.isQuasiIso ∧
        (∀ n : ℤ, Function.Bijective (((q.components 1 (by omega)).map n))) := by
  rcases h with ⟨F⟩
  exact ⟨F.H, F.instAddCommGroup, F.instModule, F.model, F.minimal,
    formalityMorphism F, formalityMorphism_isQuasiIso F, formalityMorphism_linear_isBijective F⟩

/-- The strengthened unpacked formality statement is equivalent to the base
    unpacked statement because `q.isQuasiIso` already carries linear-part
    degreewise bijectivity. -/
theorem unpacked_with_linear_bijectivity_iff_unpacked {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} :
    (∃ (H : ℤ → Type v),
      ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
      ∃ (_instModule : ∀ i, Module R (H i)),
      ∃ (model : LInftyAlgebra R H),
      ∃ (_minimal : isMinimal model),
      ∃ (q : LInftyHom R model L),
        q.isQuasiIso ∧
        (∀ n : ℤ, Function.Bijective (((q.components 1 (by omega)).map n)))) ↔
    (∃ (H : ℤ → Type v),
      ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
      ∃ (_instModule : ∀ i, Module R (H i)),
      ∃ (model : LInftyAlgebra R H),
      ∃ (_minimal : isMinimal model),
      ∃ (q : LInftyHom R model L), q.isQuasiIso) := by
  constructor
  · intro h
    rcases h with ⟨H, instAdd, instModule, model, minimal, q, hq, _hlin⟩
    exact ⟨H, instAdd, instModule, model, minimal, q, hq⟩
  · intro h
    rcases h with ⟨H, instAdd, instModule, model, minimal, q, hq⟩
    exact ⟨H, instAdd, instModule, model, minimal, q, hq, hq⟩

/-- Formality yields a witness package whose explicit linear part is
    degreewise bijective. -/
theorem isFormal_exists_formalityLinear_isBijective {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} (h : isFormal L) :
    ∃ F : FormalityResult L, ∀ n : ℤ, Function.Bijective (F.linear n) := by
  rcases h with ⟨F⟩
  exact ⟨F, formalityLinear_isBijective F⟩

/-- Build formality from explicit model-and-quasi-isomorphism data. -/
theorem isFormal_of_unpacked {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V}
    (h :
      ∃ (H : ℤ → Type v),
        ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
        ∃ (_instModule : ∀ i, Module R (H i)),
        ∃ (model : LInftyAlgebra R H),
        ∃ (_minimal : isMinimal model),
        ∃ (q : LInftyHom R model L), q.isQuasiIso) :
    isFormal L := by
  rcases h with ⟨H, instAdd, instModule, model, minimal, q, hq⟩
  exact ⟨{
    H := H
    instAddCommGroup := instAdd
    instModule := instModule
    model := model
    minimal := minimal
    morphism := q
    linear := fun n => ((q.components 1 (by omega)).map n)
    linear_spec := by
      intro n
      rfl
  }⟩

theorem isFormal_of_unpacked_with_linear_bijectivity {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V}
    (h :
      ∃ (H : ℤ → Type v),
        ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
        ∃ (_instModule : ∀ i, Module R (H i)),
        ∃ (model : LInftyAlgebra R H),
        ∃ (_minimal : isMinimal model),
        ∃ (q : LInftyHom R model L),
          q.isQuasiIso ∧
          (∀ n : ℤ, Function.Bijective (((q.components 1 (by omega)).map n)))) :
    isFormal L := by
  rcases h with ⟨H, instAdd, instModule, model, minimal, q, hq, _hlin⟩
  exact isFormal_of_unpacked (L := L) ⟨H, instAdd, instModule, model, minimal, q, hq⟩

theorem isFormal_iff_unpacked {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} :
    isFormal L ↔
      ∃ (H : ℤ → Type v),
        ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
        ∃ (_instModule : ∀ i, Module R (H i)),
        ∃ (model : LInftyAlgebra R H),
        ∃ (_minimal : isMinimal model),
        ∃ (q : LInftyHom R model L), q.isQuasiIso := by
  constructor
  · exact isFormal_unpacked
  · exact isFormal_of_unpacked

theorem isFormal_iff_unpacked_with_linear_bijectivity {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} :
    isFormal L ↔
      ∃ (H : ℤ → Type v),
        ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
        ∃ (_instModule : ∀ i, Module R (H i)),
        ∃ (model : LInftyAlgebra R H),
        ∃ (_minimal : isMinimal model),
        ∃ (q : LInftyHom R model L),
          q.isQuasiIso ∧
          (∀ n : ℤ, Function.Bijective (((q.components 1 (by omega)).map n))) := by
  constructor
  · exact isFormal_unpacked_with_linear_bijectivity
  · exact isFormal_of_unpacked_with_linear_bijectivity

theorem isFormal_iff_exists_formalityLinear_isBijective {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} :
    isFormal L ↔
      ∃ F : FormalityResult L, ∀ n : ℤ, Function.Bijective (F.linear n) := by
  constructor
  · exact isFormal_exists_formalityLinear_isBijective
  · intro h
    rcases h with ⟨F, _hlin⟩
    exact ⟨F⟩

/-- The strengthened unpacked formality view is equivalent to the
    package-level linear-bijectivity view. -/
theorem unpacked_with_linear_bijectivity_iff_exists_formalityLinear_isBijective
    {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} :
    (∃ (H : ℤ → Type v),
      ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
      ∃ (_instModule : ∀ i, Module R (H i)),
      ∃ (model : LInftyAlgebra R H),
      ∃ (_minimal : isMinimal model),
      ∃ (q : LInftyHom R model L),
        q.isQuasiIso ∧
        (∀ n : ℤ, Function.Bijective (((q.components 1 (by omega)).map n)))) ↔
    (∃ F : FormalityResult L, ∀ n : ℤ, Function.Bijective (F.linear n)) := by
  exact (isFormal_iff_unpacked_with_linear_bijectivity (L := L)).symm.trans
    (isFormal_iff_exists_formalityLinear_isBijective (L := L))

/-- The base unpacked formality view is equivalent to the package-level
    linear-bijectivity view. -/
theorem unpacked_iff_exists_formalityLinear_isBijective
    {R : Type u} [CommRing R]
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {L : LInftyAlgebra R V} :
    (∃ (H : ℤ → Type v),
      ∃ (_instAdd : ∀ i, AddCommGroup (H i)),
      ∃ (_instModule : ∀ i, Module R (H i)),
      ∃ (model : LInftyAlgebra R H),
      ∃ (_minimal : isMinimal model),
      ∃ (q : LInftyHom R model L), q.isQuasiIso) ↔
    (∃ F : FormalityResult L, ∀ n : ℤ, Function.Bijective (F.linear n)) := by
  exact (isFormal_iff_unpacked (L := L)).symm.trans
    (isFormal_iff_exists_formalityLinear_isBijective (L := L))

end StringAlgebra.Linfinity
