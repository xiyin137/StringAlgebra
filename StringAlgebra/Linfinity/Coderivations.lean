/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.Linfinity.SymmetricCoalgebra

/-!
# Coderivations on the Symmetric Coalgebra

This file defines coderivations on the symmetric coalgebra, which are the
key objects in the coalgebraic definition of L∞ algebras.

## Main definitions

* `Coderivation` - A coderivation D on S(V) satisfying the co-Leibniz rule
* `squareZero` - The condition D² = 0

## Mathematical Background

A coderivation on a coalgebra (C, Δ) is a linear map D : C → C satisfying
the co-Leibniz rule:
  Δ ∘ D = (D ⊗ id + id ⊗ D) ∘ Δ

For the symmetric coalgebra S(V), coderivations are in bijection with
linear maps ⨁_{n≥1} Sym^n(V) → V. Given such a map f, the coderivation D_f
is uniquely determined by the co-Leibniz rule.

An L∞ algebra structure on V is equivalent to a degree 1 coderivation D
on S(V[1]) satisfying D² = 0.

## The Brackets

From a coderivation D, we extract the L∞ brackets:
  l_n : V^⊗n → V
by projecting D|_{Sym^n(V[1])} to V[1] and desuspending.

The condition D² = 0 encodes all the generalized Jacobi identities.

## References

* Loday, Vallette - "Algebraic Operads"
* Lada, Markl - "Strongly homotopy Lie algebras"
-/

universe u v

namespace StringAlgebra.Linfinity

/-! ## Coderivations -/

/-- A coderivation on the symmetric coalgebra.

    A coderivation D : S(V) → S(V) satisfies the co-Leibniz rule:
    Δ ∘ D = (D ⊗ id + id ⊗ D) ∘ Δ

    Coderivations form a Lie algebra under the commutator bracket. -/
structure Coderivation (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The degree of the coderivation -/
  degree : ℤ
  /-- The underlying map on S(V) (represented abstractly) -/
  map : SymCoalg R V → SymCoalg R V
  /-- D preserves word length structure appropriately -/
  degree_shift : ∀ x : SymCoalg R V, (map x).degree = x.degree + degree
  -- The co-Leibniz rule would be stated here with proper tensor product structure

/-- A coderivation on the reduced symmetric coalgebra S⁺(V).

    This is the structure relevant for L∞ algebras. -/
structure ReducedCoderivation (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The degree of the coderivation -/
  degree : ℤ
  /-- The underlying map -/
  map : ReducedSymCoalg R V → ReducedSymCoalg R V
  /-- Word-length components of the coderivation. -/
  componentMap : ∀ (n : ℕ) (_hn : n ≥ 1), ReducedSymCoalg R V → ReducedSymCoalg R V
  /-- Consistency: on word-length-`n` inputs, the `n`-component agrees with `map`. -/
  component_spec :
    ∀ (n : ℕ) (hn : n ≥ 1) (x : ReducedSymCoalg R V), x.wordLength = n →
      componentMap n hn x = map x
  /-- Shape invariant: the extracted `n`-component lands in word length `1`
      on word-length-`n` inputs. -/
  component_wordLength_one :
    ∀ (n : ℕ) (hn : n ≥ 1) (x : ReducedSymCoalg R V), x.wordLength = n →
      (componentMap n hn x).wordLength = 1
  /-- Degree shift property -/
  degree_shift : ∀ x : ReducedSymCoalg R V, (map x).degree = x.degree + degree

/-! ## Operations on Coderivations -/

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Composition of coderivations (not generally a coderivation) -/
def Coderivation.comp (D₁ D₂ : Coderivation R V) : SymCoalg R V → SymCoalg R V :=
  D₁.map ∘ D₂.map

/-- The commutator of coderivations [D₁, D₂] = D₁ ∘ D₂ - (-1)^{|D₁||D₂|} D₂ ∘ D₁

    This IS a coderivation (coderivations form a Lie algebra). -/
structure Coderivation.CommutatorData (D₁ D₂ : Coderivation R V) where
  /-- The underlying commutator map on the coalgebra. -/
  map : SymCoalg R V → SymCoalg R V
  /-- Degree law for the commutator map. -/
  degree_shift : ∀ x : SymCoalg R V, (map x).degree = x.degree + (D₁.degree + D₂.degree)

/-- Build a coderivation from explicit commutator data. -/
def Coderivation.bracket (D₁ D₂ : Coderivation R V) (h : D₁.CommutatorData D₂) : Coderivation R V where
  degree := D₁.degree + D₂.degree
  map := h.map
  degree_shift := h.degree_shift

/-- The square of a coderivation D² = D ∘ D -/
def Coderivation.square (D : Coderivation R V) : SymCoalg R V → SymCoalg R V :=
  D.map ∘ D.map

/-- The square of a coderivation D² = D ∘ D for reduced coalgebra -/
def ReducedCoderivation.square (D : ReducedCoderivation R V) :
    ReducedSymCoalg R V → ReducedSymCoalg R V :=
  D.map ∘ D.map

/-! ## Square-Zero Coderivations and L∞ Algebras

    The condition D² = 0 is the defining equation for L∞ algebras.
    When expanded in terms of brackets, this gives the generalized
    Jacobi identities at each word length. -/

/-- A coderivation is square-zero if D² = 0.

    This means for all x in the coalgebra, (D ∘ D)(x) is the zero element.
    Mathematically: D² = 0 ⟺ all generalized Jacobi identities hold. -/
def Coderivation.isSquareZero (D : Coderivation R V) : Prop :=
  ∀ x : SymCoalg R V, (D.square x).isZero = true

/-- A reduced coderivation is square-zero if D² = 0.

    This is the key condition for L∞ algebras:
    D² = 0 encodes all the generalized Jacobi identities. -/
def ReducedCoderivation.isSquareZero (D : ReducedCoderivation R V) : Prop :=
  ∀ x : ReducedSymCoalg R V, (D.square x).isZero = true

/-- An L∞ algebra structure on V is a degree 1 square-zero coderivation
    on the reduced symmetric coalgebra S⁺(V[1]).

    This is the fundamental theorem of the coalgebraic approach:
    L∞ structures ↔ degree 1 coderivations D with D² = 0 -/
structure LInfinityStructure (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The coderivation on S⁺(V[1]) -/
  D : ReducedCoderivation R (Shift V 1)
  /-- D has degree 1 -/
  degree_one : D.degree = 1
  /-- D² = 0 -/
  square_zero : D.isSquareZero

/-! ## Extracting Brackets -/

/-- The component of a coderivation at word length n.

    For a coderivation D on S⁺(V), this is the map
    D_n : Sym^n(V) → V
    obtained by composing D|_{Sym^n(V)} with projection to V = Sym^1(V). -/
def coderivationComponent (_D : ReducedCoderivation R V) (n : ℕ) (_hn : n ≥ 1) :
    ReducedSymCoalg R V → ReducedSymCoalg R V :=
  _D.componentMap n _hn

theorem coderivationComponent_spec (_D : ReducedCoderivation R V)
    (n : ℕ) (hn : n ≥ 1) (x : ReducedSymCoalg R V) (hx : x.wordLength = n) :
    coderivationComponent _D n hn x = _D.map x :=
  _D.component_spec n hn x hx

theorem coderivationComponent_wordLength_one (_D : ReducedCoderivation R V)
    (n : ℕ) (hn : n ≥ 1) (x : ReducedSymCoalg R V) (hx : x.wordLength = n) :
    (coderivationComponent _D n hn x).wordLength = 1 :=
  _D.component_wordLength_one n hn x hx

/-- The n-th L∞ bracket l_n : V^⊗n → V.

    This is obtained from the coderivation D by:
    1. Taking the component D_n : Sym^n(V[1]) → V[1]
    2. Desuspending to get l_n : V^⊗n → V

    The degree of l_n is 2 - n. -/
def LInfinityStructure.bracket (_L : LInfinityStructure R V) (n : ℕ) (_hn : n ≥ 1) :
    ReducedSymCoalg R (Shift V 1) → ReducedSymCoalg R (Shift V 1) :=
  coderivationComponent _L.D n _hn

theorem LInfinityStructure.bracket_spec (_L : LInfinityStructure R V)
    (n : ℕ) (hn : n ≥ 1) (x : ReducedSymCoalg R (Shift V 1))
    (hx : x.wordLength = n) :
    _L.bracket n hn x = _L.D.map x :=
  coderivationComponent_spec _L.D n hn x hx

theorem LInfinityStructure.bracket_wordLength_one (_L : LInfinityStructure R V)
    (n : ℕ) (hn : n ≥ 1) (x : ReducedSymCoalg R (Shift V 1))
    (hx : x.wordLength = n) :
    (_L.bracket n hn x).wordLength = 1 :=
  coderivationComponent_wordLength_one _L.D n hn x hx

/-! ## Key Properties -/

/-- Word-length-1 square-zero witness extracted from `L.square_zero`. -/
theorem l1_is_differential_witness (L : LInfinityStructure R V) :
    ∀ x : ReducedSymCoalg R (Shift V 1), x.wordLength = 1 →
      (L.D.square x).isZero = true := by
  intro x hx
  exact L.square_zero x

/-- Word-length-2 square-zero witness extracted from `L.square_zero`. -/
theorem l1_derivation_of_l2_witness (L : LInfinityStructure R V) :
    ∀ x : ReducedSymCoalg R (Shift V 1), x.wordLength = 2 →
      (L.D.square x).isZero = true := by
  intro x hx
  exact L.square_zero x

/-- Word-length-`n` square-zero witness extracted from `L.square_zero`. -/
theorem generalized_jacobi_witness (L : LInfinityStructure R V) (n : ℕ) (_hn : n ≥ 1) :
    ∀ x : ReducedSymCoalg R (Shift V 1), x.wordLength = n →
      (L.D.square x).isZero = true := by
  intro x hx
  exact L.square_zero x

/-! ## Special Cases -/

/-- The coderivation vanishes on word length n inputs.

    This means D maps all elements of word length n to zero.
    Formally: for all x ∈ Sym^n(V[1]), we have D(x) = 0. -/
def ReducedCoderivation.vanishesOnWordLength (D : ReducedCoderivation R V) (n : ℕ) : Prop :=
  ∀ x : ReducedSymCoalg R V, x.wordLength = n → (D.map x).isZero = true

theorem ReducedCoderivation.vanishesOnWordLength_iff_componentMap
    (D : ReducedCoderivation R V) (n : ℕ) (hn : n ≥ 1) :
    D.vanishesOnWordLength n ↔
      ∀ x : ReducedSymCoalg R V, x.wordLength = n →
        (D.componentMap n hn x).isZero = true := by
  constructor
  · intro h x hx
    simpa [D.component_spec n hn x hx] using h x hx
  · intro h x hx
    simpa [D.component_spec n hn x hx] using h x hx

def ReducedCoderivation.squareVanishesOnWordLength (D : ReducedCoderivation R V) (n : ℕ) : Prop :=
  ∀ x : ReducedSymCoalg R V, x.wordLength = n → (D.square x).isZero = true

theorem ReducedCoderivation.isSquareZero_iff_squareVanishesOnAllWordLengths
    (D : ReducedCoderivation R V) :
    D.isSquareZero ↔ ∀ n : ℕ, n ≥ 1 → D.squareVanishesOnWordLength n := by
  constructor
  · intro h n hn x hx
    exact h x
  · intro h x
    exact h x.wordLength x.wordLength_pos x rfl

/-- A DGLA (differential graded Lie algebra) is an L∞ algebra
    where l_n = 0 for n ≥ 3.

    The Jacobi identity holds strictly (no higher homotopies).
    Equivalently, the coderivation D vanishes on inputs of word length ≥ 3. -/
def isDGLA (L : LInfinityStructure R V) : Prop :=
  ∀ n : ℕ, n ≥ 3 → L.D.vanishesOnWordLength n

theorem isDGLA_iff_bracketVanishes (L : LInfinityStructure R V) :
    isDGLA L ↔
      ∀ n : ℕ, ∀ hn3 : n ≥ 3,
        ∀ x : ReducedSymCoalg R (Shift V 1), x.wordLength = n →
          (L.bracket n (by omega) x).isZero = true := by
  constructor
  · intro h n hn3 x hx
    have hmap : (L.D.map x).isZero = true := h n hn3 x hx
    have hbr : L.bracket n (by omega) x = L.D.map x := L.bracket_spec n (by omega) x hx
    simpa [hbr] using hmap
  · intro h n hn3 x hx
    have hbr : (L.bracket n (by omega) x).isZero = true := h n hn3 x hx
    have hmap : L.bracket n (by omega) x = L.D.map x := L.bracket_spec n (by omega) x hx
    simpa [hmap] using hbr

/-- A Lie algebra is an L∞ algebra where l₁ = 0 and l_n = 0 for n ≥ 3.

    This means:
    - The differential l₁ vanishes (no differential)
    - Only the binary bracket l₂ is nonzero
    - The Jacobi identity holds strictly -/
def isLieAlgebra (L : LInfinityStructure R V) : Prop :=
  L.D.vanishesOnWordLength 1 ∧ isDGLA L

theorem isLieAlgebra_iff_bracketVanishes (L : LInfinityStructure R V) :
    isLieAlgebra L ↔
      (∀ x : ReducedSymCoalg R (Shift V 1), x.wordLength = 1 →
        (L.bracket 1 (by decide) x).isZero = true) ∧
      (∀ n : ℕ, ∀ hn3 : n ≥ 3,
        ∀ x : ReducedSymCoalg R (Shift V 1), x.wordLength = n →
          (L.bracket n (by omega) x).isZero = true) := by
  constructor
  · intro h
    rcases h with ⟨h1, hdgla⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have hmap : (L.D.map x).isZero = true := h1 x hx
      have hbr : L.bracket 1 (by decide) x = L.D.map x := L.bracket_spec 1 (by decide) x hx
      simpa [hbr] using hmap
    · exact (isDGLA_iff_bracketVanishes L).1 hdgla
  · intro h
    rcases h with ⟨h1, hhigh⟩
    refine ⟨?_, (isDGLA_iff_bracketVanishes L).2 hhigh⟩
    intro x hx
    have hbr : (L.bracket 1 (by decide) x).isZero = true := h1 x hx
    have hmap : L.bracket 1 (by decide) x = L.D.map x := L.bracket_spec 1 (by decide) x hx
    simpa [hmap] using hbr

/-- A strict Lie 2-algebra is an L∞ algebra where l_n = 0 for n ≥ 4.

    This allows a nontrivial Jacobiator l₃ but no higher homotopies. -/
def isLie2Algebra (L : LInfinityStructure R V) : Prop :=
  ∀ n : ℕ, n ≥ 4 → L.D.vanishesOnWordLength n

theorem isLie2Algebra_iff_bracketVanishes (L : LInfinityStructure R V) :
    isLie2Algebra L ↔
      ∀ n : ℕ, ∀ hn4 : n ≥ 4,
        ∀ x : ReducedSymCoalg R (Shift V 1), x.wordLength = n →
          (L.bracket n (by omega) x).isZero = true := by
  constructor
  · intro h n hn4 x hx
    have hmap : (L.D.map x).isZero = true := h n hn4 x hx
    have hbr : L.bracket n (by omega) x = L.D.map x := L.bracket_spec n (by omega) x hx
    simpa [hbr] using hmap
  · intro h n hn4 x hx
    have hbr : (L.bracket n (by omega) x).isZero = true := h n hn4 x hx
    have hmap : L.bracket n (by omega) x = L.D.map x := L.bracket_spec n (by omega) x hx
    simpa [hmap] using hbr

end StringAlgebra.Linfinity
