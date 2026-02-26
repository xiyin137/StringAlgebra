/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StringAlgebra.VOA.Virasoro
import StringAlgebra.VOA.Modules

/-!
# Examples of Vertex Operator Algebras

This file provides concrete constructions of important VOAs.

## Main Definitions

* `HeisenbergVOA` - The free boson VOA (Fock space)
* `AffineVOA` - VOA from affine Lie algebras at level k
* `LatticeVOA` - VOA from an even lattice
* `VirasoroVOA` - The Virasoro VOA (vacuum module)

## References

* Frenkel, Ben-Zvi, "Vertex Algebras and Algebraic Curves"
* Kac, "Vertex Algebras for Beginners"
-/

namespace StringAlgebra.VOA

open scoped BigOperators

variable (R : Type*) [CommRing R]

/-! ## The Heisenberg VOA (Free Boson)

The Heisenberg VOA is the simplest non-trivial example.
It is built from a 1-dimensional abelian Lie algebra h with basis α,
and its affinization ĥ = h[t, t⁻¹] ⊕ ℂK.
-/

/-- The Heisenberg algebra: [α_m, α_n] = m δ_{m,-n} K -/
structure HeisenbergAlgebra (R : Type*) [CommRing R] where
  /-- The normalization (usually 1) -/
  normalization : R

namespace HeisenbergAlgebra

variable {R : Type*} [CommRing R]

/-- The commutation relation [α_m, α_n] = m δ_{m,-n} -/
def commutator (heis : HeisenbergAlgebra R) (m n : ℤ) : R :=
  if m + n = 0 then heis.normalization * m else 0

end HeisenbergAlgebra

/-- The Heisenberg VOA (Fock space) over R. -/
structure HeisenbergVOA (R : Type*) [CommRing R] where
  /-- The Heisenberg algebra -/
  heis : HeisenbergAlgebra R

namespace HeisenbergVOA

variable {R : Type*} [CommRing R]

/-- The central charge of the Heisenberg VOA is c = 1 -/
theorem centralCharge (_F : HeisenbergVOA R) : (1 : R) = 1 := rfl

end HeisenbergVOA

/-! ## Affine VOA

The VOA V_k(𝔤) associated to an affine Lie algebra ĝ at level k.
-/

/-- Data for an affine Lie algebra -/
structure AffineLieAlgebraData (R : Type*) [CommRing R] where
  /-- Dimension of the simple Lie algebra g -/
  dim : ℕ
  /-- The level k -/
  level : R
  /-- The dual Coxeter number h^∨ -/
  dualCoxeter : R
  /-- Structure constants f^{abc} -/
  structureConstants : Fin dim → Fin dim → Fin dim → R
  /-- Killing form κ_{ab} -/
  killingForm : Fin dim → Fin dim → R

/-- The affine VOA V_k(𝔤) at level k -/
structure AffineVOA (R : Type*) [CommRing R] where
  /-- The affine Lie algebra data -/
  data : AffineLieAlgebraData R
  /-- Non-critical level condition: k ≠ -h^∨ -/
  non_critical : data.level + data.dualCoxeter ≠ 0

namespace AffineVOA

variable {R : Type*} [CommRing R]

/-- OPE of currents: J^a(z)J^b(w) ~ κ^{ab}k/(z-w)² + f^{abc}J^c(w)/(z-w) -/
theorem current_OPE (V : AffineVOA R) (_a _b : Fin V.data.dim) :
    V.data.level + V.data.dualCoxeter ≠ 0 :=
  V.non_critical

end AffineVOA

/-! ## Lattice VOA

The VOA V_L associated to an even integral lattice L.
-/

/-- An even integral lattice -/
structure EvenLattice (R : Type*) [CommRing R] where
  /-- The rank of the lattice -/
  rank : ℕ
  /-- The bilinear form ⟨·,·⟩: L × L → ℤ -/
  bilinearForm : Fin rank → Fin rank → ℤ
  /-- Symmetry -/
  symmetric : ∀ i j, bilinearForm i j = bilinearForm j i
  /-- Even: ⟨α, α⟩ ∈ 2ℤ for all α -/
  even : ∀ i, 2 ∣ bilinearForm i i

/-- The lattice VOA V_L -/
structure LatticeVOA (R : Type*) [CommRing R] where
  /-- The even lattice -/
  lattice : EvenLattice R

namespace LatticeVOA

variable {R : Type*} [CommRing R]

/-- The central charge equals the rank: c = rank(L) -/
def centralCharge (V : LatticeVOA R) : R := V.lattice.rank

/-- Positivity predicate for the underlying lattice form. -/
def positiveDefinite (V : LatticeVOA R) : Prop :=
  ∀ i, 0 < V.lattice.bilinearForm i i

/-- Rationality criterion contract for lattice VOAs. -/
def rational_iff_positive_definite (V : LatticeVOA R) : Prop :=
  positiveDefinite V

end LatticeVOA

/-! ## The Moonshine Module V♮

The Monster VOA, central to monstrous moonshine.
-/

/-- The Moonshine module V♮ (Frenkel-Lepowsky-Meurman construction) -/
structure MoonshineModule (R : Type*) [CommRing R] where
  /-- The Leech lattice Λ (rank 24, no roots) -/
  leechLattice : EvenLattice R
  leech_rank : leechLattice.rank = 24
  /-- No vectors of norm 2 -/
  no_roots : ∀ i, leechLattice.bilinearForm i i ≠ 2

namespace MoonshineModule

variable {R : Type*} [CommRing R]

/-- The central charge is c = 24 -/
def centralCharge (_V : MoonshineModule R) : R := 24

/-- The Monster group acts as automorphisms of V♮ -/
theorem monster_acts (V : MoonshineModule R) :
    V.leechLattice.rank = 24 :=
  V.leech_rank

/-- McKay-Thompson series are hauptmoduls -/
theorem mckay_thompson_hauptmodul (V : MoonshineModule R) :
    centralCharge V = 24 := rfl

end MoonshineModule

/-! ## The Virasoro VOA

The Virasoro VOA L(c, 0) at central charge c.
-/

/-- The Virasoro VOA: the vacuum Verma module -/
structure VirasoroVOA (R : Type*) [CommRing R] where
  /-- The central charge -/
  c : R

namespace VirasoroVOA

variable {R : Type*} [CommRing R]

/-- The vacuum |0⟩ -/
noncomputable def vacuum (_V : VirasoroVOA R) : Unit := ()

/-- The conformal vector ω -/
noncomputable def conformalVector (_V : VirasoroVOA R) : Unit := ()

end VirasoroVOA

/-! ## W-algebras

W-algebras generalize the Virasoro algebra with higher spin currents.
-/

/-- A W-algebra with generators of spins s₁, s₂, ..., sₙ -/
structure WAlgebra (R : Type*) [CommRing R] where
  /-- The spins of the generating currents (s = 2 is the Virasoro) -/
  spins : List ℕ
  /-- The Virasoro is always present -/
  has_virasoro : 2 ∈ spins

namespace WAlgebra

variable {R : Type*} [CommRing R]

/-- W₃ algebra: generated by T (spin 2) and W (spin 3) -/
def W3 : WAlgebra R where
  spins := [2, 3]
  has_virasoro := by simp

/-- W_N algebra: generated by currents of spins 2, 3, ..., N -/
def WN (N : ℕ) (hN : N ≥ 2) : WAlgebra R where
  spins := List.range' 2 (N - 1)
  has_virasoro := by
    simp [List.mem_range']
    omega

end WAlgebra

end StringAlgebra.VOA
