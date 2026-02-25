import StringAlgebra.MTC.FusionSpectral

/-!
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Fusion Perron-Frobenius Contracts

Assumption-contract layer for Frobenius-Perron dimensions built on
`FusionSpectral.lean`.

This isolates Perron-Frobenius proof debt (positivity and fusion-character
relations) behind explicit hypotheses, while keeping the candidate API stable.

This layer is intentionally `ℂ`-specialized for now, matching
`FusionSpectral.lean`.
-/

namespace StringAlgebra.MTC

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped NNReal ENNReal

universe v₁

variable {C : Type} [Category.{v₁} C] [MonoidalCategory C]
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [FusionCategory ℂ C]

namespace FusionCategory

/-- Placeholder contract for positivity of spectral-radius FP candidates. -/
class PerronFrobeniusPosAxiom : Prop where
  fpDimCandidate_pos :
    ∀ i : Idx (k := ℂ) (C := C), 0 < fpDimCandidate (C := C) i

/-- Placeholder contract for multiplicativity of spectral-radius FP candidates
against fusion rules. -/
class PerronFrobeniusFusionAxiom : Prop where
  fpDimCandidate_fusion :
    ∀ i j : Idx (k := ℂ) (C := C),
      fpDimCandidate (C := C) i * fpDimCandidate (C := C) j =
        ∑ m : Idx (k := ℂ) (C := C),
          (fusionCoeff (k := ℂ) i j m : ℝ≥0∞) * fpDimCandidate (C := C) m

/-- Placeholder contract for Perron-Frobenius style properties of the
spectral-radius FP candidates. -/
class PerronFrobeniusAxioms : Prop
    extends PerronFrobeniusPosAxiom (C := C),
      PerronFrobeniusFusionAxiom (C := C) where
  /-- Vacuum normalization. -/
  fpDimCandidate_unit :
    fpDimCandidate (C := C) unitIdx = 1

/-- Build full PF assumptions from:
`CanonicalSimpleIndex` + proven vacuum spectral normalization
and the two reduced PF contracts. -/
instance perronFrobeniusAxiomsOfPosFusion
    [HasKernels C]
    [CanonicalSimpleIndex (k := ℂ) (C := C)]
    [PerronFrobeniusPosAxiom (C := C)]
    [PerronFrobeniusFusionAxiom (C := C)] :
    PerronFrobeniusAxioms (C := C) where
  fpDimCandidate_unit := FusionCategory.fpDimCandidate_unit (C := C)
  fpDimCandidate_pos := PerronFrobeniusPosAxiom.fpDimCandidate_pos (C := C)
  fpDimCandidate_fusion := PerronFrobeniusFusionAxiom.fpDimCandidate_fusion (C := C)

theorem fpDimCandidate_pos_of_posAxiom
    [PerronFrobeniusPosAxiom (C := C)]
    (i : Idx (k := ℂ) (C := C)) :
    0 < fpDimCandidate (C := C) i :=
  PerronFrobeniusPosAxiom.fpDimCandidate_pos (C := C) i

theorem fpDimCandidate_fusion_of_fusionAxiom
    [PerronFrobeniusFusionAxiom (C := C)]
    (i j : Idx (k := ℂ) (C := C)) :
    fpDimCandidate (C := C) i * fpDimCandidate (C := C) j =
      ∑ m : Idx (k := ℂ) (C := C),
        (fusionCoeff (k := ℂ) i j m : ℝ≥0∞) * fpDimCandidate (C := C) m :=
  PerronFrobeniusFusionAxiom.fpDimCandidate_fusion (C := C) i j

theorem fpDimCandidate_unit_of_axioms
    [PerronFrobeniusAxioms (C := C)] :
    fpDimCandidate (C := C) unitIdx = 1 :=
  PerronFrobeniusAxioms.fpDimCandidate_unit (C := C)

theorem fpDimCandidate_pos_of_axioms
    [PerronFrobeniusAxioms (C := C)]
    (i : Idx (k := ℂ) (C := C)) :
    0 < fpDimCandidate (C := C) i :=
  fpDimCandidate_pos_of_posAxiom (C := C) i

theorem fpDimCandidate_fusion_of_axioms
    [PerronFrobeniusAxioms (C := C)]
    (i j : Idx (k := ℂ) (C := C)) :
    fpDimCandidate (C := C) i * fpDimCandidate (C := C) j =
      ∑ m : Idx (k := ℂ) (C := C),
        (fusionCoeff (k := ℂ) i j m : ℝ≥0∞) * fpDimCandidate (C := C) m :=
  fpDimCandidate_fusion_of_fusionAxiom (C := C) i j

theorem fpDimCandidateByFin_pos
    [PerronFrobeniusAxioms (C := C)]
    (i : Fin (rank (k := ℂ) (C := C))) :
    0 < fpDimCandidateByFin (C := C) i := by
  simpa [fpDimCandidateByFin, leftFusionSpectralRadiusByFin_eq] using
    (fpDimCandidate_pos_of_axioms (C := C) (idxOfFin (k := ℂ) (C := C) i))

theorem fpDimCandidateByFin_fusion
    [PerronFrobeniusAxioms (C := C)]
    (i j : Fin (rank (k := ℂ) (C := C))) :
    fpDimCandidateByFin (C := C) i * fpDimCandidateByFin (C := C) j =
      ∑ m : Idx (k := ℂ) (C := C),
        (fusionCoeff (k := ℂ)
          (idxOfFin (k := ℂ) (C := C) i)
          (idxOfFin (k := ℂ) (C := C) j)
          m : ℝ≥0∞) *
          fpDimCandidate (C := C) m := by
  simpa [fpDimCandidateByFin, leftFusionSpectralRadiusByFin_eq] using
    (fpDimCandidate_fusion_of_axioms (C := C)
      (idxOfFin (k := ℂ) (C := C) i)
      (idxOfFin (k := ℂ) (C := C) j))

end FusionCategory

end StringAlgebra.MTC
