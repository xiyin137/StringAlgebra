# MTC Module TODO

## Status (2026-02-25): Core infrastructure compiles; 0 sorrys, 15 placeholders behind explicit assumption classes

All files compile via `lake build StringAlgebra.MTC` with no `sorry` warnings.
Definitions are mostly sound and non-placeholder.
`Endomorphism.scalarOfEndo` now uses a canonical linear equivalence
`k ≃ₗ[k] End(X)` (no `.choose` extraction path remains in `StringAlgebra/MTC`).

- Phase 1 (easy algebraic wins): **complete** — 11 sorrys proved
- Phase 2 (duality / Drinfeld infrastructure): **complete** — Drinfeld helpers
  plus `Pivotal.leftRightDualIso` via exact pairing uniqueness
- Phase 3 (pivotal structure from ribbon): **complete** — naturality proved,
  both zigzag identities proved (pivotalIso_leftDuality, pivotalIso_leftDuality_dual)
- Phase 4 (spherical from ribbon): **temporarily assumption-backed** — `toSphericalCategory`
  now depends on explicit `RibbonSphericalAxiom` proof contract
- Phase 5 (deep modular theorems): **temporarily assumption-backed** — hard results moved
  from `sorry` to theorem wrappers backed by explicit assumption classes

## Recent Audit Fixes
- Pivotal.lean: replaced ad-hoc `leftRightDualIso` inverse proofs with
  `pivotalExactPairing` + `leftDualIso`, eliminating 2 sorrys
- PivotalCategory: added both zigzag identities (pivotalIso_leftDuality,
  pivotalIso_leftDuality_dual) for full monoidal condition on pivotal iso
- Ribbon.lean: pivotal iso now includes twist correction (j = u ∘ θ⁻¹), Drinfeld iso factored out
- FusionCategory.lean: replaced incorrect fusionCoeff_dual_symmetry with correct
  Frobenius reciprocity (fusionCoeff_frobenius) and duality swap (fusionCoeff_dual_swap)
- FusionCategory.lean: added optional index-coherence contract
  `CanonicalSimpleIndex` and vacuum normalization lemmas
  (`fusionCoeff_vacuum_iso`, `fusionCoeff_vacuum_kronecker`)
- FusionMatrices.lean: added matrix packaging of fusion coefficients
  (`leftFusionMatrix`, `leftFusionMatrixK`) with matrix-form associativity identities
  (`leftFusionMatrix_mul_assoc_entry`,
  `leftFusionMatrix_mul_eq_linearCombination`,
  `leftFusionMatrixK_mul_eq_linearCombination`)
- FusionMatrices.lean: added canonical `Idx ≃ Fin rank` reindexing
  (`idxEquivFin`, `idxOfFin`, `finOfIdx`) and Fin-indexed matrix APIs
  (`leftFusionMatrixFinNat`, `leftFusionMatrixFin`,
  `leftFusionMatrixByFinNat`, `leftFusionMatrixByFin`)
- FusionMatrices.lean: proved vacuum matrix normalization under canonical indexing
  (`leftFusionMatrix_unit`, `leftFusionMatrixK_unit`,
  `leftFusionMatrixFinNat_unit`, `leftFusionMatrixFin_unit`,
  `leftFusionMatrixByFinNat_unit`, `leftFusionMatrixByFin_unit`)
- FusionMatrices.lean: added braided commutativity theorem
  `leftFusionMatrix_mul_comm` (`N_i N_j = N_j N_i`) under
  `BraidedCategory C` + `FusionRuleAxioms`, then lifted to
  `leftFusionMatrixK_mul_comm`, `leftFusionMatrixFinNat_mul_comm`,
  `leftFusionMatrixFin_mul_comm`, `leftFusionMatrixByFinNat_mul_comm`,
  `leftFusionMatrixByFin_mul_comm`
- FusionMatrices.lean: added symmetry of fusion linear-combination matrices
  in braided setting:
  `leftFusionProductLinearCombination_comm`,
  `leftFusionProductLinearCombinationK_comm`,
  `leftFusionProductLinearCombinationFinNat_comm`,
  `leftFusionProductLinearCombinationFin_comm`
- FusionSpectral.lean: added spectral-radius FP-dimension candidate wrappers
  on Fin-reindexed fusion matrices and vacuum normalization
  (`leftFusionSpectralRadius_unit`, `fpDimCandidate_unit`)
- FusionPF.lean: added explicit Perron-Frobenius assumption contract
  `PerronFrobeniusAxioms` plus wrapper theorems on both `Idx` and `Fin`-indexed
  FPdim candidates
- FusionPF.lean: split PF proof debt into reduced contracts
  `PerronFrobeniusPosAxiom` and `PerronFrobeniusFusionAxiom`, with
  constructor `perronFrobeniusAxiomsOfPosFusion` deriving full
  `PerronFrobeniusAxioms` from reduced contracts + canonical vacuum normalization
- Semisimple.lean: removed .choose-based multiplicity definition
- Endomorphism.lean: proved scalarOfEndUnit_spec and scalarOfEndSimple_spec
- Endomorphism.lean: replaced `.choose`-based `scalarOfEndo` with
  `smulIdLinearEquiv : k ≃ₗ[k] (X ⟶ X)` built from `c ↦ c • 𝟙 X`
- Bridge/VOAToMTC.lean: fusion_symmetry now proved via BraidedFusionCategory.fusionCoeff_symmetric
- Bridge/VOAToMTC.lean: replaced bridge sorrys with explicit external hypotheses
  (`hHuang`, `hTwistRoots`) to keep the VOA interface sound without axiom smuggling
- Bridge/VOAToMTC.lean: added reusable bridge contracts
  (`VOANondegeneracyAssumptions`, `VOATwistRootAssumptions`) and constructors
  `modularTensorCategoryOfHuang` / `modularTensorCategoryOfAssumptions`
- Bridge/Assumptions.lean: extracted bridge contracts into a dedicated module
  and added combined `VOABridgeAssumptions` plus constructor
  `voaBridgeAssumptionsOfComponents`
- Bridge/VOAToMTC.lean + Bridge/Harness.lean: added bundled bridge wrappers
  (`modularTensorCategoryOfBridgeAssumptions`, bundle-level nondegeneracy/twist
  theorems) and integration checks from a single bridge bundle context
- SMatrix.lean: proved `sMatrix_symmetric` from End(𝟙)-symmetry helper and proved
  `quantumDim_vacuum` by reduction to `totalDimSq_ne_zero`
- Spherical/Ribbon/Fusion/SMatrix/Modular/Verlinde: moved placeholder assumptions
  into explicit contract classes (`*Axioms` / `RibbonSphericalAxiom`) and kept
  theorem wrappers stable
- Added `MTC/Assumptions.lean` with bundle classes:
  `FoundationAssumptions`, `ModularAssumptions`, `DevelopmentAssumptions`
  to reduce downstream instance clutter
- Added automatic bundle-constructor instances in `Assumptions.lean`:
  component contracts ⇒ `FoundationAssumptions` / `ModularAssumptions`,
  plus `FoundationAssumptions` + `ModularAssumptions` ⇒ `DevelopmentAssumptions`
- Added `ProofIdeas/AssumptionContracts.md` with a contract-to-wrapper matrix
  for systematic proof-discharge tracking
- Added `MTC/DevelopmentHarness.lean` integration checks proving key
  cross-layer theorems from a single `[DevelopmentAssumptions k C]` context
- Expanded `MTC/DevelopmentHarness.lean` to exercise the full current contract
  surface (qdim, fusion, S-matrix, modular relations, Verlinde diagonalization)
- Added `MTC/Bridge/Harness.lean` integration checks for VOA bridge contracts
  (`VOANondegeneracyAssumptions`, `VOATwistRootAssumptions`)
- Added explicit layer aggregators:
  `FoundationLayer.lean`, `FusionLayer.lean`, `ModularLayer.lean`,
  and rewired top-level `MTC.lean` imports accordingly

## File Structure

```
MTC/
  Pivotal.lean              -- PivotalCategory class (with monoidal conditions)
  Trace.lean                -- leftTrace, rightTrace
  Spherical.lean            -- SphericalCategory, trace, dim
  Ribbon.lean               -- RibbonCategory, twist axioms, Drinfeld iso
  Semisimple.lean           -- SemisimpleCategory, FinitelySemisimple
  FoundationLayer.lean      -- foundation-layer aggregator
  FusionCategory.lean       -- FusionCategory class, fusionCoeff
  FusionMatrices.lean       -- fusion matrices and matrix-form associativity
  FusionSpectral.lean       -- spectral-radius FP-dimension candidates
  FusionPF.lean             -- PF assumption contracts for FPdim candidates
  Endomorphism.lean         -- scalarOfEndo infrastructure (Schur's lemma)
  BraidedFusion.lean        -- BraidedFusionCategory, Müger center
  RibbonFusion.lean         -- RibbonFusionCategory, twistValue, tMatrix
  FusionLayer.lean          -- fusion-layer aggregator
  SMatrix.lean              -- S-matrix (End-valued and k-valued)
  ModularTensorCategory.lean -- MTC class, modular relations
  Verlinde.lean             -- Verlinde formula, TQFT dimensions
  ModularLayer.lean         -- modular-layer aggregator
  Assumptions.lean          -- grouped assumption bundles for development phase
  DevelopmentHarness.lean   -- integration theorems for bundled assumptions
  Bridge/
    Assumptions.lean        -- bridge-local assumption bundles
    VOAToMTC.lean           -- Huang's theorem (interface contract)
    Harness.lean            -- bridge contract integration checks
    Layer.lean              -- bridge-layer aggregator
```

## Priority 1: Infrastructure sorrys (blocking other proofs)

Legend:
- `[x]` proved
- `[~]` available via explicit placeholder assumption class (proof debt isolated, API stable)
- `[ ]` not yet formalized

### Pivotal.lean
- [x] `leftRightDualIso.hom_inv_id` - resolved via `leftDualIso` uniqueness
- [x] `leftRightDualIso.inv_hom_id` - resolved via `leftDualIso` uniqueness

### Ribbon.lean
- [x] `toPivotalCategory.hom_inv_id` - j = u∘θ⁻¹ is an iso (**proved** via rightDualIso.symm)
- [x] `toPivotalCategory.inv_hom_id` - j = u∘θ⁻¹ is an iso (**proved** via rightDualIso.symm)
- [x] `toPivotalCategory.pivotalIso_naturality` - naturality of j (**proved** via drinfeldIsoIso_naturality)
- [x] `toPivotalCategory.pivotalIso_leftDuality` - first zigzag (**proved** via swap pairing zigzag)
- [x] `toPivotalCategory.pivotalIso_leftDuality_dual` - second zigzag (**proved** via swap pairing zigzag)
- [~] `toSphericalCategory` instance - requires `Ribbon.RibbonSphericalAxiom`
- [x] `twist_unit` - θ_{𝟙} = id (**proved**)

### Endomorphism.lean
- [x] `scalarOfEndo_id` - proved
- [x] `scalarOfEndUnit_spec` - proved
- [x] `scalarOfEndSimple_spec` - proved

## Priority 2: Core theorem sorrys

### FusionCategory.lean
- [x] `dual_simple` - dual of a simple is simple (**proved** via `Simple.of_iso`)
- [x] `fusionCoeff_vacuum_eq/ne` - fusion with vacuum gives δ (**proved** via Schur + `Linear.homCongr`)
- [~] `fusionCoeff_assoc` - via `FusionCategory.FusionRuleAxioms`
- [~] `fusionCoeff_frobenius` - via `FusionCategory.FusionRuleAxioms`
- [~] `fusionCoeff_dual_swap` - via `FusionCategory.FusionRuleAxioms`

### BraidedFusion.lean
- [x] `unit_transparent` - tensor unit is transparent (**proved**)
- [x] `transparent_tensor` - transparent closed under tensor (**proved** via hexagon decomposition)
- [x] `transparent_dual` - transparent closed under duals (**proved** via hexagon + transparency transfer)
- [x] `fusionCoeff_symmetric` - N^m_{ij} = N^m_{ji} (**proved** via braiding + `LinearEquiv.finrank_eq`)

### RibbonFusion.lean
- [x] `twistValue_vacuum` - θ_0 = 1 (**proved** via `twist_unit` + `scalarOfEndo_id`)
- [x] `monodromy_eq_twist_ratio` - monodromy = twist ratio (**proved**)

### Semisimple.lean
- [x] `hom_simple_eq_zero` - nonzero hom between simples is iso (**proved** via Schur)
- [x] `hom_simple_eq_zero'` - reverse direction (**proved**)

### SMatrix.lean
- [~] `sMatrixEnd_symmetric` - via `SMatrix.SMatrixAxioms`
- [x] `sMatrix_symmetric` - k-valued version (reduced to End(𝟙)-symmetry helper)
- [x] `quantumDim_vacuum` - d_0 = 1 (reduced to `totalDimSq_ne_zero`)
- [~] `quantumDim_fusion` - via `SMatrix.SMatrixAxioms`
- [~] `totalDimSq_ne_zero` - via `SMatrix.SMatrixAxioms`
- [~] `sMatrix_orthogonality` - via `SMatrix.SMatrixAxioms`

### ModularTensorCategory.lean
- [x] `transparent_iff_unit` (backward) - transparent simple ≅ unit (**proved** via braiding naturality)
- [x] `transparent_iff_unit` (forward) - unit is transparent (follows from `unit_transparent`)
- [~] `sMatrix_squared` - via `ModularTensorCategory.ModularDataAxioms`
- [~] `modular_relation` - via `ModularTensorCategory.ModularDataAxioms`

### Verlinde.lean
- [~] `verlinde_formula` - via `Verlinde.VerlindeAxioms`
- [~] `sMatrix_diagonalizes_fusion` - via `Verlinde.VerlindeAxioms`
- [x] `dimTQFTSpace_torus` - dim V(T²) = rank (**proved**)

### Spherical.lean
- [~] `qdim_dual` - via `Spherical.SphericalDimAxioms`
- [~] `qdim_unit` - via `Spherical.SphericalDimAxioms`
- [~] `qdim_tensor` - via `Spherical.SphericalDimAxioms`

## Assumption Contract Inventory (2026-02-25)

The following classes currently carry the unresolved proof obligations:

- `Spherical.SphericalDimAxioms` (3 obligations)
- `Ribbon.RibbonSphericalAxiom` (1 obligation)
- `FusionCategory.FusionRuleAxioms` (3 obligations)
- `SMatrix.SMatrixAxioms` (4 obligations)
- `ModularTensorCategory.ModularDataAxioms` (2 obligations)
- `Verlinde.VerlindeAxioms` (2 obligations)
- `FusionCategory.PerronFrobeniusPosAxiom` (1 obligation)
- `FusionCategory.PerronFrobeniusFusionAxiom` (1 obligation)

Bundle convenience classes:
- `FoundationAssumptions`
- `ModularAssumptions`
- `DevelopmentAssumptions`

Bundle constructor instances:
- `foundationAssumptionsOfComponents`
- `modularAssumptionsOfComponents`
- `developmentAssumptionsOfBundles`

Optional coherence assumptions (not proof-debt placeholders):
- `FusionCategory.CanonicalSimpleIndex` for strict `Idx`-level
  isoclass uniqueness (`Nonempty (X_i ≅ X_j) ↔ i = j`)

### Bridge/VOAToMTC.lean
- [x] `huang_nondegeneracy` - now takes explicit Huang nondegeneracy hypothesis argument
- [x] `twist_roots_of_unity` - now takes explicit twist-root hypothesis argument
- [x] Added bridge assumption classes + bundled theorem wrappers:
  `huang_nondegeneracy_of_assumptions`, `twist_roots_of_unity_of_assumptions`
- [x] Added modularity constructors:
  `modularTensorCategoryOfHuang`, `modularTensorCategoryOfAssumptions`
- [x] Added combined bridge bundle wrappers:
  `huang_nondegeneracy_of_bridge_assumptions`,
  `twist_roots_of_unity_of_bundle`,
  `modularTensorCategoryOfBridgeAssumptions`

### Bridge/Assumptions.lean
- [x] Added combined bridge bundle class:
  `VOABridgeAssumptions`
- [x] Added bundle constructor instance:
  `voaBridgeAssumptionsOfComponents`

## Priority 3: Missing infrastructure

### Frobenius-Perron dimension
- Spectral-radius wrappers are now available in `FusionSpectral.lean`:
  `leftFusionSpectralRadius`, `leftFusionSpectralRadiusByFin`,
  `fpDimCandidate`, `fpDimCandidateByFin`
- Vacuum normalization proved under canonical indexing:
  `leftFusionSpectralRadius_unit = 1`, `fpDimCandidate_unit = 1`
- PF theorem wrappers are staged in `FusionPF.lean` via
  `PerronFrobeniusAxioms` (`fpDimCandidate_unit_of_axioms`,
  `fpDimCandidate_pos_of_axioms`, `fpDimCandidate_fusion_of_axioms`)
- Reduced PF contracts now isolate the remaining debt:
  `PerronFrobeniusPosAxiom`, `PerronFrobeniusFusionAxiom`
- Next theorem layer:
  1. Perron-Frobenius positivity/existence for each `leftFusionMatrixByFin i`
  2. Uniqueness of positive eigenvector up to scaling
  3. Identification `fpDim =` Perron root (not just generic spectral radius)

### HasKernels derivation
- Prove that fusion categories have kernels (semisimple → abelian → has kernels)
- Currently assumed as `[HasKernels C]` where needed

### End(X) ≅ k linear equiv
- **implemented** in `Endomorphism.lean` via:
  - `smulIdLinearMap`
  - `smulIdLinearMap_injective`
  - `smulIdLinearMap_finrank_eq`
  - `smulIdLinearEquiv`

## Architectural Restructuring Roadmap

1. Layer the module graph explicitly:
   - `MTC/Foundation/` (duality, pivotal, trace, scalar extraction, semisimple)
   - `MTC/Fusion/` (fusion coeffs, braided/ribbon fusion)
   - `MTC/Modular/` (S-matrix, modular relations, Verlinde)
2. Move heavy proof infrastructure out of statement files:
   - e.g. split long private lemmas from `Ribbon.lean` into
     `MTC/Foundation/RibbonLemmas.lean`
3. Keep bridge assumptions localized: **completed**
   - introduce dedicated hypothesis records in `MTC/Bridge/` so external
     theorem assumptions are explicit and auditable
4. Split long theorem statements from proof bodies where helpful:
   - keep short API files and move long scripts into sibling `.../Proofs/*.lean`
5. Factor FPdim development into explicit tiers:
   - `FusionMatrices` (algebraic packaging, no analysis)
   - `FusionSpectral` (spectral-radius interface)
   - future `FusionPF` (Perron-Frobenius existence/uniqueness proofs)

## Priority 4: Examples (Phase 6)
- [ ] Examples/Ising.lean - 3 objects {1, σ, ψ}
- [ ] Examples/SUTwoLevel.lean - SU(2)_k with k+1 simples
- [ ] Examples/VecG.lean - Rep(G) and Drinfeld center Z(Rep(G))

## Notes

- All definitions require `[IsAlgClosed k]` and `[HasKernels C]` for
  k-valued S-matrix/T-matrix (via Schur's lemma)
- End(𝟙)-valued S-matrix (`sMatrixEnd`) works without these assumptions
- The `fusionCoeff` definition uses `Module.finrank k (X_i ⊗ X_j ⟶ X_m)`
  which is the proper mathematical definition
