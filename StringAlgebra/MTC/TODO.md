# MTC Module TODO

## Status: Full module chain compiles; 11 sorrys proved in Phase 1

All files compile. All definitions are proper (no `True := trivial` placeholders,
no `.choose` in definitions, proper `Module.finrank` for fusion coefficients,
proper `scalarOfEndo` for twist values and S-matrix entries).

Phase 1 (easy algebraic wins) is complete. Remaining sorrys require
Drinfeld iso infrastructure (Phase 2), pivotal/spherical proofs (Phase 3-4),
fusion coefficient identities (Phase 5), and advanced properties (Phase 6-8).

## Recent Audit Fixes
- PivotalCategory: added both zigzag identities (pivotalIso_leftDuality,
  pivotalIso_leftDuality_dual) for full monoidal condition on pivotal iso
- Ribbon.lean: pivotal iso now includes twist correction (j = u ∘ θ⁻¹), Drinfeld iso factored out
- FusionCategory.lean: replaced incorrect fusionCoeff_dual_symmetry with correct
  Frobenius reciprocity (fusionCoeff_frobenius) and duality swap (fusionCoeff_dual_swap)
- Semisimple.lean: removed .choose-based multiplicity definition
- Endomorphism.lean: proved scalarOfEndUnit_spec and scalarOfEndSimple_spec
- Bridge/VOAToMTC.lean: fusion_symmetry now proved via BraidedFusionCategory.fusionCoeff_symmetric

## File Structure

```
MTC/
  Pivotal.lean              -- PivotalCategory class (with monoidal conditions)
  Trace.lean                -- leftTrace, rightTrace
  Spherical.lean            -- SphericalCategory, trace, dim
  Ribbon.lean               -- RibbonCategory, twist axioms, Drinfeld iso
  Semisimple.lean           -- SemisimpleCategory, FinitelySemisimple
  FusionCategory.lean       -- FusionCategory class, fusionCoeff
  Endomorphism.lean         -- scalarOfEndo infrastructure (Schur's lemma)
  BraidedFusion.lean        -- BraidedFusionCategory, Müger center
  RibbonFusion.lean         -- RibbonFusionCategory, twistValue, tMatrix
  SMatrix.lean              -- S-matrix (End-valued and k-valued)
  ModularTensorCategory.lean -- MTC class, modular relations
  Verlinde.lean             -- Verlinde formula, TQFT dimensions
  Bridge/
    VOAToMTC.lean           -- Huang's theorem (interface contract)
```

## Priority 1: Infrastructure sorrys (blocking other proofs)

### Pivotal.lean
- [ ] `leftRightDualIso.hom_inv_id` - zigzag proof
- [ ] `leftRightDualIso.inv_hom_id` - zigzag proof

### Ribbon.lean
- [ ] `toPivotalCategory.hom_inv_id` - j = u∘θ⁻¹ is an iso
- [ ] `toPivotalCategory.inv_hom_id` - j = u∘θ⁻¹ is an iso
- [ ] `toPivotalCategory.pivotalIso_naturality` - naturality of j
- [ ] `toPivotalCategory.pivotalIso_leftDuality` - first zigzag for left duality
- [ ] `toPivotalCategory.pivotalIso_leftDuality_dual` - second zigzag for left duality
- [ ] `toSphericalCategory` instance - show ribbon implies spherical
- [x] `twist_unit` - θ_{𝟙} = id (**proved**)

### Endomorphism.lean
- [x] `scalarOfEndo_id` - proved
- [x] `scalarOfEndUnit_spec` - proved
- [x] `scalarOfEndSimple_spec` - proved

## Priority 2: Core theorem sorrys

### FusionCategory.lean
- [x] `dual_simple` - dual of a simple is simple (**proved** via `Simple.of_iso`)
- [x] `fusionCoeff_vacuum_eq/ne` - fusion with vacuum gives δ (**proved** via Schur + `Linear.homCongr`)
- [ ] `fusionCoeff_assoc` - associativity of fusion
- [ ] `fusionCoeff_frobenius` - Frobenius reciprocity N^m_{ij} = N^i_{m,j*}
- [ ] `fusionCoeff_dual_swap` - all duals + swap: N^m_{ij} = N^{m*}_{j*,i*}

### BraidedFusion.lean
- [x] `unit_transparent` - tensor unit is transparent (**proved**)
- [x] `transparent_tensor` - transparent closed under tensor (**proved** via hexagon decomposition)
- [ ] `transparent_dual` - transparent closed under duals
- [x] `fusionCoeff_symmetric` - N^m_{ij} = N^m_{ji} (**proved** via braiding + `LinearEquiv.finrank_eq`)

### RibbonFusion.lean
- [x] `twistValue_vacuum` - θ_0 = 1 (**proved** via `twist_unit` + `scalarOfEndo_id`)
- [x] `monodromy_eq_twist_ratio` - monodromy = twist ratio (**proved**)

### Semisimple.lean
- [x] `hom_simple_eq_zero` - nonzero hom between simples is iso (**proved** via Schur)
- [x] `hom_simple_eq_zero'` - reverse direction (**proved**)

### SMatrix.lean
- [ ] `sMatrixEnd_symmetric` - S_{ij} = S_{ji}
- [ ] `sMatrix_symmetric` - k-valued version
- [ ] `quantumDim_vacuum` - d_0 = 1
- [ ] `quantumDim_fusion` - d_i · d_j = ∑ N^m_{ij} d_m
- [ ] `totalDimSq_ne_zero` - D² ≠ 0
- [ ] `sMatrix_orthogonality` - ∑ S_{im} S_{m*,j} = D² δ_{ij}

### ModularTensorCategory.lean
- [x] `transparent_iff_unit` (backward) - transparent simple ≅ unit (**proved** via braiding naturality)
- [ ] `transparent_iff_unit` (forward) - unit is transparent (follows from `unit_transparent`)
- [ ] `sMatrix_squared` - S² = charge conjugation matrix
- [ ] `modular_relation` - (ST)³ = p₊ · S²

### Verlinde.lean
- [ ] `verlinde_formula` - N^m_{ij} = ∑ S S S / S
- [ ] `sMatrix_diagonalizes_fusion` - S diagonalizes fusion matrices
- [x] `dimTQFTSpace_torus` - dim V(T²) = rank (**proved**)

### Spherical.lean
- [ ] `qdim_dual` - dim(X*) = dim(X)
- [ ] `qdim_unit` - dim(𝟙) = id
- [ ] `qdim_tensor` - dim(X⊗Y) = dim(X) · dim(Y)

## Priority 3: Missing infrastructure

### Frobenius-Perron dimension
- Requires eigenvalue theory / Perron-Frobenius theorem
- Define fusion matrix as `Matrix (Fin n) (Fin n) ℕ`
- FPdim = largest positive eigenvalue
- Could define categorically when spherical structure exists

### HasKernels derivation
- Prove that fusion categories have kernels (semisimple → abelian → has kernels)
- Currently assumed as `[HasKernels C]` where needed

### End(X) ≅ k linear equiv
- Currently use `scalarOfEndo` via `.choose` from `endomorphism_simple_eq_smul_id`
- Could construct explicit `LinearEquiv` from finrank = 1

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
