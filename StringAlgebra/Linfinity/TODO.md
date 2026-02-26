# L∞ Soundness TODO (Dependency-Driven)

Date: 2026-02-26

This file tracks formal soundness debt for `StringAlgebra/Linfinity` under `agent.md` rules:

1. no `axiom` smuggling,
2. no placeholder end-state,
3. no tautological theorem shells,
4. no silent weakening of semantics.

## Current Verified State

1. `lake build StringAlgebra.Linfinity` passes.
2. `StringAlgebra/Linfinity/*.lean` is `sorry`-free.
3. `rg` scans show no `axiom`, `admit`, `Classical.choose`, or placeholder markers in Linfinity Lean files.
4. Recent hardening completed:
   - `Transfer.lean`: removed fabricated transfer outputs and `Classical.choose` inversion; now uses explicit transfer witness packages.
   - `Formality.lean`: removed hardcoded zero graph/quantization outputs; now requires explicit witness data for formality, MC transport, and quantization outputs.
   - `Basic.lean`: removed tautological Jacobi fields; now carries explicit law interfaces.
   - `LInfinityAlgebra.lean`: removed fake twisted/Lie conversion fallbacks and synthetic transfer morphism defaults; transfer morphisms are now explicit witness fields, and core `LInftyMorphism` composition now uses explicit composition data with canonical identity instances.
   - `GradedInfrastructure.lean`: removed `Classical.epsilon` degree selector; degree extraction now requires a homogeneity witness.
   - `Morphisms.lean`: quasi-isomorphism criterion strengthened to degreewise bijectivity; composition now uses explicit `CompositionData`, with derived canonical instances for identity and strict-morphism composition.
   - `Morphisms.lean`: added explicit conversion bridges between bundled `LInftyHom` data and core `LInftyMorphism`, including composition-data transport.
   - `DGLA.lean`: replaced tautological `toLInftyQuasiIso` shell with an explicit `DGLAMorphismLInftyLift` bridge and degreewise linear quasi-isomorphism criterion; added canonical DGLA-to-L∞ lift, DGLA morphism identity/composition, and composition-aware lift transport in the current `LInftyMorphism` interface.
   - `BVAlgebra.lean`: `CyclicLInfty.antibracket` now uses explicit `l2` and cyclicity law instead of a fabricated zero output.
   - `MaurerCartan.lean`: removed hardcoded zero Kuranishi map; Kuranishi local model now requires explicit `KuranishiTheory` data with base-point normalization.
   - `Coderivations.lean`: component extraction no longer aliases the global map; explicit component maps are part of reduced coderivation data.

## Linfinity Dependency Graph

```text
Basic
  ├─> SymmetricTensor
  ├─> SymmetricAlgebra
  └─> SymmetricCoalgebra

SymmetricCoalgebra -> Coderivations -> LInfinityAlgebra -> Morphisms
ChainComplex -> DGLA
LInfinityAlgebra + DGLA + Morphisms -> MaurerCartan
MaurerCartan -> Transfer
DGLA + Morphisms -> Formality
Transfer + SymmetricAlgebra -> BVAlgebra
PlanarTree supports transfer combinatorics
```

## Theorem Flow Toward Deformation Quantization

```text
PolyvectorFieldsDGLA.toDGLAData
+ HochschildCochainsDGLA.toDGLAData
+ HKRMap
+ FormalityMorphism witness

-> kontsevichFormality
-> kontsevichFormality_is_quasi_iso
-> formalityTheorem

+ MCPreservation witness
-> linfty_preserves_mc

+ QuantizationResult witness
-> deformationQuantization
```

## Soundness Audit Matrix (All Linfinity Files)

1. `Basic.lean`: medium risk. Foundational sign/shift infrastructure is stable; Jacobi laws are now explicit external obligations and must be concretized in downstream models.
2. `PlanarTree.lean`: low risk. Structural combinatorics only.
3. `SymmetricTensor.lean`: low-medium risk. Technical dependent-type tensor quotient layer; no proof debt markers.
4. `SymmetricAlgebra.lean`: low risk.
5. `SymmetricCoalgebra.lean`: medium risk. Uses representational `Bool`-style zero tracking; mathematically usable but non-quotiented semantics remain limited.
6. `Coderivations.lean`: medium-high risk. Core interfaces hardened; constructive co-Leibniz/component derivation remains pending.
7. `GradedInfrastructure.lean`: medium-high risk. Extraction interfaces are explicit; internal constructive realization still pending.
8. `ChainComplex.lean`: low risk.
9. `LInfinityAlgebra.lean`: medium-high risk. Core object definitions compile and transfer morphisms are explicit witnesses; semantically nontrivial constructions still depend on supplied transfer/twisting data.
10. `Morphisms.lean`: medium risk. Composition/quasi-isomorphism interfaces are explicit and include canonical strict/identity composition data; full homology-level and homotopy-equation semantics are pending.
11. `DGLA.lean`: medium risk. Tautological bridge shells removed and canonical lift/compose wiring exists; full bracket-sensitive constructive bridge from DGLA structure to higher L∞ components is still pending.
12. `MaurerCartan.lean`: medium risk. MC/gauge/twisting operations are explicit interface data, and Kuranishi outputs are no longer fabricated; canonical constructive formulas and cohomological quotient realization remain pending.
13. `Transfer.lean`: high risk. Fabricated outputs removed, but transferred brackets/structures are witness-driven and not yet constructed from trees internally.
14. `Formality.lean`: high risk. Placeholder outputs removed; theorem-level bridge is witness-driven and awaits constructive graph-weight/operator machinery.
15. `BVAlgebra.lean`: medium risk. No `sorry`; cyclic antibracket interface is explicit, while key BV-to-Gerstenhaber/CME derivations still rely on explicit assumptions pending closure.
16. `TODO.md`: active audit ledger.

## Open Work Packages

### WP1 - Constructive Coderivation Extraction

Targets: `GradedInfrastructure.lean`, `Coderivations.lean`

1. Implement constructive desuspension/extraction from coderivations.
2. Prove component/co-Leibniz compatibility lemmas from internal definitions.
3. Remove remaining witness-only extraction bridges.

### WP2 - Core L∞ Semantics Tightening

Targets: `LInfinityAlgebra.lean`, `Morphisms.lean`

1. Replace fallback/trivial model uses in semantically nontrivial APIs.
2. Internalize concrete higher-component composition formulas so general `CompositionData` can be derived (current derived coverage: identity and strict morphisms).
3. Introduce homology-level quasi-isomorphism interface (or a tightly scoped bridge to chain-level cohomology).
4. Add nontrivial homotopy-equation semantics for `LInftyHomotopy`.

### WP3 - Canonical DGLA -> L∞ Bridge

Target: `DGLA.lean`

1. Construct canonical L∞ model from DGLA differential/bracket data.
2. Align shifted degree conventions explicitly with Schouten/Gerstenhaber packages.
3. Remove dependence on externally supplied `linftyModel` in canonical constructions.

### WP4 - Transfer Internalization

Target: `Transfer.lean`

1. Build transferred brackets from rooted-tree formulas internally.
2. Prove SDR-based transfer identities from those constructions.
3. Strengthen minimal-model uniqueness and formality outputs from witness-level to derived statements.

### WP5 - Formality Internalization

Target: `Formality.lean`

1. Add constructive graph-weight/operator infrastructure.
2. Tie `FormalityMorphism` components to graph systems via explicit equations.
3. Strengthen quantization theorem from witness-driven existence to graph-derived existence.

### WP6 - BV Closure

Target: `BVAlgebra.lean`

1. Derive Gerstenhaber symmetry and CME implications from BV axioms internally.
2. Remove explicit external assumption wrappers once derivations land.

## Anti-Smuggling Gates (Must Hold Per PR)

1. No `axiom`.
2. No `sorry`.
3. No tautological shells (`x = x`, `n = n`) used to stand in for missing semantics.
4. No arbitrary witness extraction (`Classical.choose`/`epsilon`) in core definitions.
5. Any external witness interface must be explicit, minimal, and listed in this TODO with a closure plan.
