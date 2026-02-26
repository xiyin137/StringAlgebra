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
   - `Transfer.lean`: tightened `minimal_model_unique` output from bare `Nonempty` to an explicit quasi-isomorphic comparison witness that is returned identically (no hidden witness substitution).
   - `Transfer.lean`: added unpacked formality interface (`isFormal_unpacked`/`isFormal_of_unpacked`/`isFormal_iff_unpacked`) exposing explicit minimal-model and quasi-isomorphism data from/to `isFormal`.
   - `Transfer.lean`: added canonical accessor morphisms (`minimalModelMorphism`, `formalityMorphism`) with explicit quasi-isomorphism theorems and routed `minimal_model_exists` through these accessors.
   - `Transfer.lean`: strengthened `TransferResult` with explicit linear-consistency constraint (`inclusion_linear`) tying the lifted inclusion's arity-1 component to the underlying SDR inclusion map; added exported theorem `transferInclusion_linear`.
   - `Transfer.lean`: strengthened both `MinimalModelResult` and `FormalityResult` with explicit linear-part fields tied to the arity-1 quasi-isomorphism components (`linear_spec`), and added derived degreewise bijectivity theorems (`minimalModelLinear_isBijective`, `formalityLinear_isBijective`).
   - `Transfer.lean`: added `transferInclusionLinear_isBijective`, deriving degreewise bijectivity of `data.incl` from `TransferResult.inclusion_isQuasiIso` via the exported arity-1 coherence theorem `transferInclusion_linear`.
   - `Transfer.lean`: added canonical accessor linear-bridge theorems (`minimalModelMorphism_linear_isBijective`, `formalityMorphism_linear_isBijective`) and simp equalities (`minimalModelMorphism_linear_eq`, `formalityMorphism_linear_eq`), so package-level linear bijectivity now explicitly factors through canonical accessor morphisms.
   - `Transfer.lean`: strengthened extraction-level existence theorems with explicit linear bijectivity packaging (`minimal_model_exists_with_linear_bijectivity`, `isFormal_unpacked_with_linear_bijectivity`, `isFormal_exists_formalityLinear_isBijective`), so witness unpacking now preserves explicit arity-1 isomorphism data.
   - `Formality.lean`: removed hardcoded zero graph/quantization outputs; now requires explicit witness data for formality, MC transport, and quantization outputs.
   - `Formality.lean`: strengthened MC transport to explicit element-level output (`linfty_preserves_mc`) with an existence wrapper lemma, and added reflexive/symmetric/transitive gauge-equivalence infrastructure with a `Setoid` instance on star products.
   - `Formality.lean`: added explicit star-product gauge-class quotient interface (`StarProductGaugeClass`, projection, and exact equality↔gauge-equivalence bridge lemmas).
   - `Formality.lean`: added classification bridge theorem on quotient classes (`starProductClassification_toGaugeClass`) to consume assumptions directly at the `toGaugeClass` level.
   - `Formality.lean`: gauge transformations are now identity-normalized (`T₀ = 0`) and composition/symmetry preserve and combine explicit transformation data instead of discarding components; the local `ConfigurationSpace` model also enforces collision-freeness via injectivity.
   - `Formality.lean`: strengthened `KontsevichGraph.ordering` by replacing the tautological ground-target branch with an explicit finite-index bound (`j.val < groundVertices`).
   - `Formality.lean`: strengthened `FormalityComponent` with explicit degree-consistency proof (`degree_spec`) and exported simp lemma (`FormalityComponent.degree_eq`), eliminating unconstrained arity/degree metadata.
   - `Formality.lean`: strengthened `FormalityMorphism` with explicit component consistency against the bundled `LInftyHom` at every arity (`component_spec`) and explicit arity-1 HKR normalization (`linear_hkr_spec`); added the derived theorem `FormalityMorphism.linearIsHKR_of_specs`.
   - `Formality.lean`: strengthened `MCPreservation` with element-level arity-1 linear compatibility (`map_element_linear`) and added exported theorem `linfty_preserves_mc_element`.
   - `Formality.lean`: aligned theorem naming/documentation with witness-level semantics (`hkr_chain_equation`, `canonicalCommutator_firstOrder`, `poissonSigmaModel_witness`) while retaining compatibility aliases for historical names.
   - `Basic.lean`: removed tautological Jacobi fields; now carries explicit law interfaces.
   - `LInfinityAlgebra.lean`: removed fake twisted/Lie conversion fallbacks and synthetic transfer morphism defaults; transfer morphisms are now explicit witness fields, and core `LInftyMorphism` composition now uses explicit composition data with canonical identity instances.
   - `LInfinityAlgebra.lean`: homotopy-transfer witness package now includes explicit quasi-isomorphism certification of the lifted inclusion, with derived transfer linear/quasi-iso lemmas.
   - `LInfinityAlgebra.lean`: core `LInftyMorphism` now enforces arity-0 normalization via `higher_zero`; canonical constructors and bridge adapters (`Morphisms.lean`, `DGLA.lean`) are updated accordingly.
   - `SymmetricCoalgebra.lean`: strengthened `SymPower` with explicit total-degree consistency proof (`totalDegree_eq`) and exported simp lemma (`SymPower.totalDegree_eq_sum`), eliminating unconstrained stored total-degree metadata.
   - `SymmetricCoalgebra.lean`: strengthened `SymPower` zero-marker semantics with explicit degree-vanishing constraint (`isZero_degrees_zero`) and derived theorems (`degrees_eq_zero_of_isZero`, `totalDegree_eq_zero_of_isZero`), preventing inconsistent zero-flag payloads.
   - `SymmetricCoalgebra.lean`: strengthened `SymCoalg` zero-marker semantics with explicit factor-degree vanishing constraint (`isZero_factorDegrees_zero`) and derived theorems (`factorDegrees_eq_zero_of_isZero`, `degree_eq_zero_of_isZero`).
   - `SymmetricCoalgebra.lean`: strengthened `ReducedSymCoalg` zero-marker semantics with explicit word-length normalization (`isZero_wordLength_one`) and derived theorem (`wordLength_eq_one_of_isZero`), matching all current reduced-zero constructors/usages.
   - `GradedInfrastructure.lean`: removed `Classical.epsilon` degree selector; degree extraction now requires a homogeneity witness.
   - `GradedInfrastructure.lean`: strengthened `ReducedSymCoalgElem` with explicit total-degree consistency proof (`totalDegree_eq`) and exported simp lemma (`ReducedSymCoalgElem.totalDegree_eq_sum`), eliminating unconstrained stored total-degree metadata.
   - `GradedInfrastructure.lean`: strengthened coderivation/L∞ extracted-bracket witness bundles with explicit unary consistency constraints (arity-1 multilinear component must match provided linear differential/bracket views), preventing silent drift between parallel unary interfaces; added explicit exported bridge theorem (`Coderivation.differential_spec_from_bracket`) so downstream proofs consume this consistency directly.
   - `Morphisms.lean`: quasi-isomorphism criterion strengthened to degreewise bijectivity; composition now uses explicit `CompositionData`, with derived canonical instances for identity and strict-morphism composition.
   - `Morphisms.lean`: added explicit conversion bridges between bundled `LInftyHom` data and core `LInftyMorphism`, including composition-data transport.
   - `Morphisms.lean`: strengthened `MorphismComponent` with explicit degree-consistency proof (`degree_spec`) and exported simp lemma (`MorphismComponent.degree_eq`), preventing silent arity/degree drift in component records.
   - `Morphisms.lean`: `LInftyHomotopy` now carries an explicit first-order linear homotopy equation (`linearDelta`, `linear_spec`) and derived symmetry/transitivity constructors.
   - `Morphisms.lean`: homotopy now exposes an `Equivalence` theorem and a canonical `Setoid` instance on `LInftyHom`.
   - `Morphisms.lean`: added data-level `LInftyHomotopy.refl/symm/trans` constructors and rewired relation lemmas to these canonical constructors.
   - `Morphisms.lean`: added explicit homotopy-class quotient interface (`LInftyHomotopyClass`, projection, and exact equality↔homotopy bridge lemmas).
   - `Morphisms.lean`: strengthened `LInftyHom` ↔ core `LInftyMorphism` bridges with explicit higher-component round-trip theorems (including arity-0 normalization and all `n ≥ 1` component recovery), so conversion layers are data-preserving beyond the linear part.
   - `DGLA.lean`: replaced tautological `toLInftyQuasiIso` shell with an explicit `DGLAMorphismLInftyLift` bridge and degreewise linear quasi-isomorphism criterion; added canonical DGLA-to-L∞ lift, DGLA morphism identity/composition, and composition-aware lift transport in the current `LInftyMorphism` interface.
   - `DGLA.lean`: added converse/iff theorems for the canonical DGLA→L∞ quasi-isomorphism criterion (`isLinearQuasiIso ↔ toLInftyMorphism.isQuasiIso`) and its canonical-lift restatement.
   - `DGLA.lean`: strengthened `DGLAMorphismLInftyLift` witnesses with explicit unary-higher agreement and non-unary higher vanishing constraints, so canonical-lift packages cannot hide arbitrary higher components.
   - `DGLA.lean`: added explicit-lift quasi-isomorphism converse/iff theorems (`isLinearQuasiIso_of_toLInftyQuasiIso`, `toLInftyQuasiIso_iff`) and a derived linear-vs-unary coherence theorem (`DGLAMorphismLInftyLift.linear_eq_higher_one`) for arbitrary witness packages, not only the canonical lift.
   - `BVAlgebra.lean`: `CyclicLInfty.antibracket` now uses explicit `l2` and cyclicity law instead of a fabricated zero output.
   - `BVAlgebra.lean`: renamed the `Δ`-closure witness field to `triple_delta_zero` and aligned documentation with the actual encoded condition (no implicit claim of full seven-term second-order identity).
   - `MaurerCartan.lean`: removed hardcoded zero Kuranishi map; Kuranishi local model now requires explicit `KuranishiTheory` data with base-point normalization.
   - `MaurerCartan.lean`: gauge equivalence now has explicit reflexive/symmetric/transitive lemmas and a canonical `Setoid`; smoothness now exposes an explicit moduli-point constructor (`smoothPoint_when_unobstructed`) with a `Nonempty` wrapper theorem.
   - `MaurerCartan.lean`: added explicit MC-to-moduli projection with exact characterization `a.toModuli = b.toModuli ↔ GaugeEquivalent T a b`.
   - `MaurerCartan.lean`: strengthened `MCTheory` by linking gauge action to gauge-equivalence data (`gaugeAction_zero`, `gaugeAction_sound`) and added exported bridge theorems (`gaugeAction_zero`, `gaugeAction_gaugeEquivalent`).
   - `MaurerCartan.lean`: strengthened `MCTheory` with MC-preservation under gauge action (`gaugeAction_preserves_curvature_zero`), added theorem-level bridge (`gaugeAction_preservesMC`), and added canonical gauge action on MC elements (`MCElement.gaugeAct`) with neutral-action theorem (`MCElement.gaugeAct_zero`).
   - `MaurerCartan.lean`: added explicit compatibility of the canonical MC-element gauge action with gauge/moduli quotients (`MCElement.gaugeAct_gaugeEquivalent`, `MCElement.toModuli_eq_gaugeAct`).
   - `MaurerCartan.lean`: aligned gauge/twisting/tangent-obstruction documentation and theorem naming with witness-level semantics (`twisted_diff_sq_zero_witness` plus compatibility alias), avoiding unencoded gauge-flow/cohomology claims.
   - `Coderivations.lean`: strengthened `ReducedCoderivation` with explicit `component_spec` consistency (on word-length-`n` inputs, `componentMap n` agrees with `map`) and explicit unary-output shape (`component_wordLength_one`), added `coderivationComponent_spec`/`coderivationComponent_wordLength_one`/`LInfinityStructure.bracket_spec`/`LInfinityStructure.bracket_wordLength_one`, exposed vanishing equivalence (`vanishesOnWordLength_iff_componentMap`) to keep map-vs-component formulations synchronized, added an explicit square-zero decomposition interface by word length (`squareVanishesOnWordLength`, `isSquareZero_iff_squareVanishesOnAllWordLengths`), and added bracket-level characterizations for `isDGLA`/`isLieAlgebra`/`isLie2Algebra` with witness-level naming plus compatibility aliases for historical theorem names.
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

TransferResult.inclusion_isQuasiIso
+ transferInclusion_linear
-> transferInclusionLinear_isBijective

MinimalModelResult.quasiIso_property
+ minimalModelMorphism_linear_eq
-> minimalModelMorphism_linear_isBijective
-> minimalModelLinear_isBijective

FormalityResult.quasiIso_property
+ formalityMorphism_linear_eq
-> formalityMorphism_linear_isBijective
-> formalityLinear_isBijective

MinimalModelResult + canonical accessor bridges
-> minimal_model_exists_with_linear_bijectivity

isFormal
-> isFormal_unpacked_with_linear_bijectivity
-> isFormal_exists_formalityLinear_isBijective

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
5. `SymmetricCoalgebra.lean`: medium risk. Uses representational `Bool`-style zero tracking; `SymPower`, `SymCoalg`, and `ReducedSymCoalg` now enforce stored degree consistency plus explicit zero-marker normalization constraints, but non-quotiented semantics remain limited.
6. `Coderivations.lean`: medium-high risk. Core interfaces are further hardened with explicit map/component consistency, unary-output shape constraints for components/brackets, synchronized vanishing formulations, square-zero decomposition by word length, and bracket-level characterization lemmas for DGLA/Lie/Lie2 truncation; constructive co-Leibniz/component derivation remains pending.
7. `GradedInfrastructure.lean`: medium-high risk. Extraction interfaces are explicit, enforce unary consistency across multilinear/linear extracted data, and now enforce stored total-degree consistency for reduced coalgebra elements while exposing theorem-level unary bridge access; internal constructive realization is still pending.
8. `ChainComplex.lean`: low risk.
9. `LInfinityAlgebra.lean`: medium risk. Core object definitions compile, morphisms now enforce arity-0 normalization and transfer morphisms carry explicit linear/quasi-isomorphism certification in the homotopy-transfer interface; semantically nontrivial constructions still depend on supplied transfer/twisting data.
10. `Morphisms.lean`: medium risk. Composition/quasi-isomorphism interfaces are explicit and include canonical strict/identity composition data, component records now enforce arity-indexed degree consistency, bridge conversions now have explicit higher-component round-trip guarantees, and first-order homotopy-equation semantics exist with explicit symmetry/transitivity constructors; higher coherence equations and homology-level semantics remain pending.
11. `DGLA.lean`: medium risk. Tautological bridge shells removed, canonical lift/compose wiring has bidirectional quasi-isomorphism criterion equivalence, arbitrary explicit lift packages now also carry bidirectional quasi-isomorphism criteria plus derived linear-vs-unary coherence, and lift witnesses explicitly constrain higher-component shape; full bracket-sensitive constructive bridge from DGLA structure to higher L∞ components is still pending.
12. `MaurerCartan.lean`: medium risk. MC/gauge/twisting operations are explicit interface data with witness-aligned theorem/docs, gauge action is explicitly tied to gauge-equivalence and MC preservation (including canonical action on `MCElement` and moduli-class invariance under that action), and Kuranishi outputs are no longer fabricated; canonical constructive formulas and cohomological quotient realization remain pending.
13. `Transfer.lean`: high risk. Fabricated outputs removed, witness-return theorems now preserve supplied comparison data explicitly, lifted transfer inclusions carry explicit arity-1 agreement with SDR inclusion maps, and minimal/formality witness packages now expose linear quasi-isomorphism views tied to arity-1 components; transferred brackets/structures are still witness-driven and not yet constructed from trees internally.
14. `Formality.lean`: high risk. Placeholder outputs removed; `KontsevichGraph.ordering` now records explicit ground-target bounds (no tautological ground branch), formality components now enforce arity-indexed degree consistency, `FormalityMorphism` enforces arity-wise component consistency with bundled L∞ data and explicit HKR normalization at arity 1, MC-preservation data now enforces element-level arity-1 linear compatibility with the chosen L∞ morphism, gauge-equivalence/gauge-class interfaces are explicit, theorem naming now reflects witness-level semantics, and gauge-transformation normalization/composition are data-preserving, while the theorem-level bridge still remains witness-driven and awaits constructive graph-weight/operator machinery.
15. `BVAlgebra.lean`: medium risk. No `sorry`; cyclic antibracket interface is explicit, `Δ`-closure is tracked via an explicit trilinear vanishing witness (`triple_delta_zero`), and key BV-to-Gerstenhaber/CME derivations still rely on explicit assumptions pending closure.
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
4. Extend `LInftyHomotopy` from first-order linear semantics to higher-component coherence equations matching full L∞ homotopy identities.

### WP3 - Canonical DGLA -> L∞ Bridge

Target: `DGLA.lean`

1. Construct canonical L∞ model from DGLA differential/bracket data.
2. Align shifted degree conventions explicitly with Schouten/Gerstenhaber packages.
3. Remove dependence on externally supplied `linftyModel` in canonical constructions.

### WP4 - Transfer Internalization

Target: `Transfer.lean`

1. Build transferred brackets from rooted-tree formulas internally.
2. Prove SDR-based transfer identities from those constructions.
   Partial closure: arity-1 agreement between lifted inclusion and SDR inclusion is now encoded in `TransferResult`.
3. Strengthen minimal-model uniqueness and formality outputs from witness-level to derived statements.

### WP5 - Formality Internalization

Target: `Formality.lean`

1. Add constructive graph-weight/operator infrastructure.
2. Tie `FormalityMorphism` components to graph systems via explicit equations.
   Partial closure: arity-wise consistency with bundled L∞ data and arity-1 HKR normalization are now encoded; remaining work is constructive graph-operator equations for higher arities.
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
