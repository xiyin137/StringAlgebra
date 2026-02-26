# StringAlgebra

Rigorous formalization of algebraic structures in string theory in Lean 4 with Mathlib. All definitions and proofs build purely on Mathlib's foundations. `axiom` is strictly forbidden.

Previously part of [ModularPhysics](https://github.com/xiyin137/ModularPhysics).

## Structure

```
StringAlgebra/
├── Linfinity/                       # L-infinity algebras
│   ├── Basic.lean                   # Grading/sign foundations
│   ├── GradedInfrastructure.lean    # Graded multilinear infrastructure
│   ├── SymmetricTensor.lean         # Symmetric tensors
│   ├── SymmetricAlgebra.lean        # Symmetric algebra
│   ├── SymmetricCoalgebra.lean      # Symmetric coalgebra
│   ├── Coderivations.lean           # Coderivation approach
│   ├── ChainComplex.lean            # DG module/chain-level infrastructure
│   ├── LInfinityAlgebra.lean        # Core definition
│   ├── Morphisms.lean               # L-infinity morphisms
│   ├── MaurerCartan.lean            # Maurer-Cartan equation
│   ├── Transfer.lean                # Homotopy transfer theorem
│   ├── DGLA.lean                    # DG Lie algebras
│   ├── BVAlgebra.lean               # BV algebra structure
│   ├── Formality.lean               # Formality theorem
│   ├── PlanarTree.lean              # Tree combinatorics
│   └── TODO.md                      # Dependency-driven closure plan
├── MZV/                             # Multiple zeta values
│   ├── ShuffleAlgebra.lean
│   ├── StuffleAlgebra.lean
│   ├── DoubleShuffle.lean
│   ├── Relations.lean
│   ├── IteratedIntegral.lean
│   ├── Polylogarithm.lean
│   ├── Associator.lean
│   ├── Motivic.lean
│   └── TODO.md                      # Dependency-driven closure plan
├── VOA/                             # Vertex operator algebras
│   ├── VertexAlgebra.lean
│   ├── FormalDistributions.lean
│   ├── Modules.lean
│   ├── Virasoro.lean
│   ├── Examples.lean
│   └── TODO.md                      # Dependency-driven closure plan
└── MTC/                             # Modular tensor categories
    ├── Pivotal.lean                 # Pivotal categories (j : X ≅ Xᘁᘁ)
    ├── Trace.lean                   # Left/right categorical traces
    ├── Spherical.lean               # Spherical categories, quantum dim
    ├── Ribbon.lean                  # Ribbon categories, twist, Drinfeld iso
    ├── Semisimple.lean              # Semisimple categories, Schur's lemma
    ├── FusionCategory.lean          # Fusion categories, fusion coefficients
    ├── Endomorphism.lean            # scalarOfEndo infrastructure
    ├── BraidedFusion.lean           # Braided fusion, Mueger center
    ├── RibbonFusion.lean            # Ribbon fusion, twist values, T-matrix
    ├── SMatrix.lean                 # S-matrix (End-valued and k-valued)
    ├── ModularTensorCategory.lean   # MTC class, modular relations
    ├── Verlinde.lean                # Verlinde formula, TQFT dimensions
    └── Bridge/
        └── VOAToMTC.lean            # Huang's theorem (interface contract)
```

### L-infinity Algebras

Core infrastructure for L-infinity (strong homotopy Lie) algebras, including the symmetric coalgebra/coderivation approach, morphisms, homotopy transfer, Maurer-Cartan theory, DGLAs, BV structures, and the formality/quantization pipeline.

Current audited status (2026-02-26):

1. `lake build StringAlgebra.Linfinity` passes.
2. `StringAlgebra/Linfinity` is currently `sorry`-free.
3. No `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in Linfinity Lean files.
4. Recent hardening removed fabricated transfer/formality/BV outputs and tautological bridge shells; nontrivial constructions now require explicit witness data rather than hidden defaults, both `LInftyHom` and core `LInftyMorphism` composition have explicit identity/derived composition data and core morphisms now enforce arity-0 normalization (`higher_zero`), DGLA-to-L∞ transport plus `LInftyHom`/core-morphism conversion now have explicit bridge infrastructure with bidirectional quasi-isomorphism criterion equivalence for canonical lifts, explicit higher-shape constraints on canonical lift witnesses, explicit-lift quasi-isomorphism iff criteria with derived linear-vs-unary coherence, and higher-component round-trip preservation, homotopy-transfer in the core `LInfinityAlgebra` interface now carries explicit linear and quasi-isomorphism certification for the lifted inclusion, coderivation/L∞ extraction interfaces now enforce unary consistency between multilinear and linear witness layers, map/component agreement on matching word lengths, explicit unary-output shape constraints for extracted components, stored total-degree consistency in both symmetric-power and reduced-coalgebra element records together with explicit zero-marker normalization constraints across symmetric-power/symmetric-coalgebra/reduced-coalgebra layers, bracket-level component interfaces now enforce arity-indexed degree consistency for both general morphism components and formality components, explicit equivalence between map-level/component-level vanishing formulations, square-zero decomposition by word length, bracket-level characterization lemmas for DGLA/Lie/Lie2 truncation, and explicit theorem-level unary extraction bridges, Maurer-Cartan Kuranishi local models now require explicit `KuranishiTheory` data (no hardcoded zero map), Maurer-Cartan gauge equivalence now has explicit relation lemmas plus a canonical `Setoid`, gauge action is now explicitly linked to encoded gauge-equivalence and MC-preservation constraints (`gaugeAction_zero`, `gaugeAction_sound`, `gaugeAction_preserves_curvature_zero`) with a canonical action on MC elements (`MCElement.gaugeAct`) and theorem-level moduli-class invariance (`MCElement.toModuli_eq_gaugeAct`), smoothness now exposes an explicit moduli-point constructor, MC twisting/tangent-obstruction interfaces now use witness-aligned naming/documentation, and MC moduli classes now have an explicit projection/characterization (`a.toModuli = b.toModuli ↔ GaugeEquivalent T a b`), `LInftyHomotopy` now carries an explicit first-order linear homotopy equation with canonical data-level `refl/symm/trans` constructors plus induced `Setoid` and homotopy-class quotient interfaces, transfer-level minimal-model uniqueness now returns explicit quasi-isomorphic comparison data rather than bare existence, transfer-level minimal/formality witness packages now expose explicit linear quasi-isomorphism views tied to arity-1 components, transfer-level formality now has an explicit unpacked interface equivalent to `isFormal` plus canonical accessor morphisms, transfer-result inclusion witnesses now explicitly enforce arity-1 agreement with underlying SDR inclusion maps, BV now records its current `Δ`-closure assumption explicitly as `triple_delta_zero` rather than claiming the full seven-term identity, and formality-level witness packaging now enforces explicit arity-wise component consistency (`component_spec`), arity-1 HKR normalization (`linear_hkr_spec`), non-tautological ground-target ordering constraints in `KontsevichGraph`, and element-level arity-1 linear compatibility in MC transport (`map_element_linear`) before exposing star-product gauge equivalence/gauge-class interfaces, including a direct classification bridge at quotient-class level with normalized, data-preserving gauge transformations and witness-aligned theorem naming.
5. Transfer hardening now also exports `transferInclusionLinear_isBijective`, making degreewise bijectivity of SDR inclusions explicit from `TransferResult.inclusion_isQuasiIso` plus arity-1 coherence (`transferInclusion_linear`).
6. Minimal/formality witness packages now also expose canonical accessor-level linear bridges (`minimalModelMorphism_linear_isBijective`, `formalityMorphism_linear_isBijective`) plus simp identification lemmas to the packaged linear maps, so degreewise bijectivity can be consumed uniformly from accessor morphisms.
7. Transfer extraction interfaces now include linear-bijectivity-preserving existence theorems (`minimal_model_exists_with_linear_bijectivity`, `isFormal_unpacked_with_linear_bijectivity`, `isFormal_exists_formalityLinear_isBijective`) so witness unpacking does not lose arity-1 isomorphism data.
8. Transfer formality extraction now has explicit reverse/iff bridges (`isFormal_of_unpacked_with_linear_bijectivity`, `isFormal_iff_unpacked_with_linear_bijectivity`, `isFormal_iff_exists_formalityLinear_isBijective`) so strengthened unpacked/package-level views are theorem-level equivalent to `isFormal`.
9. Transfer extraction conservativity is now explicit (`minimal_model_exists_with_linear_bijectivity_iff`, `unpacked_with_linear_bijectivity_iff_unpacked`): strengthened “with linear bijectivity” statements are equivalent to base quasi-isomorphism existence/unpacked statements.
10. Formality classification bridges are now bidirectional (`starProductClassification_toGaugeClass`, `starProductClassification_of_toGaugeClass`) with an explicit equivalence theorem (`starProductClassification_iff_toGaugeClass`) between gauge-equivalence and quotient-class formulations.
11. Transfer minimal-model uniqueness now has an explicit conservativity theorem (`minimal_model_unique_iff_isQuasiIso`) linking witness-return packaging directly to `comparison.isQuasiIso`.
12. Remaining semantic debt is tracked explicitly in `StringAlgebra/Linfinity/TODO.md`.

Current dependency flow toward `Formality.lean`:

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
```

Theorem-critical flow toward deformation quantization:

```text
PolyvectorFieldsDGLA.toDGLAData + HochschildCochainsDGLA.toDGLAData + HKRMap + FormalityMorphism witness
-> kontsevichFormality
-> kontsevichFormality_is_quasi_iso
-> formalityTheorem
TransferResult.inclusion_isQuasiIso + transferInclusion_linear -> transferInclusionLinear_isBijective
MinimalModelResult.quasiIso_property + minimalModelMorphism_linear_eq -> minimalModelMorphism_linear_isBijective -> minimalModelLinear_isBijective
FormalityResult.quasiIso_property + formalityMorphism_linear_eq -> formalityMorphism_linear_isBijective -> formalityLinear_isBijective
MinimalModelResult + canonical accessor bridges -> minimal_model_exists_with_linear_bijectivity
isFormal -> isFormal_unpacked_with_linear_bijectivity -> isFormal_exists_formalityLinear_isBijective
minimal_model_exists_with_linear_bijectivity <-> minimal_model_exists_with_linear_bijectivity_iff
isFormal_unpacked_with_linear_bijectivity <-> unpacked_with_linear_bijectivity_iff_unpacked
minimal_model_unique <-> minimal_model_unique_iff_isQuasiIso
isFormal_of_unpacked_with_linear_bijectivity -> isFormal
isFormal <-> isFormal_iff_unpacked_with_linear_bijectivity <-> isFormal_iff_exists_formalityLinear_isBijective
starProductClassification <-> starProductClassification_iff_toGaugeClass -> starProductClassification_toGaugeClass -> starProductClassification_of_toGaugeClass
-> linfty_preserves_mc (with MCPreservation witness)
-> MaurerCartan local deformation packaging (explicit KuranishiTheory witness)
-> deformationQuantization (with QuantizationResult witness)
```

Detailed dependency debt tracking, anti-smuggling gates, and closure order are maintained in `StringAlgebra/Linfinity/TODO.md`.

### Multiple Zeta Values

Shuffle and stuffle algebras, double shuffle relations, iterated integrals, polylogarithms, Drinfeld associators, and motivic MZVs.

Current audited status (2026-02-26):

1. `lake build StringAlgebra.MZV` passes.
2. `StringAlgebra/MZV` is `sorry`-free.
3. No `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in MZV Lean files.
4. Remaining semantic/proof debt is tracked in `StringAlgebra/MZV/TODO.md` (including finite-basis double-shuffle interfaces and explicit Ihara-derivation structural lemmas).

Current dependency flow:

```text
Basic -> ShuffleAlgebra -> DoubleShuffle -> Motivic -> Associator
Basic -> StuffleAlgebra -> DoubleShuffle -> Relations
Basic -> Polylogarithm
ShuffleAlgebra -> IteratedIntegral
```

### Vertex Operator Algebras

Vertex algebras, formal distributions, modules, the Virasoro algebra, and examples.

Current audited status (2026-02-26):

1. `lake build StringAlgebra.VOA` passes.
2. `StringAlgebra/VOA` is `sorry`-free.
3. No `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in VOA Lean files.
4. Recent hardening removed `Classical.choose`-based conformal-weight extraction and replaced fabricated Dong/antibracket-style outputs with explicit witness-driven contracts, including explicit lattice rationality criterion packages, positive fusion-rule bound theorems under rationality assumptions, and derived locality symmetry constructors.
5. Remaining semantic/proof debt is tracked in `StringAlgebra/VOA/TODO.md`.

Current dependency flow:

```text
Basic -> FormalDistributions -> VertexAlgebra -> Virasoro -> Modules -> Examples
```

### Modular Tensor Categories

Full hierarchy from pivotal categories to the Verlinde formula:

**Pivotal** → **Trace** → **Spherical** → **Ribbon** → **Semisimple** → **Fusion** → **Endomorphism** → **Braided Fusion** → **Ribbon Fusion** → **S-Matrix** → **Modular Tensor Category** → **Verlinde**

Definitions include fusion coefficients N^m\_{ij}, the S-matrix, T-matrix, quantum dimensions, the Mueger center, and TQFT dimensions. All definitions are proper (no axiom smuggling, no placeholders). Key proofs completed include the twist on the unit, braiding symmetry of fusion coefficients, closure of transparent objects under tensor products, Schur's lemma applications, and the Verlinde genus-1 dimension formula. A bridge module connects VOA representation categories to MTCs via Huang's theorem.
