# StringAlgebra

Rigorous formalization of algebraic structures in string theory in Lean 4 with Mathlib. All definitions and proofs build purely on Mathlib's foundations. `axiom` is strictly forbidden.

Previously part of [ModularPhysics](https://github.com/xiyin137/ModularPhysics).

## Proof-Gap Counts (2026-02-26)

Counted as lines matching `^\s*sorry` in Lean files.

1. `StringAlgebra/Linfinity`: 3
2. `StringAlgebra/MZV`: 0
3. `StringAlgebra/VOA`: 0
4. `StringAlgebra/MTC`: 18
5. Total (`StringAlgebra/**/*.lean`): 21

Recompute command:

```bash
echo "Linfinity $(rg -n '^\s*sorry\\b' StringAlgebra/Linfinity --glob '*.lean' | wc -l | tr -d ' ')"
echo "MZV $(rg -n '^\s*sorry\\b' StringAlgebra/MZV --glob '*.lean' | wc -l | tr -d ' ')"
echo "VOA $(rg -n '^\s*sorry\\b' StringAlgebra/VOA --glob '*.lean' | wc -l | tr -d ' ')"
echo "MTC $(rg -n '^\s*sorry\\b' StringAlgebra/MTC --glob '*.lean' | wc -l | tr -d ' ')"
echo "TOTAL $(rg -n '^\s*sorry\\b' StringAlgebra --glob '*.lean' | wc -l | tr -d ' ')"
```

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
2. `StringAlgebra/Linfinity` currently has 3 explicit theorem-level `sorry` markers for active proof gaps (`LInfinityAlgebra.lean`: 1, `Transfer.lean`: 2); no `sorry` appears in `def`/`structure`/`abbrev` bodies.
3. Current Linfinity proof-gap loci are:
   - `LInfinityAlgebra.lean`: `transferMorphism_isQuasiIso`
   - `Transfer.lean`: `minimalModelMorphism_isQuasiIso`, `formalityMorphism_isQuasiIso`
4. No `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in Linfinity Lean files.
5. Recent hardening removed fabricated transfer/formality/BV outputs and tautological bridge shells; nontrivial constructions now require explicit witness data rather than hidden defaults, both `LInftyHom` and core `LInftyMorphism` composition have explicit identity/derived composition data and core morphisms enforce arity-0 normalization (`higher_zero`), and remaining transfer quasi-isomorphism obligations are tracked explicitly at theorem sites (`transferMorphism_isQuasiIso`, `minimalModelMorphism_isQuasiIso`, `formalityMorphism_isQuasiIso`) instead of being carried as hidden proof fields in witness structures.
5. Transfer hardening now also exports `transferInclusionLinear_isBijective`, making degreewise bijectivity of SDR inclusions explicit from `transfer_is_quasiIso` plus arity-1 coherence (`transferInclusion_linear`).
6. Minimal/formality witness packages now also expose canonical accessor-level linear bridges (`minimalModelMorphism_linear_isBijective`, `formalityMorphism_linear_isBijective`) plus simp identification lemmas to the packaged linear maps, so degreewise bijectivity can be consumed uniformly from accessor morphisms.
7. Transfer extraction interfaces now include linear-bijectivity-preserving existence theorems (`minimal_model_exists_with_linear_bijectivity`, `isFormal_unpacked_with_linear_bijectivity`, `isFormal_exists_formalityLinear_isBijective`) so witness unpacking does not lose arity-1 isomorphism data.
8. Transfer formality extraction now has explicit reverse/iff bridges (`isFormal_of_unpacked_with_linear_bijectivity`, `isFormal_iff_unpacked_with_linear_bijectivity`, `isFormal_iff_exists_formalityLinear_isBijective`) so strengthened unpacked/package-level views are theorem-level equivalent to `isFormal`.
9. Transfer extraction conservativity is now explicit (`minimal_model_exists_with_linear_bijectivity_iff`, `unpacked_with_linear_bijectivity_iff_unpacked`): strengthened “with linear bijectivity” statements are equivalent to base quasi-isomorphism existence/unpacked statements.
10. Formality classification now has a direct quotient-class bridge (`starProductClassification_toGaugeClass`) and an explicit equivalence theorem (`starProductClassification_iff_toGaugeClass`) between gauge-equivalence and quotient-class formulations.
11. Transfer no longer includes tautological minimal-model uniqueness wrappers that only forwarded supplied comparison-map assumptions.
12. Transfer formality extraction now has direct bridges from unpacked data views to package-level linear-bijectivity witnesses (`unpacked_with_linear_bijectivity_iff_exists_formalityLinear_isBijective`, `unpacked_iff_exists_formalityLinear_isBijective`).
13. Formality classification now also exposes directional extraction lemmas (`starProductClassification_gaugeEquivalent_of_poisson_eq`, `starProductClassification_poisson_eq_of_gaugeEquivalent`, `starProductClassification_toGaugeClass_eq_of_poisson_eq`, `starProductClassification_poisson_eq_of_toGaugeClass_eq`) to consume classification bridges without manually unpacking iff statements.
14. Formality classification removed assumption-forwarding wrapper families; directional extraction lemmas now depend directly on `starProductClassification` and `starProductClassification_toGaugeClass`.
15. Formality classification interface is now kept at direct theorem level (`starProductClassification` and quotient-class bridge/extraction theorems), without alias-contract or classify-parameter forwarding layers.
16. Additional tautological forwarding wrappers have been removed from `LInfinityAlgebra.lean`, `Transfer.lean`, `Coderivations.lean`, `MaurerCartan.lean`, and `Formality.lean`; those files now use direct witness fields where the forwarding theorems added no semantics.
17. `Transfer.transfer_is_quasiIso` and `Formality.kontsevichFormality_is_quasi_iso` are now proved from existing core bridges/spec fields; remaining theorem-level proof gaps are concentrated in core transfer and package-level quasi-isomorphism claims.
18. Remaining semantic debt is tracked explicitly in `StringAlgebra/Linfinity/TODO.md`.

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
transfer_is_quasiIso + transferInclusion_linear -> transferInclusionLinear_isBijective
minimalModelMorphism_isQuasiIso + minimalModelMorphism_linear_eq -> minimalModelMorphism_linear_isBijective -> minimalModelLinear_isBijective
formalityMorphism_isQuasiIso + formalityMorphism_linear_eq -> formalityMorphism_linear_isBijective -> formalityLinear_isBijective
MinimalModelResult + canonical accessor bridges -> minimal_model_exists_with_linear_bijectivity
isFormal -> isFormal_unpacked_with_linear_bijectivity -> isFormal_exists_formalityLinear_isBijective
minimal_model_exists_with_linear_bijectivity <-> minimal_model_exists_with_linear_bijectivity_iff
isFormal_unpacked_with_linear_bijectivity <-> unpacked_with_linear_bijectivity_iff_unpacked
isFormal_of_unpacked_with_linear_bijectivity -> isFormal
isFormal <-> isFormal_iff_unpacked_with_linear_bijectivity <-> isFormal_iff_exists_formalityLinear_isBijective
isFormal_unpacked_with_linear_bijectivity <-> unpacked_with_linear_bijectivity_iff_exists_formalityLinear_isBijective
isFormal_unpacked <-> unpacked_iff_exists_formalityLinear_isBijective
starProductClassification <-> starProductClassification_iff_toGaugeClass -> starProductClassification_toGaugeClass
-> starProductClassification_gaugeEquivalent_of_poisson_eq
-> starProductClassification_poisson_eq_of_gaugeEquivalent
-> starProductClassification_toGaugeClass_eq_of_poisson_eq
-> starProductClassification_poisson_eq_of_toGaugeClass_eq
-> linfty_preserves_mc (with MCPreservation witness)
-> MaurerCartan local deformation packaging (explicit KuranishiTheory witness)
-> deformationQuantization (with QuantizationResult witness)
```

Detailed dependency debt tracking, anti-smuggling gates, and closure order are maintained in `StringAlgebra/Linfinity/TODO.md`.

### Multiple Zeta Values

Shuffle and stuffle algebras, double shuffle relations, iterated integrals, polylogarithms, Drinfeld associators, and motivic MZVs.

Current audited status (2026-02-26):

1. `lake build StringAlgebra.MZV` passes.
2. `StringAlgebra/MZV` is `sorry`-free (proof-level `sorry` count: 0).
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
2. `StringAlgebra/VOA` is `sorry`-free (proof-level `sorry` count: 0).
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

Definitions include fusion coefficients N^m\_{ij}, the S-matrix, T-matrix, quantum dimensions, the Mueger center, and TQFT dimensions. Core definitions are proper (no placeholder defs). Key completed proofs include the twist on the unit, braiding symmetry of fusion coefficients, closure of transparent objects under tensor products, Schur's lemma applications, and the Verlinde genus-1 dimension formula. Remaining MTC proof debt is explicit at theorem sites (`sorry`), with no local assumption-bundle/axiom-class wrappers in MTC.

Current audited gap count (2026-02-26): proof-level `sorry` count in `StringAlgebra/MTC/*.lean` is 18.
