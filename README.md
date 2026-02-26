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
│   └── Motivic.lean
├── VOA/                             # Vertex operator algebras
│   ├── VertexAlgebra.lean
│   ├── FormalDistributions.lean
│   ├── Modules.lean
│   ├── Virasoro.lean
│   └── Examples.lean
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
4. Recent hardening removed fabricated transfer/formality outputs; nontrivial constructions now require explicit witness data rather than hidden defaults.
5. Remaining semantic debt is tracked explicitly in `StringAlgebra/Linfinity/TODO.md`.

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
-> linfty_preserves_mc (with MCPreservation witness)
-> deformationQuantization (with QuantizationResult witness)
```

Detailed dependency debt tracking, anti-smuggling gates, and closure order are maintained in `StringAlgebra/Linfinity/TODO.md`.

### Multiple Zeta Values

Shuffle and stuffle algebras, double shuffle relations, iterated integrals, polylogarithms, Drinfeld associators, and motivic MZVs.

### Vertex Operator Algebras

Vertex algebras, formal distributions, modules, the Virasoro algebra, and examples.

### Modular Tensor Categories

Full hierarchy from pivotal categories to the Verlinde formula:

**Pivotal** → **Trace** → **Spherical** → **Ribbon** → **Semisimple** → **Fusion** → **Endomorphism** → **Braided Fusion** → **Ribbon Fusion** → **S-Matrix** → **Modular Tensor Category** → **Verlinde**

Definitions include fusion coefficients N^m\_{ij}, the S-matrix, T-matrix, quantum dimensions, the Mueger center, and TQFT dimensions. All definitions are proper (no axiom smuggling, no placeholders). Key proofs completed include the twist on the unit, braiding symmetry of fusion coefficients, closure of transparent objects under tensor products, Schur's lemma applications, and the Verlinde genus-1 dimension formula. A bridge module connects VOA representation categories to MTCs via Huang's theorem.
