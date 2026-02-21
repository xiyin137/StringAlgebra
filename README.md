# StringAlgebra

Rigorous formalization of algebraic structures in string theory in Lean 4 with Mathlib. All definitions and proofs build purely on Mathlib's foundations, with `sorry` used for incomplete proofs. `axiom` is strictly forbidden.

Previously part of [ModularPhysics](https://github.com/xiyin137/ModularPhysics).

## Structure

```
StringAlgebra/
├── Linfinity/                       # L-infinity algebras
│   ├── LInfinityAlgebra.lean        # Core definition
│   ├── Morphisms.lean               # L-infinity morphisms
│   ├── Transfer.lean                # Homotopy transfer theorem
│   ├── MaurerCartan.lean            # Maurer-Cartan equation
│   ├── Formality.lean               # Formality theorem
│   ├── BVAlgebra.lean               # BV algebra structure
│   ├── DGLA.lean                    # DG Lie algebras
│   ├── Coderivations.lean           # Coderivation approach
│   ├── SymmetricAlgebra.lean
│   ├── SymmetricCoalgebra.lean
│   ├── SymmetricTensor.lean
│   └── PlanarTree.lean
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

Core infrastructure for L-infinity (strong homotopy Lie) algebras, including the symmetric coalgebra/coderivation approach, morphisms, homotopy transfer, Maurer-Cartan theory, and BV algebras.

### Multiple Zeta Values

Shuffle and stuffle algebras, double shuffle relations, iterated integrals, polylogarithms, Drinfeld associators, and motivic MZVs.

### Vertex Operator Algebras

Vertex algebras, formal distributions, modules, the Virasoro algebra, and examples.

### Modular Tensor Categories

Full hierarchy from pivotal categories to the Verlinde formula:

**Pivotal** → **Trace** → **Spherical** → **Ribbon** → **Semisimple** → **Fusion** → **Endomorphism** → **Braided Fusion** → **Ribbon Fusion** → **S-Matrix** → **Modular Tensor Category** → **Verlinde**

Definitions include fusion coefficients N^m\_{ij}, the S-matrix, T-matrix, quantum dimensions, the Mueger center, and TQFT dimensions. All definitions are proper (no axiom smuggling, no placeholders). Key proofs completed include the twist on the unit, braiding symmetry of fusion coefficients, closure of transparent objects under tensor products, Schur's lemma applications, and the Verlinde genus-1 dimension formula. A bridge module connects VOA representation categories to MTCs via Huang's theorem.
