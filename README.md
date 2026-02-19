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
└── VOA/                             # Vertex operator algebras
    ├── VertexAlgebra.lean
    ├── FormalDistributions.lean
    ├── Modules.lean
    ├── Virasoro.lean
    └── Examples.lean
```

### L-infinity Algebras

Core infrastructure for L-infinity (strong homotopy Lie) algebras, including the symmetric coalgebra/coderivation approach, morphisms, homotopy transfer, Maurer-Cartan theory, and BV algebras.

### Multiple Zeta Values

Shuffle and stuffle algebras, double shuffle relations, iterated integrals, polylogarithms, Drinfeld associators, and motivic MZVs.

### Vertex Operator Algebras

Vertex algebras, formal distributions, modules, the Virasoro algebra, and examples.
