# L∞ Formality Program - Dependency-Driven TODO (Agent-Rigor)

Date: 2026-02-26

## Scope

This is the active development plan for `StringAlgebra/Linfinity`, with an explicit dependency path to:

1. `StringAlgebra.Linfinity.Formality.formalityTheorem`
2. `StringAlgebra.Linfinity.Formality.deformationQuantization`

It follows `agent.md` strictly: no axiom smuggling, no placeholder end-state, no weakened statements to force proof completion.

## Hard Rules (from `agent.md`)

1. Never introduce `axiom` or equivalent assumption smuggling.
2. Do not keep mathematically meaningful content encoded as placeholders (`True`, `Unit`, arbitrary witness tricks).
3. Do not weaken theorem statements to make proofs easy.
4. When blocked, split into helper lemmas before giving up.
5. Use targeted checks only (`lake env lean <file>`, `lake build <module>`).
6. Keep this file synchronized with actual debt and dependency status.

## Verified Snapshot (2026-02-26)

Integration status:

1. `lake build StringAlgebra.Linfinity` passes.
2. `rg -n ':\s*Unit|:\s*True' StringAlgebra/Linfinity/*.lean` has no hits.
3. `sorry` debt remains and is concentrated in five files.

`StringAlgebra/Linfinity` `sorry` inventory:

| File | `sorry` |
|---|---:|
| `Formality.lean` | 6 |
| `DGLA.lean` | 4 |
| `Transfer.lean` | 3 |
| `LInfinityAlgebra.lean` | 2 |
| `BVAlgebra.lean` | 2 |
| all other `Linfinity` files | 0 |

Total: **17**.

## Module Dependency Flowchart (toward Formality)

Actual import DAG inside `StringAlgebra/Linfinity`:

```text
Basic -> SymmetricCoalgebra -> Coderivations -> LInfinityAlgebra -> Morphisms -> MaurerCartan -> Transfer
ChainComplex -> DGLA
LInfinityAlgebra -> DGLA
DGLA -> Formality
Morphisms -> Formality

GradedInfrastructure -> SymmetricTensor -> SymmetricAlgebra -> PlanarTree
Transfer -> BVAlgebra
SymmetricAlgebra -> BVAlgebra
```

Critical path to formality files is:

```text
Basic/SymmetricCoalgebra/Coderivations -> LInfinityAlgebra -> Morphisms
ChainComplex + LInfinityAlgebra -> DGLA
DGLA + Morphisms -> Formality
```

## Theorem Dependency Flowchart (Formality Critical Path)

```text
DGLA.PolyvectorFieldsDGLA.toDGLAData        (open)
DGLA.HochschildCochainsDGLA.toDGLAData      (open)
DGLA.HKRMap (chain_map + induces_iso fields)
                    |
                    v
          Formality.FormalityData
                    |
                    v
       Formality.kontsevichFormality        (open)
                    |
        +-----------+-----------+
        v                       v
kontsevichFormality_is_linfty   kontsevichFormality_is_quasi_iso (open)
morphism (partially scaffolded)
                    |
                    v
        Formality.formalityTheorem
                    |
                    v
        Formality.linfty_preserves_mc       (open)
                    |
                    v
       Formality.deformationQuantization    (open)
                    |
                    v
       Formality.kontsevichStarProduct      (open)
```

## Current Blockers (ordered by dependency impact)

1. `DGLA.lean` conversion obligations:
   `PolyvectorFieldsDGLA.toDGLAData` and `HochschildCochainsDGLA.toDGLAData` still contain 4 `sorry`.
2. `Morphisms.lean` quasi-isomorphism semantics are still weak (`isQuasiIso` currently only checks zero preservation for `f₁`).
3. `Formality.lean` has 6 `sorry` on core construction and downstream quantization nodes.
4. `LInfinityAlgebra.lean` transfer constructors (`transferredStructure`, `transferMorphism`) still open.
5. `Transfer.lean` has 3 open proofs/constructions used by the transfer branch.
6. `BVAlgebra.lean` has 2 open proofs (not on the shortest formality path, but needed for branch closure).

## Anti-Smuggling Gates (must hold for every closure step)

1. No new `axiom`.
2. No reintroduction of `Unit`/`True` structure fields for nontrivial mathematical data.
3. No theorem restatement as tautology (`n = n`, `x = x`, `∃ x, x = x`) unless the theorem itself is explicitly about inhabitation.
4. No constant-zero witness used to satisfy a nontrivial interface without an explicit TODO entry and dependency note.
5. Any temporary scaffolding must be named and tracked as removable debt in this file.

## Dependency-Ordered Work Packages

### WP0 - Guardrail Lock-In

Targets:

1. `Morphisms.lean`
2. `Formality.lean`

Tasks:

1. Document and isolate semantic placeholders currently encoded as reflexive equalities/constant maps.
2. Tighten theorem statements where they were reduced to tautologies.

Exit checks:

1. `rg -n '\bn = n\b|\bx = x\b|∃ .* = .*' StringAlgebra/Linfinity/Formality.lean StringAlgebra/Linfinity/Morphisms.lean` reviewed and justified line-by-line.

### WP1 - DGLA Adapter Closure (hard prerequisite)

Targets:

1. `DGLA.lean`

Tasks:

1. Close all 4 `sorry` in the two `toDGLAData` constructors.
2. Add helper lemmas for degree casts and shifted antisymmetry transport.

Exit checks:

1. `lake env lean StringAlgebra/Linfinity/DGLA.lean`
2. `lake build StringAlgebra.Linfinity.DGLA`

### WP2 - Quasi-Isomorphism Semantics Upgrade

Targets:

1. `Morphisms.lean`
2. `Formality.lean` (call-site updates)

Tasks:

1. Replace weak `LInftyHom.isQuasiIso` predicate with a defensible surrogate (at minimum: degreewise bijectivity on linear part, until full homology API is wired).
2. Update `quasiIso_comp`, `kontsevichFormality_is_quasi_iso`, and all transfer/formality uses.

Exit checks:

1. `lake env lean StringAlgebra/Linfinity/Morphisms.lean`
2. `lake env lean StringAlgebra/Linfinity/Formality.lean`

### WP3 - Formality Core Construction

Targets:

1. `Formality.lean`

Tasks:

1. Implement `kontsevichFormality` with explicit component construction (scaffold acceptable only if mathematically typed and non-tautological).
2. Close `kontsevichFormality_is_quasi_iso` using HKR data currently present in `FormalityData`.
3. Keep `formalityTheorem` as a direct consequence (no weakening).

Exit checks:

1. `lake env lean StringAlgebra/Linfinity/Formality.lean`
2. `lake build StringAlgebra.Linfinity.Formality`

### WP4 - MC Transfer to Quantization Output

Targets:

1. `Formality.lean`
2. `MaurerCartan.lean` (if needed for stronger MC transport API)

Tasks:

1. Close `linfty_preserves_mc` with explicit construction and nontrivial condition.
2. Close `deformationQuantization` and `kontsevichStarProduct` with concrete witnesses matching theorem statements.
3. Ensure `StarProduct` leading-term and Poisson extraction statements are used meaningfully, not tautologically.

Exit checks:

1. `lake env lean StringAlgebra/Linfinity/Formality.lean`
2. `lake build StringAlgebra.Linfinity`

### WP5 - Transfer/BV Branch Closure (parallel branch, post-critical path)

Targets:

1. `LInfinityAlgebra.lean`
2. `Transfer.lean`
3. `BVAlgebra.lean`

Tasks:

1. Close transfer constructors and uniqueness theorem.
2. Close BV `sorry` proofs.
3. Remove remaining placeholder comments once replaced by actual lemmas.

Exit checks:

1. `lake env lean StringAlgebra/Linfinity/LInfinityAlgebra.lean`
2. `lake env lean StringAlgebra/Linfinity/Transfer.lean`
3. `lake env lean StringAlgebra/Linfinity/BVAlgebra.lean`

## Execution Cadence

1. Start each session with debt scan (`sorry`, semantic placeholder grep).
2. Work in dependency order: `DGLA -> Morphisms -> Formality` before transfer/BV cleanup.
3. After each closed node, run file-scoped check immediately.
4. Only run `lake build StringAlgebra.Linfinity` as an integration gate after all touched files are green.
