# VOA Soundness TODO (Dependency-Driven)

Date: 2026-02-26

This file tracks semantic and proof debt for `StringAlgebra/VOA` under `agent.md` rigor rules.

## Current Verified State

1. `lake build StringAlgebra.VOA` passes.
2. `StringAlgebra/VOA/*.lean` is `sorry`-free.
3. No `axiom`/`admit`/`Classical.choose`/`Classical.epsilon` usage in VOA Lean files.
4. Placeholder `True := trivial` stubs in core module/formal-distribution/example interfaces have been removed.
5. Conformal-weight extraction and lattice rationality criteria now use explicit witness packages (`L0Grading`, `RationalityCriterion`) instead of implicit selection.

## VOA Dependency Graph

```text
Basic
  -> FormalDistributions
  -> VertexAlgebra
  -> Virasoro
  -> Modules
  -> Examples

Detailed edge chain:
Basic -> FormalDistributions -> VertexAlgebra -> Virasoro -> Modules -> Examples
```

## Theorem Flow Toward Representation/Fusion Layer

```text
Formal-distribution locality/OPE interfaces
-> vertex algebra axioms (vacuum/translation/locality)
-> conformal/Virasoro structures
-> module/intertwining/fusion interfaces
-> example families (Heisenberg, affine, lattice, moonshine)
```

## Audit Matrix

1. `Basic.lean`: low risk. Formal Laurent-series infrastructure is explicit and stable.
2. `FormalDistributions.lean`: medium risk. Locality/OPE interfaces are explicit; full Borcherds/Dong closure is still witness-driven.
3. `VertexAlgebra.lean`: medium risk. Core axioms are explicit; conformal-weight extraction now uses explicit grading witnesses.
4. `Virasoro.lean`: medium risk. Virasoro and minimal-model interfaces are explicit; full representation-theoretic closure remains pending.
5. `Modules.lean`: medium-high risk. Module/fusion structures are explicit; fusion finiteness now has positive finite-bound theorems, while complete reducibility and deeper fusion semantics still need stronger derived closure theorems.
6. `Examples.lean`: medium-high risk. Example families are explicit and type-safe; lattice rationality criteria now include explicit forward/backward implication lemmas, while deeper construction-specific theorem derivations are pending.

## Open Work Packages

### WP1 - Jacobi/Borcherds Internalization

Targets: `FormalDistributions.lean`, `VertexAlgebra.lean`

1. Replace coefficient-model simplifications with progressively richer Jacobi/Borcherds formulations.
2. Internalize Dong-lemma closure from explicit witness contracts to derived lemmas where feasible.
3. Strengthen locality/OPE compatibility theorems beyond mode-level commutation shells.

### WP2 - Conformal/Virasoro Closure

Targets: `VertexAlgebra.lean`, `Virasoro.lean`

1. Expand explicit `L(0)` grading witness usage across conformal-dependent APIs.
2. Add additional derived Virasoro-mode identities from the scaled commutator axiom.
3. Tighten primary-state interfaces with more derived consequences.

### WP3 - Module/Fusion Semantics

Target: `Modules.lean`

1. Strengthen complete-reducibility interfaces toward semisimple decomposition witnesses.
2. Add explicit compatibility contracts between intertwining operators and VOA actions.
3. Improve fusion-finiteness statements from tautological bounds to representation-theoretic bounds where infrastructure exists.

### WP4 - Example Realization Depth

Target: `Examples.lean`

1. Refine each example section with construction-level assumptions and derived consequences.
2. Keep rationality/classification claims tied to explicit criteria data, not informal naming.
3. Connect example statements to module/fusion interfaces by explicit lemmas.

## Anti-Smuggling Gates

1. No `axiom`.
2. No `sorry`.
3. No fabricated outputs in core algebra/module operations.
4. Any external assumption contract must be explicit and minimal.
