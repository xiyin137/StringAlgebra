# Proof Ideas: SMatrix.lean

## Status (2026-02-25)

Proved:
- `sMatrix_symmetric` (k-valued) via helper
  `sMatrix_symmetric_of_end_symmetric`.
- `quantumDim_vacuum` via helper
  `quantumDim_vacuum_of_sMatrix_unit_ne_zero` and reduction to
  `totalDimSq_ne_zero`.

Temporarily assumption-backed placeholders:
- `SMatrixAxioms.sMatrixEnd_symmetric`
- `SMatrixAxioms.totalDimSq_ne_zero`
- `SMatrixAxioms.quantumDim_fusion`
- `SMatrixAxioms.sMatrix_orthogonality`

## Main Proof Debt

The central blocker remains `sMatrixEnd_symmetric`, which reduces to:
```
trace (β_XY ≫ β_YX) = trace (β_YX ≫ β_XY)
```
for simple representatives `X = simpleObj i`, `Y = simpleObj j`.

This suggests proving a reusable trace-cyclicity/conjugation lemma:
```
trace (f ≫ g) = trace (g ≫ f)
```
or at least an iso-conjugation invariance lemma for trace.

## Proposed development order

1. Add trace cyclicity/conjugation lemmas in `Trace.lean`.
2. Replace `SMatrixAxioms.sMatrixEnd_symmetric`.
3. Replace `SMatrixAxioms.sMatrix_orthogonality`.
4. Derive `totalDimSq_ne_zero` and `quantumDim_fusion`, then remove the remaining axioms.
