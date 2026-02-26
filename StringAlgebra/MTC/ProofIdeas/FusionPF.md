# Proof Ideas: FusionPF.lean

## Status (2026-02-26)

Open theorem-level gaps:
- `fpDimCandidate_unit_gap`
- `fpDimCandidate_pos_gap`
- `fpDimCandidate_fusion_gap`
- `fpDimCandidateByFin_pos`
- `fpDimCandidateByFin_fusion`

No PF assumption classes remain.

## Proof Plan

1. Establish positivity of spectral-radius candidates from nonnegative fusion matrices.
2. Prove fusion-character identity for `fpDimCandidate`.
3. Transport results to Fin-indexed forms.

## Structural Direction

- Keep algebraic matrix facts in `FusionMatrices`/`FusionSpectral`.
- Keep PF analytic lemmas in `FusionPF` (or split into `FusionPF/Core`, `FusionPF/Perron`, `FusionPF/Character`).
