# Proof Ideas: Spherical.lean

## Status (2026-02-25)

`qdim_dual`, `qdim_unit`, and `qdim_tensor` are now exposed through the
assumption class:

- `SphericalDimAxioms`

The exported theorem names remain unchanged (`qdim_dual`, `qdim_unit`,
`qdim_tensor`), while proof debt is isolated behind an explicit contract.

## Proof Obligations To Replace Axioms

### `qdim_dual`: dim(Xᘁ) = dim(X)
- Prove a trace-duality bridge lemma:
  `leftTrace (𝟙 (Xᘁ)) = rightTrace (𝟙 X)`.
- Combine with sphericality `leftTrace = rightTrace`.
- Normalize with pivotal isomorphism naturality and mate lemmas.

### `qdim_unit`: dim(𝟙) = 𝟙
- Specialize pivotal zigzags at `X = 𝟙_ C`.
- Reduce the resulting expression to unit exact-pairing identities.
- Keep this as a reusable normalization lemma for later trace proofs.

### `qdim_tensor`: dim(X ⊗ Y) = dim(X) ≫ dim(Y)
- Introduce a partial-trace multiplicativity lemma.
- Use monoidality of the pivotal structure (both zigzags already available).
- Apply sphericality only at the final normalization boundary.

## Recommended Ordering

1. Prove `qdim_unit`.
2. Prove `qdim_dual`.
3. Prove `qdim_tensor` using the previous normalization lemmas.
