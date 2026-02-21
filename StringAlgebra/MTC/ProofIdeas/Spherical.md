# Proof Ideas: Spherical.lean

## qdim_dual: dim(Xᘁ) = dim(X)

Strategy:
- dim(X) = trace(id_X) = leftTrace(id_X)
- dim(Xᘁ) = trace(id_{Xᘁ}) = leftTrace(id_{Xᘁ})
- The left trace of id_X involves the pairing (X, Xᘁ)
- The left trace of id_{Xᘁ} involves the pairing (Xᘁ, (Xᘁ)ᘁ)
- Using the pivotal isomorphism j : X ≅ (Xᘁ)ᘁ, relate the two traces
- In a spherical category, leftTrace = rightTrace, which gives extra
  flexibility in choosing which trace formula to use

## qdim_unit: dim(𝟙) = id_{𝟙}

Strategy:
- dim(𝟙) = trace(id_𝟙) = leftTrace(id_𝟙)
- leftTrace(id_𝟙) = η_{𝟙ᘁ,(𝟙ᘁ)ᘁ} ≫ (𝟙ᘁ ◁ j_𝟙⁻¹) ≫ (𝟙ᘁ ◁ id_𝟙) ≫ ε_{𝟙,𝟙ᘁ}
- Since 𝟙ᘁ = 𝟙 (definitionally in Mathlib), this simplifies significantly
- (𝟙ᘁ)ᘁ = 𝟙ᘁ = 𝟙, and the exact pairings for the unit are simple
- Need to show that η_{𝟙,𝟙} and ε_{𝟙,𝟙} compose to give id_{𝟙}

Key Mathlib facts:
- `(𝟙_ C)ᘁ = 𝟙_ C` (from `hasRightDualUnit`)
- The ExactPairing for (𝟙, 𝟙) should have simple evaluation/coevaluation

## qdim_tensor: dim(X ⊗ Y) = dim(X) ≫ dim(Y)

This is the multiplicativity of quantum dimension. It requires the
full monoidal condition on the pivotal isomorphism (both zigzags).

Strategy:
- dim(X ⊗ Y) = trace(id_{X⊗Y})
- Need to decompose this into trace(id_X) ≫ trace(id_Y)
- The key step is relating j_{X⊗Y} to j_X ⊗ j_Y
- In a spherical category, trace is both left and right trace, giving
  flexibility in how to decompose the tensor product trace
- The "partial trace" argument: trace_{X⊗Y}(f ⊗ g) = trace_X(f) ≫ trace_Y(g)

This is likely the hardest of the three spherical proofs and requires
the pivotalIso_leftDuality + pivotalIso_leftDuality_dual zigzags.
