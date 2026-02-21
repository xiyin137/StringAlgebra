# Proof Ideas: Pivotal.lean

## leftRightDualIso.hom_inv_id / inv_hom_id

These are the two zigzag proofs showing that the left-right dual isomorphism
(ᘁX) ≅ (Xᘁ) is indeed an isomorphism.

### Strategy: String diagram chase

Both proofs are essentially string diagram calculations. The key tools are:
- The two ExactPairing zigzag identities for (X, Xᘁ) and (Xᘁ, (Xᘁ)ᘁ)
- The pivotal isomorphism j and its inverse
- The pivotalIso_leftDuality zigzag identities (both of them)
- Naturality of the pivotal isomorphism

### hom_inv_id: (ᘁX → Xᘁ → ᘁX) = id

The composite is:
```
ᘁX →[λ⁻¹] 𝟙 ⊗ ᘁX →[coev_{Xᘁ} ⊗ id] (Xᘁ ⊗ (Xᘁ)ᘁ) ⊗ ᘁX →[α] Xᘁ ⊗ ((Xᘁ)ᘁ ⊗ ᘁX)
  →[id ⊗ (j⁻¹ ⊗ id)] Xᘁ ⊗ (X ⊗ ᘁX) →[id ⊗ ev_{ᘁX,X}] Xᘁ ⊗ 𝟙 →[ρ] Xᘁ
  →[λ⁻¹] 𝟙 ⊗ Xᘁ →[coev_{ᘁX,X} ⊗ id] (ᘁX ⊗ X) ⊗ Xᘁ →[α] ᘁX ⊗ (X ⊗ Xᘁ)
  →[id ⊗ (j ⊗ id)] ᘁX ⊗ ((Xᘁ)ᘁ ⊗ Xᘁ) →[id ⊗ ev_{Xᘁ,(Xᘁ)ᘁ}] ᘁX ⊗ 𝟙 →[ρ] ᘁX
```

The proof likely involves:
1. Combining the middle section (ρ then λ⁻¹) into an identity
2. Using associativity to rearrange
3. Applying the pivotalIso_leftDuality zigzag to cancel j and j⁻¹
4. Finishing with the ExactPairing zigzag for (ᘁX, X) or (X, Xᘁ)

### Lean tactics to try
- `simp only [Category.assoc]` to normalize associativity
- `slice_lhs` / `slice_rhs` for focusing on subsequences
- Mathlib's monoidal category coherence lemmas
- `MonoidalCategory.whisker_exchange` for commuting whiskers past each other

### Key Mathlib lemmas
- `ExactPairing.coevaluation_evaluation`: zigzag for Y in (X, Y) pairing
- `ExactPairing.evaluation_coevaluation`: zigzag for X in (X, Y) pairing
- `MonoidalCategory.triangle_assoc_comp_left/right`
- `rightUnitor_inv_naturality`, `leftUnitor_naturality`
