# Proof Ideas: Ribbon.lean

## toPivotalCategory: j = θ⁻¹ ∘ u is an isomorphism

### hom_inv_id: (θ⁻¹ ∘ u) ∘ (u⁻¹ ∘ θ) = id

This reduces to showing drinfeldIso ∘ drinfeldIsoInv = id_X (after θ⁻¹ ∘ θ cancels).

Strategy:
1. `(twist X).inv ≫ drinfeldIso X ≫ drinfeldIsoInv X ≫ (twist X).hom`
2. If `drinfeldIso X ≫ drinfeldIsoInv X = 𝟙 X`, then = `(twist X).inv ≫ (twist X).hom = 𝟙 X`
3. So reduce to showing `drinfeldIso X ≫ drinfeldIsoInv X = 𝟙 X`

The Drinfeld iso uses β_{X,Xᘁ} (forward braiding) and its inverse uses β⁻¹_{X,(Xᘁ)ᘁ}.
The composite is a string diagram that should simplify using:
- ExactPairing zigzags for (X, Xᘁ) and (Xᘁ, (Xᘁ)ᘁ)
- Yang-Baxter equation / braiding naturality
- Coherence (associator, unitor)

### inv_hom_id: similarly reduces to drinfeldIsoInv ≫ drinfeldIso = id

## pivotalIso_naturality

Need: f ≫ j_Y = j_X ≫ fᘁᘁ where j_X = θ_X⁻¹ ≫ u_X.

Strategy:
1. Naturality of twist: f ≫ θ_Y = θ_X ≫ f (given as `twist_naturality`)
2. Naturality of Drinfeld iso: f ≫ u_Y = u_X ≫ fᘁᘁ (needs proof)
3. Combine: f ≫ θ_Y⁻¹ ≫ u_Y = θ_X⁻¹ ≫ f ≫ u_Y = θ_X⁻¹ ≫ u_X ≫ fᘁᘁ

For step 2 (naturality of u), this is a diagram chase using:
- Naturality of braiding: (f ⊗ g) ≫ β = β ≫ (g ⊗ f)
- Naturality of evaluation/coevaluation
- `comp_rightAdjointMate`: (f ≫ g)ᘁ = gᘁ ≫ fᘁ

## pivotalIso_leftDuality / pivotalIso_leftDuality_dual

These are the zigzag identities for j = θ⁻¹ ∘ u. They express that the
induced left duality from the ribbon structure is exact.

Strategy:
- The key insight (EGNO Prop 8.10.5) is that j = u ∘ θ⁻¹ is the UNIQUE
  monoidal pivotal structure corresponding to the twist θ
- The twist_tensor axiom θ_{X⊗Y} = (θ_X ⊗ θ_Y) ∘ c²_{X,Y} is exactly
  what makes θ⁻¹ correct the non-monoidality of u
- Proof involves expanding the zigzag, substituting u and θ⁻¹, then using
  twist_tensor, braiding naturality, and the right duality zigzags

## toSphericalCategory: ribbon implies spherical

Need: leftTrace f = rightTrace f for all f.

Strategy:
- Expand leftTrace and rightTrace using their definitions
- The difference between left and right traces involves j vs j⁻¹ applied
  on opposite sides
- In a ribbon category, j = θ⁻¹ ∘ u, and the twist_dual axiom
  θ_{Xᘁ} = (θ_X)ᘁ provides the key symmetry
- The proof should use twist_dual to relate the two traces

### Key reference: EGNO Proposition 8.10.12
"Every ribbon category is spherical" — the proof uses that
the twist provides the correction making left = right trace.

## twist_unit: θ_𝟙 = id

Strategy from twist_tensor:
- Apply twist_tensor to X = Y = 𝟙:
  θ_{𝟙⊗𝟙} = (θ_𝟙 ⊗ θ_𝟙) ≫ β_{𝟙,𝟙} ≫ β_{𝟙,𝟙}
- Use: 𝟙 ⊗ 𝟙 ≅ 𝟙 (left unitor), β_{𝟙,𝟙} = id (braiding on units)
- Get: θ_𝟙 = θ_𝟙 ≫ θ_𝟙 (under the identification 𝟙 ⊗ 𝟙 = 𝟙)
- Since θ_𝟙 is an iso, cancel one copy to get θ_𝟙 = id

Lean approach:
- Use `BraidedCategory.braiding_leftUnitor` or similar coherence for β_{𝟙,𝟙}
- `leftUnitor_tensor`, `rightUnitor_tensor` for 𝟙 ⊗ 𝟙 coherence
