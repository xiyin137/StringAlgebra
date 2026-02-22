# Proof Ideas: Ribbon.lean

## Status

- `twist_unit` — **PROVED**
- `toPivotalCategory` (hom_inv_id, inv_hom_id) — **PROVED** (via `rightDualIso.symm`)
- `pivotalIso_naturality` — **PROVED** (via drinfeldIsoIso_naturality + twist_naturality)
- `pivotalIso_leftDuality` — IN PROGRESS (detailed proof plan below)
- `pivotalIso_leftDuality_dual` — pending (parallel structure to leftDuality)
- `toSphericalCategory` — pending (depends on zigzag identities)

## Helper lemmas — all PROVED

- `whiskerRight_eval_cancel` — injectivity: f ▷ Yᘁ ≫ ε = g ▷ Yᘁ ≫ ε → f = g
- `drinfeldIsoIso_eval` — u ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ
- `drinfeldIsoIso_coeval` — η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ u⁻¹ = η_ X Xᘁ ≫ (β_ Xᘁ X).inv
- `drinfeldIsoIso_naturality` — f ≫ u_Y = u_X ≫ fᘁᘁ

---

## Critical Mathlib type conventions (ExactPairing)

**These must be kept in mind for all proofs in this file!**

```
class ExactPairing (X Y : C) where
  coevaluation' : 𝟙_ C ⟶ X ⊗ Y       -- NOTE: X ⊗ Y, not Y ⊗ X
  evaluation'   : Y ⊗ X ⟶ 𝟙_ C       -- NOTE: Y ⊗ X, not X ⊗ Y

η_ X Y : 𝟙_ C ⟶ X ⊗ Y               -- coevaluation
ε_ X Y : Y ⊗ X ⟶ 𝟙_ C               -- evaluation
```

### Zigzag identities for ExactPairing X Y:

```
coevaluation_evaluation' (Y-zigzag):
  Y ◁ η_ X Y ≫ (α_ Y X Y).inv ≫ ε_ X Y ▷ Y = (ρ_ Y).hom ≫ (λ_ Y).inv

evaluation_coevaluation' (X-zigzag):
  η_ X Y ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε_ X Y = (λ_ X).hom ≫ (ρ_ X).inv
```

### Standard right duality ExactPairing X Xᘁ:

```
η_ X Xᘁ : 𝟙 → X ⊗ Xᘁ
ε_ X Xᘁ : Xᘁ ⊗ X → 𝟙
```

### Standard ExactPairing Xᘁ (Xᘁ)ᘁ:

```
η_ Xᘁ (Xᘁ)ᘁ : 𝟙 → Xᘁ ⊗ (Xᘁ)ᘁ
ε_ Xᘁ (Xᘁ)ᘁ : (Xᘁ)ᘁ ⊗ Xᘁ → 𝟙
```

### Swap pairing (from BraidedCategory.exactPairing_swap)

```
exactPairing_swap X Y [ExactPairing X Y] : ExactPairing Y X where
  coevaluation' := η_ X Y ≫ (β_ Y X).inv     -- 𝟙 → X ⊗ Y → Y ⊗ X
  evaluation'   := (β_ X Y).hom ≫ ε_ X Y     -- X ⊗ Y → Y ⊗ X → 𝟙
```

For `exactPairing_swap X Xᘁ : ExactPairing Xᘁ X`:

```
η_swap := η_ X Xᘁ ≫ (β_ Xᘁ X).inv : 𝟙 → X ⊗ Xᘁ → Xᘁ ⊗ X
ε_swap := (β_ X Xᘁ).hom ≫ ε_ X Xᘁ : X ⊗ Xᘁ → Xᘁ ⊗ X → 𝟙
```

### Swap zigzag for ExactPairing Xᘁ X (coevaluation_evaluation):

```
X ◁ η_swap ≫ (α_ X Xᘁ X).inv ≫ ε_swap ▷ X = (ρ_ X).hom ≫ (λ_ X).inv
```

This is proved in Mathlib as `coevaluation_evaluation_braided'` (private).

---

## pivotalIso_leftDuality — COMPLETE PROOF PLAN

### Goal (from Pivotal.lean:79-82)

```lean
(ρ_ X).inv ≫ (X ◁ η_ Xᘁ (Xᘁ)ᘁ) ≫ (X ◁ (Xᘁ ◁ (pivotalIso X).inv)) ≫
(α_ X Xᘁ X).inv ≫ (((pivotalIso X).hom ▷ Xᘁ) ▷ X) ≫
((ε_ Xᘁ (Xᘁ)ᘁ) ▷ X) ≫ (λ_ X).hom = 𝟙 X
```

where `(pivotalIso X).hom = θ⁻¹ ≫ u` and `(pivotalIso X).inv = u⁻¹ ≫ θ`.

### Step 1: Expand j and distribute whiskers

```
simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
           whiskerLeft_comp, comp_whiskerRight, Category.assoc]
```

After expansion:
```
ρ⁻¹ ≫ (X ◁ η_ Xᘁ (Xᘁ)ᘁ) ≫ (X ◁ (Xᘁ ◁ u⁻¹)) ≫ (X ◁ (Xᘁ ◁ θ)) ≫
α⁻¹ ≫ ((θ⁻¹ ▷ Xᘁ) ▷ X) ≫ ((u ▷ Xᘁ) ▷ X) ≫ (ε_ Xᘁ (Xᘁ)ᘁ ▷ X) ≫ λ
```

### Step 2: Apply drinfeldIsoIso_coeval

Combine `(X ◁ η_ Xᘁ (Xᘁ)ᘁ) ≫ (X ◁ (Xᘁ ◁ u⁻¹))` into
`X ◁ (η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ u⁻¹)` using `← whiskerLeft_comp`,
then rewrite with `drinfeldIsoIso_coeval`.

Result: `X ◁ (η_ X Xᘁ ≫ (β_ Xᘁ X).inv)`, which equals
`(X ◁ η_ X Xᘁ) ≫ (X ◁ (β_ Xᘁ X).inv)` = `X ◁ η_swap`.

After re-expanding with `whiskerLeft_comp`:
```
ρ⁻¹ ≫ (X ◁ η_swap) ≫ (X ◁ (Xᘁ ◁ θ)) ≫
α⁻¹ ≫ ((θ⁻¹ ▷ Xᘁ) ▷ X) ≫ ((u ▷ Xᘁ) ▷ X) ≫ (ε_ Xᘁ (Xᘁ)ᘁ ▷ X) ≫ λ
```

### Step 3: Apply drinfeldIsoIso_eval

Combine `((u ▷ Xᘁ) ▷ X) ≫ (ε_ Xᘁ (Xᘁ)ᘁ ▷ X)` into
`(u ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ) ▷ X` using `← comp_whiskerRight`,
then rewrite with `drinfeldIsoIso_eval`.

Result: `((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ▷ X` = `ε_swap ▷ X`.

After re-expanding with `comp_whiskerRight`:
```
ρ⁻¹ ≫ (X ◁ η_swap) ≫ (X ◁ (Xᘁ ◁ θ)) ≫
α⁻¹ ≫ ((θ⁻¹ ▷ Xᘁ) ▷ X) ≫ (ε_swap ▷ X) ≫ λ
```

### Step 4: Move θ to the far right

**4a.** Past α⁻¹ (associator naturality in Z):
```
X ◁ (Xᘁ ◁ θ) ≫ (α_ X Xᘁ X).inv = (α_ X Xᘁ X).inv ≫ (X ⊗ Xᘁ) ◁ θ
```
Mathlib: `associator_inv_naturality_right` (or derive from `associator_naturality`)

**4b.** Past `(θ⁻¹ ▷ Xᘁ) ▷ X` (different tensor factors, commute):
```
(X ⊗ Xᘁ) ◁ θ ≫ (θ⁻¹ ▷ Xᘁ) ▷ X = (θ⁻¹ ▷ Xᘁ) ▷ X ≫ (X ⊗ Xᘁ) ◁ θ
```
Mathlib: `whisker_exchange` with f = θ⁻¹ ▷ Xᘁ, g = θ

**4c.** Past `ε_swap ▷ X` (whisker_exchange):
```
(X ⊗ Xᘁ) ◁ θ ≫ ε_swap ▷ X = ε_swap ▷ X ≫ (𝟙_ C) ◁ θ
```
Mathlib: `whisker_exchange` with f = ε_swap, g = θ

**4d.** Past λ (leftUnitor naturality):
```
(𝟙_ C) ◁ θ ≫ (λ_ X).hom = (λ_ X).hom ≫ θ
```
Mathlib: `leftUnitor_naturality`

After step 4:
```
ρ⁻¹ ≫ (X ◁ η_swap) ≫ α⁻¹ ≫ ((θ⁻¹ ▷ Xᘁ) ▷ X) ≫ (ε_swap ▷ X) ≫ λ ≫ θ
```

### Step 5: Move θ⁻¹ to the far left

**5a.** Past α⁻¹ (associator naturality in X):
```
(α_ X Xᘁ X).inv ≫ (θ⁻¹ ▷ Xᘁ) ▷ X = θ⁻¹ ▷ (Xᘁ ⊗ X) ≫ (α_ X Xᘁ X).inv
```
Mathlib: `associator_inv_naturality_left` (naturality of α⁻¹ in the first component)

**5b.** Past `X ◁ η_swap` (whisker_exchange):
```
(X ◁ η_swap) ≫ θ⁻¹ ▷ (Xᘁ ⊗ X) = θ⁻¹ ▷ 𝟙 ≫ (X ◁ η_swap)
```
Mathlib: `whisker_exchange` with f = θ⁻¹, g = η_swap

**5c.** Past ρ⁻¹ (rightUnitor naturality):
```
(ρ_ X).inv ≫ θ⁻¹ ▷ (𝟙_ C) = θ⁻¹ ≫ (ρ_ X).inv
```
Mathlib: derive from `rightUnitor_naturality`: `θ⁻¹ ▷ 𝟙 ≫ ρ = ρ ≫ θ⁻¹`,
then pre-compose with ρ⁻¹ and post-compose with ρ⁻¹.

After step 5:
```
θ⁻¹ ≫ ρ⁻¹ ≫ (X ◁ η_swap) ≫ α⁻¹ ≫ (ε_swap ▷ X) ≫ λ ≫ θ
```

### Step 6: Apply swap pairing zigzag

The swap pairing `ExactPairing Xᘁ X` has zigzag `coevaluation_evaluation`:
```
X ◁ η_swap ≫ (α_ X Xᘁ X).inv ≫ ε_swap ▷ X = (ρ_ X).hom ≫ (λ_ X).inv
```

So the middle part:
```
ρ⁻¹ ≫ (X ◁ η_swap) ≫ α⁻¹ ≫ (ε_swap ▷ X) ≫ λ
= ρ⁻¹ ≫ ρ ≫ λ⁻¹ ≫ λ
= 𝟙
```

**Lean incantation for swap zigzag:**
```lean
letI p_swap : ExactPairing Xᘁ X := BraidedCategory.exactPairing_swap X Xᘁ
have swap_zig := @ExactPairing.coevaluation_evaluation C _ _ Xᘁ X p_swap
```

Note: The `η_swap` and `ε_swap` in the zigzag use the swap instance's coevaluation
and evaluation. To match with our expanded form `η_ X Xᘁ ≫ (β_ Xᘁ X).inv` and
`(β_ X Xᘁ).hom ≫ ε_ X Xᘁ`, we need to unfold the swap pairing's fields.

### Step 7: Cancel θ⁻¹ ≫ θ

```
θ⁻¹ ≫ 𝟙 ≫ θ = θ⁻¹ ≫ θ = 𝟙
```

Mathlib: `Iso.inv_hom_id`

### Key Mathlib lemmas needed

| Lemma | Statement |
|-------|-----------|
| `whiskerLeft_comp` | `X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g` |
| `comp_whiskerRight` | `(f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z` |
| `whisker_exchange` | `W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X' ◁ g` |
| `associator_inv_naturality_left` | α⁻¹ naturality in first component |
| `associator_inv_naturality_right` | α⁻¹ naturality in third component |
| `leftUnitor_naturality` | `(𝟙_ C) ◁ f ≫ λ = λ ≫ f` |
| `rightUnitor_inv_naturality` | `ρ⁻¹ ≫ f ▷ 𝟙 = f ≫ ρ⁻¹` (or derive) |
| `ExactPairing.coevaluation_evaluation` | Y-zigzag identity |
| `drinfeldIsoIso_coeval` | η ≫ Xᘁ ◁ u⁻¹ = η_swap (local) |
| `drinfeldIsoIso_eval` | u ▷ Xᘁ ≫ ε = ε_swap (local) |

### Implementation considerations

1. **Matching swap notation**: After steps 2-3, the η_swap and ε_swap
   terms are in expanded form. When applying the swap zigzag (step 6),
   we need to either:
   - Use `@` syntax with explicit ExactPairing instance, or
   - First fold the expanded terms back into swap notation via `show` or `conv`

2. **Associator naturality names**: Need to verify exact names of
   `associator_inv_naturality_left` and `_right` in current Mathlib.
   Alternative: use `MonoidalCategory.associator_naturality` and derive
   the inverse version.

3. **rightUnitor_inv_naturality**: May not exist directly. Derive from
   `rightUnitor_naturality`: `f ▷ (𝟙_ C) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f`.

4. **The middle part (step 6)**: The cleanest approach may be to
   use `letI` to introduce the swap pairing, then use `have` for the
   zigzag, then rewrite. The challenge is matching the expanded
   `η_ X Xᘁ ≫ (β_ Xᘁ X).inv` with `@η_ Xᘁ X p_swap`.

5. **Alternative for step 6**: Instead of unfolding the swap pairing,
   directly prove the middle identity `ρ⁻¹ ≫ X ◁ (η_ X Xᘁ ≫ (β_ Xᘁ X).inv) ≫
   α⁻¹ ≫ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ▷ X ≫ λ = 𝟙` as a standalone lemma,
   using the private `coevaluation_evaluation_braided'` proof technique
   (Yang-Baxter + braiding naturality). This avoids instance-matching issues.

---

## pivotalIso_leftDuality_dual

### Goal (from Pivotal.lean:91-94)

```lean
(λ_ Xᘁ).inv ≫ (η_ Xᘁ (Xᘁ)ᘁ ▷ Xᘁ) ≫ ((Xᘁ ◁ (pivotalIso X).inv) ▷ Xᘁ) ≫
(α_ Xᘁ X Xᘁ).hom ≫ (Xᘁ ◁ ((pivotalIso X).hom ▷ Xᘁ)) ≫
(Xᘁ ◁ ε_ Xᘁ (Xᘁ)ᘁ) ≫ (ρ_ Xᘁ).hom = 𝟙 Xᘁ
```

### Strategy

Parallel to `pivotalIso_leftDuality`, using the Xᘁ-zigzag instead.

**Step 1-3**: Same expansion and substitution with coeval/eval helpers.

**Step 4-5**: Move θ terms to the outside. This time:
- θ moves to the left past λ⁻¹ (using `leftUnitor_inv_naturality`)
- θ⁻¹ moves to the right past ρ (using `rightUnitor_naturality`)

**Step 6**: Apply swap pairing `evaluation_coevaluation` zigzag:
```
η_swap ▷ Xᘁ ≫ (α_ Xᘁ X Xᘁ).hom ≫ Xᘁ ◁ ε_swap = (λ_ Xᘁ).hom ≫ (ρ_ Xᘁ).inv
```

**Step 7**: Cancel θ ≫ θ⁻¹ = 𝟙.

### Key differences from leftDuality

- Uses `(α_ Xᘁ X Xᘁ).hom` instead of `(α_ X Xᘁ X).inv`
- Needs associator naturality for `.hom` instead of `.inv`
- Uses `evaluation_coevaluation` instead of `coevaluation_evaluation`

---

## toSphericalCategory: ribbon implies spherical

### Goal

```lean
leftTrace f = rightTrace f
```

for all `f : X ⟶ X`.

### Expanding the definitions

From Trace.lean, leftTrace and rightTrace are:

**leftTrace f** (trace using right duality + pivotal iso):
```
η_ Xᘁ (Xᘁ)ᘁ ≫ (Xᘁ ◁ j⁻¹) ≫ (Xᘁ ◁ f) ≫ ... ≫ ε_ X Xᘁ  (schematic)
```

**rightTrace f** (trace using right duality directly):
```
η_ X Xᘁ ≫ (f ▷ Xᘁ) ≫ (j ▷ Xᘁ) ≫ ε_ Xᘁ (Xᘁ)ᘁ  (schematic)
```

### Strategy (EGNO Proposition 8.10.12)

**Key insight**: The `twist_dual` axiom `rightAdjointMate (twist X).hom = (twist Xᘁ).hom`
provides the symmetry between left and right traces.

**Step 1**: Substitute j = θ⁻¹ ≫ u in both traces.

**Step 2**: In rightTrace, use `drinfeldIsoIso_eval` to replace
`u ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ` with `(β_ X Xᘁ).hom ≫ ε_ X Xᘁ`.

**Step 3**: Use braiding naturality to commute θ⁻¹ past braiding.

**Step 4**: Use `twist_dual` to convert θ_X terms to θ_{Xᘁ} terms.

**Step 5**: In leftTrace, use `drinfeldIsoIso_coeval` to replace
`η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ u⁻¹` with `η_ X Xᘁ ≫ (β_ Xᘁ X).inv`.

**Step 6**: Show both traces reduce to the same expression.

### Prerequisite

Must first read the exact definitions of leftTrace and rightTrace from
Trace.lean to get the precise Lean expressions.

---

## twist_unit: θ_𝟙 = id — **PROVED**

The proof uses:
1. `twist_tensor (𝟙_ C) (𝟙_ C)` + `β²_{𝟙,𝟙} = id` gives `θ_{𝟙⊗𝟙} = θ_𝟙 ⊗ θ_𝟙`
2. `twist_naturality (λ_ (𝟙_ C)).hom` gives naturality through left unitor
3. `tensorHom_def'` decomposes the tensor product of twists
4. Idempotent iso argument: θ = θ ∘ θ and θ is iso implies θ = id
