# Proof Ideas: Ribbon.lean

## Status

- `twist_unit` — **PROVED**
- `toPivotalCategory` (hom_inv_id, inv_hom_id) — **PROVED** (via `rightDualIso.symm`)
- `pivotalIso_naturality` — **PROVED** (via drinfeldIsoIso_naturality + twist_naturality)
- `pivotalIso_leftDuality` — **PROVED**
- `pivotalIso_leftDuality_dual` — **PROVED**
- `toSphericalCategory` — IN PROGRESS (detailed proof plan below)

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

## pivotalIso_leftDuality — PROOF IN PROGRESS

### Goal (from Pivotal.lean:79-82)

```lean
(ρ_ X).inv ≫ (X ◁ η_ Xᘁ (Xᘁ)ᘁ) ≫ (X ◁ (Xᘁ ◁ (pivotalIso X).inv)) ≫
(α_ X Xᘁ X).inv ≫ (((pivotalIso X).hom ▷ Xᘁ) ▷ X) ≫
((ε_ Xᘁ (Xᘁ)ᘁ) ▷ X) ≫ (λ_ X).hom = 𝟙 X
```

where `(pivotalIso X).hom = θ⁻¹ ≫ u` and `(pivotalIso X).inv = u⁻¹ ≫ θ`.

### Step 1: Expand j and distribute whiskers — CONFIRMED WORKS

```lean
simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
           whiskerLeft_comp, comp_whiskerRight, Category.assoc]
```

**Confirmed Lean goal state after step 1** (from compilation 2026-02-22):
```lean
(ρ_ X).inv ≫
  X ◁ η_ Xᘁ Xᘁᘁ ≫
    X ◁ Xᘁ ◁ (drinfeldIsoIso X).inv ≫
      X ◁ Xᘁ ◁ (twist X).hom ≫
        (α_ X Xᘁ X).inv ≫
          (twist X).inv ▷ Xᘁ ▷ X ≫
            (drinfeldIsoIso X).hom ▷ Xᘁ ▷ X ≫
              ε_ Xᘁ Xᘁᘁ ▷ X ≫
                (λ_ X).hom = 𝟙 X
```

Notes on Lean notation:
- `X ◁ Xᘁ ◁ f` means `X ◁ (Xᘁ ◁ f)` (left-whiskering associates right)
- `f ▷ Xᘁ ▷ X` means `(f ▷ Xᘁ) ▷ X` (right-whiskering associates left)
- The simp **fully flattened** the expression — all whiskers distributed, right-associated

### Step 2: Apply drinfeldIsoIso_coeval

Fold `X ◁ η_ Xᘁ Xᘁᘁ ≫ X ◁ Xᘁ ◁ u⁻¹` into `X ◁ (η ≫ Xᘁ ◁ u⁻¹)` then rewrite.

```lean
rw [← whiskerLeft_comp_assoc, drinfeldIsoIso_coeval]
```

**Expected state after step 2:**
```lean
(ρ_ X).inv ≫
  X ◁ (η_ X Xᘁ ≫ (β_ Xᘁ X).inv) ≫
    X ◁ Xᘁ ◁ (twist X).hom ≫
      (α_ X Xᘁ X).inv ≫
        (twist X).inv ▷ Xᘁ ▷ X ≫
          (drinfeldIsoIso X).hom ▷ Xᘁ ▷ X ≫
            ε_ Xᘁ Xᘁᘁ ▷ X ≫
              (λ_ X).hom = 𝟙 X
```

**ISSUE**: The `← whiskerLeft_comp_assoc` needs the RHS to be in the form
`X ◁ f ≫ X ◁ g ≫ rest`. Since step 1 output is fully right-associated:
`X ◁ η ≫ (X ◁ Xᘁ ◁ u⁻¹ ≫ ...)`, it should match with `f = η` and
`g = Xᘁ ◁ u⁻¹` since `X ◁ Xᘁ ◁ u⁻¹ = X ◁ (Xᘁ ◁ u⁻¹)`.

### Step 3: Apply drinfeldIsoIso_eval

Fold `(drinfeldIsoIso X).hom ▷ Xᘁ ▷ X ≫ ε_ Xᘁ Xᘁᘁ ▷ X` into
`((drinfeldIsoIso X).hom ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ) ▷ X` then rewrite.

```lean
rw [← comp_whiskerRight_assoc, drinfeldIsoIso_eval]
```

**POTENTIAL ISSUE**: `comp_whiskerRight` matches `(f ≫ g) ▷ X = f ▷ X ≫ g ▷ X`.
The backward rewrite `← comp_whiskerRight` matches `f ▷ X ≫ g ▷ X`. But
`(drinfeldIsoIso X).hom ▷ Xᘁ ▷ X` is `((drinfeldIsoIso X).hom ▷ Xᘁ) ▷ X`,
i.e. `f ▷ X` where `f = (drinfeldIsoIso X).hom ▷ Xᘁ`. And `ε_ Xᘁ Xᘁᘁ ▷ X`
is `g ▷ X` where `g = ε_ Xᘁ Xᘁᘁ`. So `← comp_whiskerRight` should fold these
into `(f ≫ g) ▷ X = ((drinfeldIsoIso X).hom ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ) ▷ X`.
Then `drinfeldIsoIso_eval` rewrites the inner part.

BUT: `← comp_whiskerRight_assoc` matches the **first** occurrence of
`f ▷ Z ≫ g ▷ Z ≫ rest`, which might be `(twist X).inv ▷ Xᘁ ▷ X ≫ (drinfeldIsoIso X).hom ▷ Xᘁ ▷ X ≫ rest` instead. Need to check if `▷ Xᘁ ▷ X` is treated
as `(... ▷ Xᘁ) ▷ X`, which means the `▷ X` level has:
- `f ▷ X = (twist X).inv ▷ Xᘁ ▷ X` where `f = (twist X).inv ▷ Xᘁ`
- `g ▷ X = (drinfeldIsoIso X).hom ▷ Xᘁ ▷ X` where `g = (drinfeldIsoIso X).hom ▷ Xᘁ`

So yes, `← comp_whiskerRight` will match the WRONG pair first!

**FIX**: Use `conv_lhs` to navigate to the correct position, or reorder the steps.

**Alternative approach (Step 3 first, then Step 2)**:
If we do the eval rewrite first (before coeval), the first `f ▷ X ≫ g ▷ X`
pair in the fully flattened expression is `(twist X).inv ▷ Xᘁ ▷ X ≫ (drinfeldIsoIso X).hom ▷ Xᘁ ▷ X`
which is still the wrong pair.

**FIX OPTION 1**: Use `conv` to navigate past θ⁻¹:
```lean
conv_lhs =>
  rw [show ... from ← comp_whiskerRight ...]
```

**FIX OPTION 2**: First move θ⁻¹ out of the way (step 5a), then the eval pair
becomes the first `f ▷ X ≫ g ▷ X`.

**FIX OPTION 3**: Use a helper lemma that combines steps 2-3:
```lean
private lemma coeval_eval_swap (X : C) :
    X ◁ η_ Xᘁ Xᘁᘁ ≫ X ◁ Xᘁ ◁ (drinfeldIsoIso X).inv ≫ ... = ...
```

**FIX OPTION 4 (simplest)**: Use `slice_lhs` to target specific positions:
```lean
slice_lhs 6 7 => rw [← comp_whiskerRight, drinfeldIsoIso_eval]
```
(Need to verify the correct position numbers.)

### Step 4: Move θ to the far right

After steps 2-3, need to move `X ◁ Xᘁ ◁ (twist X).hom` past everything to the right.

**4a.** Past α⁻¹: `associator_inv_naturality_right_assoc`
**4b.** Past `(θ⁻¹ ▷ Xᘁ) ▷ X`: `whisker_exchange_assoc`
**4c.** Past eval terms: `whisker_exchange_assoc`
**4d.** Past λ: `leftUnitor_naturality`

### Step 5: Move θ⁻¹ to the far left

**5a.** Past α⁻¹: `← associator_inv_naturality_left_assoc`
  Note: This rewrites `α⁻¹ ≫ (θ⁻¹ ▷ Xᘁ) ▷ X` into `θ⁻¹ ▷ (Xᘁ ⊗ X) ≫ α⁻¹`
  Wait — actually `associator_inv_naturality_left` may have form:
  `(f ▷ Y) ▷ Z ≫ (α_ ...).inv = (α_ ...).inv ≫ f ▷ (Y ⊗ Z)`
  So the backward rewrite `← ...` gives: `(α_ ...).inv ≫ f ▷ (Y ⊗ Z) → (f ▷ Y) ▷ Z ≫ (α_ ...).inv`
  That's the WRONG direction. We want: `(α_ ...).inv ≫ (f ▷ Y) ▷ Z → f ▷ (Y ⊗ Z) ≫ (α_ ...).inv`

  NEED TO CHECK: What is the exact statement of `associator_inv_naturality_left`?
  From previous research: `f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ (f ▷ Y) ▷ Z`
  So backward: `(α_ X Y Z).inv ≫ (f ▷ Y) ▷ Z = f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv` ✓

**5b.** Past η_swap terms: `whisker_exchange_assoc`
**5c.** Past ρ⁻¹: `← rightUnitor_inv_naturality_assoc`

### Step 6: Apply swap pairing zigzag

After steps 4-5, the expression should be:
```
θ⁻¹ ≫ ρ⁻¹ ≫ X ◁ η_swap ≫ α⁻¹ ≫ ε_swap ▷ X ≫ λ ≫ θ
```

The middle part `ρ⁻¹ ≫ X ◁ η_swap ≫ α⁻¹ ≫ ε_swap ▷ X ≫ λ` should equal `𝟙`
by the swap zigzag identity.

**KEY CHALLENGE**: The swap zigzag uses `@η_` and `@ε_` with the swap pairing instance.
Need to match these with the expanded forms `η_ X Xᘁ ≫ (β_ Xᘁ X).inv` and
`(β_ X Xᘁ).hom ≫ ε_ X Xᘁ`.

**Approach**: Prove a helper lemma `swap_zigzag_expanded` that states the zigzag
directly in terms of the standard pairing + braiding:
```lean
private lemma swap_coevaluation_evaluation (X : C) :
    X ◁ (η_ X Xᘁ ≫ (β_ Xᘁ X).inv) ≫
    (α_ X Xᘁ X).inv ≫
    ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ▷ X =
    (ρ_ X).hom ≫ (λ_ X).inv := by
  letI : ExactPairing Xᘁ X := BraidedCategory.exactPairing_swap X Xᘁ
  exact @ExactPairing.coevaluation_evaluation' C _ _ Xᘁ X this
```

### Step 7: Cancel θ⁻¹ ≫ 𝟙 ≫ θ = 𝟙

```lean
simp [Iso.inv_hom_id]
```

### Draft Lean proof (untested)

```lean
pivotalIso_leftDuality X := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
             whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  -- Fold coeval pair
  rw [← whiskerLeft_comp_assoc, drinfeldIsoIso_coeval]
  -- Distribute X ◁ (η ≫ β⁻¹) back out
  simp only [whiskerLeft_comp, Category.assoc]
  -- Fold eval pair (need to skip past θ⁻¹ ▷ Xᘁ ▷ X)
  slice_lhs 6 7 => rw [← comp_whiskerRight, drinfeldIsoIso_eval]
  simp only [comp_whiskerRight, Category.assoc]
  -- Move θ to far right
  rw [associator_inv_naturality_right_assoc]  -- past α⁻¹
  rw [whisker_exchange_assoc]                  -- past θ⁻¹ ▷ Xᘁ ▷ X
  rw [whisker_exchange_assoc]                  -- past (β_ X Xᘁ).hom ▷ X
  rw [whisker_exchange_assoc]                  -- past (ε_ X Xᘁ) ▷ X
  rw [leftUnitor_naturality]                   -- past λ
  simp only [Category.assoc]
  -- Move θ⁻¹ to far left
  rw [← associator_inv_naturality_left_assoc]  -- past α⁻¹
  rw [whisker_exchange_assoc]                   -- past X ◁ (β_ Xᘁ X).inv
  rw [whisker_exchange_assoc]                   -- past X ◁ η_ X Xᘁ
  rw [← rightUnitor_inv_naturality_assoc]       -- past ρ⁻¹
  -- Now: θ⁻¹ ≫ ρ⁻¹ ≫ X ◁ η_swap ≫ α⁻¹ ≫ ε_swap ▷ X ≫ λ ≫ θ = 𝟙
  -- Apply swap zigzag...
  sorry
```

### Key Mathlib lemmas needed

| Lemma | Statement |
|-------|-----------|
| `whiskerLeft_comp` | `X ◁ (f ≫ g) = X ◁ f ≫ X ◁ g` |
| `comp_whiskerRight` | `(f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z` |
| `whisker_exchange` | `W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X' ◁ g` |
| `associator_inv_naturality_left` | `f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ (f ▷ Y) ▷ Z` |
| `associator_inv_naturality_right` | `(X ⊗ Y) ◁ f ≫ (α_ X Y Z').inv = (α_ X Y Z).inv ≫ X ◁ (Y ◁ f)` |
| `leftUnitor_naturality` | `(𝟙_ C) ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f` |
| `rightUnitor_inv_naturality` | `f ▷ (𝟙_ C) ≫ (ρ_ Y).inv = (ρ_ X).inv ≫ ...` (need to check) |
| `ExactPairing.coevaluation_evaluation'` | Y-zigzag identity |
| `drinfeldIsoIso_coeval` | `η ≫ Xᘁ ◁ u⁻¹ = η_ X Xᘁ ≫ (β_ Xᘁ X).inv` (local) |
| `drinfeldIsoIso_eval` | `u ▷ Xᘁ ≫ ε = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ` (local) |

### Implementation risks & open questions

1. **`slice_lhs` availability**: Need `import Mathlib.Tactic.CategoryTheory.Slice`
   or it may already be available via CoherenceLemmas. Alternatively, use `conv`.

2. **`whisker_exchange` direction**: The lemma is `f ▷ Y ≫ X' ◁ g = W ◁ g ≫ f ▷ Z`.
   When moving θ right, we use the backward direction (fold `f ▷ ... ≫ ... ◁ θ`
   back and pull θ to the right). Need to check exact direction carefully.

3. **`rightUnitor_inv_naturality`**: May not exist. Alternative: derive from
   `rightUnitor_naturality : f ▷ (𝟙_ C) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f`.
   Use `Iso.comp_inv_eq` or `cancel_mono` to get the inverse version.

4. **Swap zigzag matching**: The most delicate step. The expanded forms
   `η_ X Xᘁ ≫ (β_ Xᘁ X).inv` and `(β_ X Xᘁ).hom ≫ ε_ X Xᘁ` need to match
   the swap pairing's `η_` and `ε_`. A helper lemma is likely the cleanest approach.

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

## toSphericalCategory: ribbon implies spherical — IN PROGRESS

### Goal

```lean
leftTrace f = rightTrace f
```

for all `f : X ⟶ X`.

### Exact Lean definitions (from Trace.lean)

**leftTrace f** =
```lean
η_ Xᘁ (Xᘁ)ᘁ ≫ (Xᘁ ◁ (PivotalCategory.pivotalIso X).inv) ≫
  (Xᘁ ◁ f) ≫ ε_ X Xᘁ
```

**rightTrace f** =
```lean
η_ X Xᘁ ≫ (f ▷ Xᘁ) ≫ ((PivotalCategory.pivotalIso X).hom ▷ Xᘁ) ≫
  ε_ Xᘁ (Xᘁ)ᘁ
```

In the ribbon category, `pivotalIso X = (twist X).symm ≪≫ drinfeldIsoIso X`, so:
- `(pivotalIso X).hom = (twist X).inv ≫ (drinfeldIsoIso X).hom`
- `(pivotalIso X).inv = (drinfeldIsoIso X).inv ≫ (twist X).hom`

### After expanding j in both traces

**leftTrace f** =
```
η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ (u⁻¹ ≫ θ) ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ
= η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ u⁻¹ ≫ Xᘁ ◁ θ ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ
```

Apply `drinfeldIsoIso_coeval`:
```
= (η_ X Xᘁ ≫ β⁻¹) ≫ Xᘁ ◁ θ ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ
= η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ θ ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ
```

**rightTrace f** =
```
η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (θ⁻¹ ≫ u) ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ
= η_ X Xᘁ ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ u ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ
```

Apply `drinfeldIsoIso_eval`:
```
= η_ X Xᘁ ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ
```

### Mathlib rightAdjointMate (exact)

```lean
def rightAdjointMate (f : X ⟶ Y) : Yᘁ ⟶ Xᘁ :=
  (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ _ ◁ f ▷ _ ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (λ_ _).hom
```

Key lemmas (all `@[reassoc]`):
```
rightAdjointMate_comp_evaluation (f : X ⟶ Y):
  (fᘁ ▷ X) ≫ ε_ X Xᘁ = (Yᘁ ◁ f) ≫ ε_ Y Yᘁ

coevaluation_comp_rightAdjointMate (f : X ⟶ Y):
  η_ Y Yᘁ ≫ _ ◁ fᘁ = η_ _ _ ≫ f ▷ _

comp_rightAdjointMate (f : X ⟶ Y) (g : Y ⟶ Z):
  (f ≫ g)ᘁ = gᘁ ≫ fᘁ
```

`twist_dual X : rightAdjointMate (twist X).hom = (twist Xᘁ).hom`

### Derived identities from twist_dual

Applying `rightAdjointMate_comp_evaluation` to `(twist X).hom`, using `twist_dual`:
```
θ_{Xᘁ} ▷ X ≫ ε_ X Xᘁ = Xᘁ ◁ θ_X ≫ ε_ X Xᘁ    ... (eval-twist)
```
Applying `coevaluation_comp_rightAdjointMate` to `(twist X).hom`:
```
η_ X Xᘁ ≫ X ◁ θ_{Xᘁ} = η_ X Xᘁ ≫ θ_X ▷ Xᘁ    ... (coeval-twist)
```

### Consolidated proof strategy

After expanding j = θ⁻¹ ≫ u in both traces and applying drinfeldIsoIso helpers:

**LHS** = `η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ θ ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ`
**RHS** = `η_ X Xᘁ ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ`

**RHS manipulation** using `braiding_naturality_left` twice:
`f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom` becomes `(β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ Xᘁ ◁ θ⁻¹`

So: **RHS** = `η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ Xᘁ ◁ θ⁻¹ ≫ ε_ X Xᘁ`

Both now have form: `η ≫ [β-term] ≫ Xᘁ ◁ f ≫ Xᘁ ◁ [twist-term] ≫ ε`

The core equation to prove is:
```
(β_ Xᘁ X).inv ≫ Xᘁ ◁ θ ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ
  = (β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ Xᘁ ◁ θ⁻¹ ≫ ε_ X Xᘁ
```

NOTE: `(β_ Xᘁ X).inv : X ⊗ Xᘁ → Xᘁ ⊗ X` and `(β_ X Xᘁ).hom : X ⊗ Xᘁ → Xᘁ ⊗ X`
have the same type but are NOT equal (unless the category is symmetric).

Using eval-twist identity: `Xᘁ ◁ θ ≫ ε = θ_{Xᘁ} ▷ X ≫ ε`

LHS becomes: `(β_ Xᘁ X).inv ≫ Xᘁ ◁ f ≫ θ_{Xᘁ} ▷ X ≫ ε`
           = `(β_ Xᘁ X).inv ≫ θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ f ≫ ε` (whisker_exchange)
RHS:         `(β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ Xᘁ ◁ θ⁻¹ ≫ ε`
           = `(β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ (twist Xᘁ).inv ▷ X ≫ ε` (eval-twist for inv)
           = `(β_ X Xᘁ).hom ≫ (twist Xᘁ).inv ▷ X ≫ Xᘁ ◁ f ≫ ε` (whisker_exchange)

So the key is:
```
(β_ Xᘁ X).inv ≫ θ_{Xᘁ} ▷ X = (β_ X Xᘁ).hom ≫ (twist Xᘁ).inv ▷ X   ???
```
i.e., `(β_ Xᘁ X).inv ≫ θ_{Xᘁ} ▷ X ≫ θ_{Xᘁ} ▷ X = (β_ X Xᘁ).hom`?
No: `θ ≫ θ⁻¹ = id`, so `(β_ Xᘁ X).inv = (β_ X Xᘁ).hom ≫ (twist Xᘁ).inv ▷ X ≫ (twist Xᘁ).inv ▷ X`?
That's `β = β⁻¹ ≫ θ² ▷ X`. This doesn't look right.

Actually: we need
`(β_ Xᘁ X).inv ≫ θ_{Xᘁ} ▷ X = (β_ X Xᘁ).hom ≫ (twist Xᘁ).inv ▷ X`

i.e., `(β_ X Xᘁ).hom⁻¹ ≫ (β_ Xᘁ X).inv = (twist Xᘁ).inv ▷ X ≫ (θ_{Xᘁ} ▷ X)⁻¹`
i.e., `(β_ Xᘁ X).hom ≫ (β_ Xᘁ X).inv = θ_{Xᘁ}⁻¹ ▷ X ≫ θ_{Xᘁ}⁻¹ ▷ X`???
No, this is getting confused. Let me think differently.

The equation `(β_ Xᘁ X).inv ≫ θ_{Xᘁ} ▷ X = (β_ X Xᘁ).hom ≫ (twist Xᘁ).inv ▷ X`
rearranges to:
`θ_{Xᘁ} ▷ X ≫ (twist Xᘁ).hom ▷ X = (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom`
i.e., `(θ² _{Xᘁ}) ▷ X = monodromy(Xᘁ, X)`

This looks like it could follow from `twist_tensor` applied to Xᘁ and X!
`θ_{Xᘁ ⊗ X} = (θ_{Xᘁ} ⊗ θ_X) ≫ β_{Xᘁ,X} ≫ β_{X,Xᘁ}`

**TODO**: Verify this approach — it connects to monodromy_eq_twist_ratio!

### Confirmed Lean goal (after drinfeldIso expansion, 2026-02-22)

```lean
⊢ η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ (twist X).hom ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ =
    η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (twist X).inv ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ
```

### Key helper lemma needed

If we can prove:
```
(β_ Xᘁ X).inv ≫ Xᘁ ◁ (twist X).hom = (twist X).inv ▷ Xᘁ ≫ (β_ X Xᘁ).hom
```
then the proof of spherical follows by naturality of the braiding + twist_naturality.

Proof sketch using helper:
1. Rewrite LHS middle with helper: `β⁻¹ ≫ Xᘁ ◁ θ = θ⁻¹ ▷ Xᘁ ≫ β`
2. Now LHS = `η ≫ θ⁻¹ ▷ Xᘁ ≫ β ≫ Xᘁ ◁ f ≫ ε`
3. Use braiding_naturality_left (backward): `β ≫ Xᘁ ◁ f = f ▷ Xᘁ ≫ β`
4. LHS = `η ≫ θ⁻¹ ▷ Xᘁ ≫ f ▷ Xᘁ ≫ β ≫ ε`
5. Use twist_naturality: `θ⁻¹ ≫ f = f ≫ θ⁻¹`, so `θ⁻¹ ▷ Xᘁ ≫ f ▷ Xᘁ = f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ`
6. LHS = `η ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ β ≫ ε` = RHS ✓

### Proving the helper lemma

The equation `(β_ Xᘁ X).inv ≫ Xᘁ ◁ θ = θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom`
is about `X ⊗ Xᘁ → Xᘁ ⊗ X`.

This can be rearranged to:
`(β_ X Xᘁ).hom⁻¹ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ θ = θ⁻¹ ▷ Xᘁ`

where `(β_ X Xᘁ).hom⁻¹ = (β_ X Xᘁ).inv`.

Or equivalently: `(β_ Xᘁ X).inv ≫ Xᘁ ◁ θ ≫ (β_ X Xᘁ).inv = θ⁻¹ ▷ Xᘁ`

TODO: think about how to prove this from the ribbon axioms.

### OLDER exploration (Strategy B): Use rightAdjointMate to convert between traces

The `rightAdjointMate` operation converts:
```
rightAdjointMate_comp_evaluation: fᘁ ▷ X ≫ ε = Yᘁ ◁ f ≫ ε
```
and
```
coevaluation_comp_rightAdjointMate: η ≫ Y ◁ fᘁ = η ≫ f ▷ Xᘁ
```

Key observation: `twist_dual` says `(θ_X)ᘁ = θ_{Xᘁ}`, i.e.,
`rightAdjointMate (twist X).hom = (twist Xᘁ).hom`.

From `rightAdjointMate_comp_evaluation`:
```
(θ_X)ᘁ ▷ X ≫ ε_ X Xᘁ = Xᘁ ◁ θ_X ≫ ε_ X Xᘁ
```
So: `θ_{Xᘁ} ▷ X ≫ ε_ X Xᘁ = Xᘁ ◁ θ_X ≫ ε_ X Xᘁ`

Similarly from `coevaluation_comp_rightAdjointMate`:
```
η_ X Xᘁ ≫ X ◁ (θ_X)ᘁ = η_ X Xᘁ ≫ θ_X ▷ Xᘁ
```
So: `η_ X Xᘁ ≫ X ◁ θ_{Xᘁ} = η_ X Xᘁ ≫ θ_X ▷ Xᘁ`

These are KEY IDENTITIES. They let us convert between "θ acting on dual via whiskering"
and "θ acting on primal via whiskering".

### Strategy C (most promising): Rewrite LHS to match RHS step by step

**LHS** (leftTrace f expanded):
```
η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ θ ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ
```

Step 1: Use `rightAdjointMate_comp_evaluation` with `twist_dual`:
```
Xᘁ ◁ θ_X ≫ ε_ X Xᘁ = θ_{Xᘁ} ▷ X ≫ ε_ X Xᘁ
```
(Note: `rightAdjointMate_comp_evaluation` says `fᘁ ▷ X ≫ ε = Yᘁ ◁ f ≫ ε`
 for f : X → Y. Applying to f = θ_X : X → X, we get (θ_X)ᘁ ▷ X ≫ ε = Xᘁ ◁ θ_X ≫ ε.
 By twist_dual, (θ_X)ᘁ = θ_{Xᘁ}.)

So LHS becomes:
```
η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ f ≫ θ_{Xᘁ} ▷ X ≫ ε_ X Xᘁ
```
Wait, that's wrong — Xᘁ ◁ θ and Xᘁ ◁ f don't commute in general.

Actually the trace has `Xᘁ ◁ θ ≫ Xᘁ ◁ f`. We need to use the identity on
`Xᘁ ◁ (θ ≫ f) ≫ ε_ X Xᘁ`. But `rightAdjointMate_comp_evaluation` gives
`(θ ≫ f)ᘁ ▷ X ≫ ε = Xᘁ ◁ (θ ≫ f) ≫ ε`.

Hmm, this only helps if we can simplify `(θ ≫ f)ᘁ`. By `comp_rightAdjointMate`:
`(θ ≫ f)ᘁ = fᘁ ≫ θᘁ = fᘁ ≫ θ_{Xᘁ}`.

So: `Xᘁ ◁ (θ ≫ f) ≫ ε = (fᘁ ≫ θ_{Xᘁ}) ▷ X ≫ ε = fᘁ ▷ X ≫ θ_{Xᘁ} ▷ X ≫ ε`

Actually, let me think more carefully. The substitution for twist_naturality gives
`θ ≫ f = f ≫ θ`, so `Xᘁ ◁ (θ ≫ f) = Xᘁ ◁ (f ≫ θ) = Xᘁ ◁ f ≫ Xᘁ ◁ θ`.

So we can reorder: LHS becomes:
```
η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ f ≫ Xᘁ ◁ θ ≫ ε_ X Xᘁ
```
Then apply the mate identity to the last two terms:
```
= η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ f ≫ θ_{Xᘁ} ▷ X ≫ ε_ X Xᘁ
```
Then use whisker_exchange on `Xᘁ ◁ f ≫ θ_{Xᘁ} ▷ X = θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ f`:
Wait, no. `whisker_exchange` says `f ▷ Y ≫ X ◁ g = X ◁ g ≫ f ▷ Y` (schematic).
Actually it says for `f : W ⟶ X` and `g : Y ⟶ Z`:
`f ▷ Y ≫ X ◁ g = W ◁ g ≫ f ▷ Z`

Hmm, `θ_{Xᘁ} ▷ X` and `Xᘁ ◁ f` — these have types:
- `θ_{Xᘁ} : Xᘁ ⟶ Xᘁ`, so `θ_{Xᘁ} ▷ X : Xᘁ ⊗ X ⟶ Xᘁ ⊗ X`
- `f : X ⟶ X`, so `Xᘁ ◁ f : Xᘁ ⊗ X ⟶ Xᘁ ⊗ X`

`whisker_exchange` (with W=X'=Xᘁ, Y=Z=X): `θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ f = Xᘁ ◁ f ≫ θ_{Xᘁ} ▷ X`

So they DO commute. This means:
```
LHS = η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ
```

Now the RHS is:
```
η_ X Xᘁ ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ
```

Hmm, these look quite different still. LHS has `β⁻¹ ≫ θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ f ≫ ε`
while RHS has `f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ β ≫ ε`.

Using braiding naturality on LHS to move β⁻¹ past θ_{Xᘁ} ▷ X:
`(β_ Xᘁ X).inv ≫ θ_{Xᘁ} ▷ X = Xᘁ ◁ θ_{Xᘁ}... ` no wait, braiding naturality
involves swapping the object positions.

`braiding_naturality_left`: `f ▷ Y ≫ (β_ X' Y).hom = (β_ X Y).hom ≫ Y ◁ f`
So for `θ_{Xᘁ} ▷ X ≫ (β_ Xᘁ X).hom = (β_ Xᘁ X).hom ≫ X ◁ θ_{Xᘁ}`.
Backward: `(β_ Xᘁ X).inv ≫ θ_{Xᘁ} ▷ X = X ◁ θ_{Xᘁ} ≫ (β_ Xᘁ X).inv`
Wait, we need the inv version. Let me think...

`(β_ Xᘁ X).hom : Xᘁ ⊗ X → X ⊗ Xᘁ`
`(β_ Xᘁ X).inv : X ⊗ Xᘁ → Xᘁ ⊗ X`

So `(β_ Xᘁ X).inv` goes FROM X ⊗ Xᘁ TO Xᘁ ⊗ X.

Actually I realize the analysis is getting complex. Let me just document what I have
and note the open questions.

### Actual Lean goal at step 4 failure (2026-02-22 compilation)

After steps 1-3 + mate_eval, step 4 `braiding_inv_naturality_right` moved θ_{Xᘁ} to
the LEFT of β⁻¹ as `X ◁ (twist Xᘁ).hom`, giving:

```lean
η_ X Xᘁ ≫ f ▷ Xᘁ ≫ X ◁ (twist Xᘁ).hom ≫ (β_ Xᘁ X).inv ≫ ε_ X Xᘁ =
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (twist X).inv ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ
```

After canceling common prefix `η ≫ f ▷ Xᘁ`, need:
```
X ◁ (twist Xᘁ).hom ≫ (β_ Xᘁ X).inv ≫ ε_ X Xᘁ =
  (twist X).inv ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ
```

### NEW APPROACH (2026-02-22): Use mate_coeval on LHS

On LHS, use mate_coeval BACKWARDS to replace `X ◁ (twist Xᘁ).hom` with `(twist X).hom ▷ Xᘁ`
after η. But we're not directly after η — we have `f ▷ Xᘁ` in between.

Wait: whisker_exchange gives `f ▷ Xᘁ ≫ X ◁ θ_{Xᘁ} = X ◁ θ_{Xᘁ} ≫ f ▷ Xᘁ`?
No! whisker_exchange: `f ▷ Y ≫ X' ◁ g = W ◁ g ≫ f ▷ Z`.
Here f : X → X, g : Xᘁ → Xᘁ, so: `f ▷ Xᘁ ≫ X ◁ θ_{Xᘁ} = X ◁ θ_{Xᘁ} ≫ f ▷ Xᘁ`. YES they commute!

So: swap them: `η ≫ X ◁ θ_{Xᘁ} ≫ f ▷ Xᘁ ≫ β⁻¹ ≫ ε`
Then use mate_coeval: `η ≫ X ◁ θ_{Xᘁ} = η ≫ θ_X ▷ Xᘁ`
So LHS = `η ≫ θ_X ▷ Xᘁ ≫ f ▷ Xᘁ ≫ β⁻¹ ≫ ε`
By twist_naturality on f: `θ ≫ f = f ≫ θ`, so `θ ▷ Xᘁ ≫ f ▷ Xᘁ = (θ ≫ f) ▷ Xᘁ = (f ≫ θ) ▷ Xᘁ = f ▷ Xᘁ ≫ θ ▷ Xᘁ`
So LHS = `η ≫ f ▷ Xᘁ ≫ θ ▷ Xᘁ ≫ β⁻¹ ≫ ε`

RHS = `η ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ β ≫ ε`

So need: `θ ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε = θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε`

This is `coeval_twist_braiding` again (but at the eval end). As noted, this requires θ⁴=id.

### TRULY NEW APPROACH: Don't use mate_eval at step 3

Go back to the confirmed goal after steps 1-2:
```
η ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ θ ≫ Xᘁ ◁ f ≫ ε = η ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ β ≫ ε
```

Instead of converting Xᘁ ◁ θ via mate, use BRAIDING NATURALITY DIRECTLY.

`braiding_inv_naturality_left`: for g : X → X', `g ▷ Y ≫ (β_ X' Y).hom = (β_ X Y).hom ≫ Y ◁ g`
inv version: `(β_ X' Y).inv ≫ g ▷ Y = Y ◁ g ≫ (β_ X Y).inv`

Wait, let me check: what about `(β_ Xᘁ X).inv ≫ Xᘁ ◁ θ`?
`(β_ Xᘁ X).inv : X ⊗ Xᘁ → Xᘁ ⊗ X`
`Xᘁ ◁ θ : Xᘁ ⊗ X → Xᘁ ⊗ X`

braiding_inv_naturality_right for g : Y → Y':
`X ◁ g ≫ (β_ X Y').hom = (β_ X Y).hom ≫ g ▷ X`
inv version: `(β_ X Y').inv ≫ X ◁ g = g ▷ X ≫ (β_ X Y).inv`

With X=Xᘁ, Y=Y'=X, g=θ:
`(β_ Xᘁ X).inv ≫ Xᘁ ◁ θ = θ ▷ Xᘁ ≫ (β_ Xᘁ X).inv`

YES! This just moves θ across β⁻¹ without changing its whisker side!
So LHS becomes: `η ≫ θ ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ f ≫ ε`

Then similarly move f: `(β_ Xᘁ X).inv ≫ Xᘁ ◁ f = f ▷ Xᘁ ≫ (β_ Xᘁ X).inv`
LHS = `η ≫ θ ▷ Xᘁ ≫ f ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε`
By twist_naturality: `θ ▷ Xᘁ ≫ f ▷ Xᘁ = f ▷ Xᘁ ≫ θ ▷ Xᘁ`
LHS = `η ≫ f ▷ Xᘁ ≫ θ ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε`

RHS = `η ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε`

Cancel common prefix `η ≫ f ▷ Xᘁ`, need:
```
θ ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε_ X Xᘁ = θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ
```

Multiply both sides on the left by θ⁻¹ ▷ Xᘁ:
```
θ² ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε = (β_ X Xᘁ).hom ≫ ε
```

i.e., `θ² ▷ Xᘁ ≫ β⁻¹_{Xᘁ,X} ≫ ε = β_{X,Xᘁ} ≫ ε`

This is exactly `coeval_twist_braiding` again (renamed). It's provable from twist_tensor!

### Proving θ² ▷ Xᘁ ≫ β⁻¹ ≫ ε = β ≫ ε (THE KEY IDENTITY)

From twist_naturality on ε : Xᘁ ⊗ X → 𝟙:
`ε ≫ θ_𝟙 = θ_{Xᘁ⊗X} ≫ ε`, and θ_𝟙 = id, so `ε = θ_{Xᘁ⊗X} ≫ ε`.

Expand twist_tensor on Xᘁ, X:
`θ_{Xᘁ⊗X} = (θ_{Xᘁ} ⊗ₘ θ_X) ≫ β_{Xᘁ,X} ≫ β_{X,Xᘁ}`

So: `(θ_{Xᘁ} ⊗ₘ θ_X) ≫ β_{Xᘁ,X} ≫ β_{X,Xᘁ} ≫ ε = ε`   ... (*)

Now `θ_{Xᘁ} ⊗ₘ θ_X = θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ_X` (tensorHom_def)

By mate identity: `Xᘁ ◁ θ_X ≫ ε = θ_{Xᘁ} ▷ X ≫ ε`

So we need to carefully sequence the calculation. Let's go from (*):
```
θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ_X ≫ β_{Xᘁ,X} ≫ β_{X,Xᘁ} ≫ ε = ε
```

Use braiding_naturality_right (for `θ_X : X → X`):
`Xᘁ ◁ θ_X ≫ (β_ Xᘁ X).hom = (β_ Xᘁ X).hom ≫ θ_X ▷ Xᘁ`

So: `θ_{Xᘁ} ▷ X ≫ (β_ Xᘁ X).hom ≫ θ_X ▷ Xᘁ ≫ β_{X,Xᘁ} ≫ ε = ε`

Use braiding_naturality_left (for `θ_X : X → X`):
`θ_X ▷ Xᘁ ≫ (β_ X Xᘁ).hom = (β_ X Xᘁ).hom ≫ Xᘁ ◁ θ_X`

Wait, that's .hom. We have β_{X,Xᘁ}.hom composed with ε.
Actually β_{X,Xᘁ} goes X ⊗ Xᘁ → Xᘁ ⊗ X. Then ε : Xᘁ ⊗ X → 𝟙.

So: `θ_{Xᘁ} ▷ X ≫ (β_ Xᘁ X).hom ≫ θ_X ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε = ε`

Now use braiding_naturality_left for θ_X in the second β:
`θ_X ▷ Xᘁ ≫ (β_ X Xᘁ).hom = (β_ X Xᘁ).hom ≫ Xᘁ ◁ θ_X`

So: `θ_{Xᘁ} ▷ X ≫ (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ θ_X ≫ ε = ε`

Use mate identity: `Xᘁ ◁ θ_X ≫ ε = θ_{Xᘁ} ▷ X ≫ ε`

So: `θ_{Xᘁ} ▷ X ≫ β ≫ β' ≫ θ_{Xᘁ} ▷ X ≫ ε = ε`

Hmm... `β ≫ β'` is `(β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom`. But:
- `(β_ Xᘁ X).hom : Xᘁ ⊗ X → X ⊗ Xᘁ`
- `(β_ X Xᘁ).hom : X ⊗ Xᘁ → Xᘁ ⊗ X`

So β ≫ β' = `(β_ X Xᘁ).inv ≫ ... ` no, `(β_ Xᘁ X).hom` then `(β_ X Xᘁ).hom`.
That's monodromy(Xᘁ, X).

Actually let me use braiding_naturality_left on θ_{Xᘁ} for the first β:
`θ_{Xᘁ} ▷ X ≫ (β_ Xᘁ X).hom = (β_ Xᘁ X).hom ≫ X ◁ θ_{Xᘁ}`

So: `(β_ Xᘁ X).hom ≫ X ◁ θ_{Xᘁ} ≫ (β_ X Xᘁ).hom ≫ θ_{Xᘁ} ▷ X ≫ ε = ε`

Use braiding_naturality_right for θ_{Xᘁ} in the second β:
Hmm, `X ◁ θ_{Xᘁ} ≫ (β_ X Xᘁ).hom`:
braiding_naturality_right: `X ◁ g ≫ (β_ X Y').hom = (β_ X Y).hom ≫ g ▷ X`
With g = θ_{Xᘁ}: `X ◁ θ_{Xᘁ} ≫ (β_ X Xᘁ).hom = (β_ X Xᘁ).hom ≫ θ_{Xᘁ} ▷ X`

So: `(β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ θ_{Xᘁ} ▷ X ≫ θ_{Xᘁ} ▷ X ≫ ε = ε`

i.e., `monodromy(Xᘁ,X) ≫ (θ_{Xᘁ})² ▷ X ≫ ε = ε`

Now use mate identity twice: `θ_{Xᘁ} ▷ X ≫ ε = Xᘁ ◁ θ_X ≫ ε`

Actually we can't directly use mate on `(θ_{Xᘁ})² ▷ X ≫ ε`. We'd need:
`(θ_{Xᘁ})² ▷ X ≫ ε = θ_{Xᘁ} ▷ X ≫ θ_{Xᘁ} ▷ X ≫ ε = θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ ≫ ε`

Hmm, let me try to get the identity we actually need.

We want: `θ² ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε = (β_ X Xᘁ).hom ≫ ε`
(i.e., θ_X² ▷ Xᘁ, where the β, ε are evaluated at Xᘁ ⊗ X → 𝟙)

Wait: `(β_ Xᘁ X).inv : X ⊗ Xᘁ → Xᘁ ⊗ X`, then ε : Xᘁ ⊗ X → 𝟙.
And `(β_ X Xᘁ).hom : X ⊗ Xᘁ → Xᘁ ⊗ X`, then ε.

So both `(β_ Xᘁ X).inv` and `(β_ X Xᘁ).hom` are X ⊗ Xᘁ → Xᘁ ⊗ X.
And θ² ▷ Xᘁ : X ⊗ Xᘁ → X ⊗ Xᘁ.

From (*): `(θ_{Xᘁ} ⊗ₘ θ_X) ≫ (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε = ε`

So: `(β_ X Xᘁ).hom ≫ ε = ((β_ Xᘁ X).hom)⁻¹ ≫ (θ_{Xᘁ} ⊗ₘ θ_X)⁻¹ ≫ ε`
  = `(β_ Xᘁ X).inv ≫ (θ_{Xᘁ}⁻¹ ⊗ₘ θ_X⁻¹) ≫ ε`

We want: `θ² ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε = (β_ X Xᘁ).hom ≫ ε`
  = `θ² ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε = (β_ Xᘁ X).inv ≫ (θ_{Xᘁ}⁻¹ ⊗ₘ θ_X⁻¹) ≫ ε`

Cancel (β_ Xᘁ X).inv (it's iso):
`θ² ▷ Xᘁ ≫ ε = (θ_{Xᘁ}⁻¹ ⊗ₘ θ_X⁻¹) ≫ ε`
= `(θ_{Xᘁ}⁻¹ ▷ X ≫ Xᘁ ◁ θ_X⁻¹) ≫ ε`  (tensorHom_def)
= `θ_{Xᘁ}⁻¹ ▷ X ≫ Xᘁ ◁ θ_X⁻¹ ≫ ε`

Wait NO. The β⁻¹ is in front of θ² on LHS but in front of θ⁻¹⊗θ⁻¹ on RHS.
I can't cancel β⁻¹ like that because θ² is on the LEFT of β⁻¹.

Let me redo. From (*):
`(θ_{Xᘁ} ⊗ₘ θ_X) ≫ (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε = ε`

Rearranging: `(β_ X Xᘁ).hom ≫ ε = (β_ Xᘁ X).hom⁻¹ ≫ (θ_{Xᘁ} ⊗ₘ θ_X)⁻¹ ≫ ε`
`(β_ X Xᘁ).hom ≫ ε = (β_ Xᘁ X).inv ≫ (θ_{Xᘁ}⁻¹ ⊗ₘ θ_X⁻¹) ≫ ε`

Now expand `(θ_{Xᘁ}⁻¹ ⊗ₘ θ_X⁻¹) = θ_{Xᘁ}⁻¹ ▷ X ≫ Xᘁ ◁ θ_X⁻¹`:
`(β_ X Xᘁ).hom ≫ ε = (β_ Xᘁ X).inv ≫ θ_{Xᘁ}⁻¹ ▷ X ≫ Xᘁ ◁ θ_X⁻¹ ≫ ε`

Using mate identity: `Xᘁ ◁ θ_X⁻¹ ≫ ε = θ_{Xᘁ}⁻¹ ▷ X ≫ ε`
(mate for θ_X⁻¹: rightAdjointMate θ_X⁻¹ = (twist_dual for inv))

Actually: twist_dual says rightAdjointMate θ_X = θ_{Xᘁ}.
For the inverse: rightAdjointMate θ_X⁻¹ = (θ_X⁻¹)ᘁ.
By comp_rightAdjointMate: (θ ≫ θ⁻¹)ᘁ = (θ⁻¹)ᘁ ≫ θᘁ = id.
So (θ⁻¹)ᘁ = (θᘁ)⁻¹ = θ_{Xᘁ}⁻¹.

So: `Xᘁ ◁ θ_X⁻¹ ≫ ε = θ_{Xᘁ}⁻¹ ▷ X ≫ ε`  ✓

Then: `(β_ X Xᘁ).hom ≫ ε = (β_ Xᘁ X).inv ≫ (θ_{Xᘁ}⁻¹)² ▷ X ≫ ε`

And we want: `θ_X² ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε = (β_ X Xᘁ).hom ≫ ε`

So we need: `θ_X² ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε = (β_ Xᘁ X).inv ≫ (θ_{Xᘁ}⁻¹)² ▷ X ≫ ε`

This would require: `θ_X² ▷ Xᘁ ≫ (β_ Xᘁ X).inv = (β_ Xᘁ X).inv ≫ (θ_{Xᘁ}⁻¹)² ▷ X`

Using braiding_inv_naturality to move θ² past β⁻¹:
`(β_ Xᘁ X).inv ≫ Xᘁ ◁ θ² = θ² ▷ Xᘁ ≫ (β_ Xᘁ X).inv` (from braiding_inv_naturality_right)

Wait NO. braiding_inv_naturality_right: `(β_ X Y').inv ≫ X ◁ g = g ▷ X ≫ (β_ X Y).inv`
With X=Xᘁ, g = θ_X²: `(β_ Xᘁ X).inv ≫ Xᘁ ◁ θ² = θ² ▷ Xᘁ ≫ (β_ Xᘁ X).inv`
Hmm wait, Y = Y' = X since θ² : X → X.
So: `θ² ▷ Xᘁ ≫ (β_ Xᘁ X).inv = (β_ Xᘁ X).inv ≫ Xᘁ ◁ θ²`

But we need the RHS to have `(θ_{Xᘁ}⁻¹)² ▷ X`, not `Xᘁ ◁ θ²`.

Hmm... These are different types entirely: `Xᘁ ◁ θ² : Xᘁ ⊗ X → Xᘁ ⊗ X` vs
`(θ_{Xᘁ}⁻¹)² ▷ X : Xᘁ ⊗ X → Xᘁ ⊗ X`. Same type!

We need: `Xᘁ ◁ θ² ≫ ε = (θ_{Xᘁ}⁻¹)² ▷ X ≫ ε`

By mate identity applied twice:
`Xᘁ ◁ θ ≫ ε = θ_{Xᘁ} ▷ X ≫ ε` (NOT θ_{Xᘁ}⁻¹)

So: `Xᘁ ◁ θ² ≫ ε = Xᘁ ◁ θ ≫ Xᘁ ◁ θ ≫ ε = Xᘁ ◁ θ ≫ θ_{Xᘁ} ▷ X ≫ ε`
  = (whisker_exchange) `θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ ≫ ε = θ_{Xᘁ} ▷ X ≫ θ_{Xᘁ} ▷ X ≫ ε`
  = `(θ_{Xᘁ})² ▷ X ≫ ε`

But we need `(θ_{Xᘁ}⁻¹)² ▷ X ≫ ε`, not `(θ_{Xᘁ})² ▷ X ≫ ε`.
So `θ² ≠ θ⁻²` unless θ⁴ = id.

THIS CONFIRMS: the approach via just twist_tensor on ε requires θ⁴=id.

### FUNDAMENTAL INSIGHT: We need BOTH η and ε simultaneously

The equation `η ≫ f ▷ Xᘁ ≫ θ ▷ Xᘁ ≫ β⁻¹ ≫ ε = η ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ β ≫ ε`
has `f ▷ Xᘁ` in the middle. This is NOT a scalar equation unless f = id.

For f = id, we need: `η ≫ θ ▷ Xᘁ ≫ β⁻¹ ≫ ε = η ≫ θ⁻¹ ▷ Xᘁ ≫ β ≫ ε`

From twist_tensor on η: `η = η ≫ θ_{X⊗Xᘁ}`
  = `η ≫ (θ_X ⊗ₘ θ_{Xᘁ}) ≫ β_{X,Xᘁ} ≫ β_{Xᘁ,X}`

Using mate_coeval: `η ≫ X ◁ θ_{Xᘁ} = η ≫ θ ▷ Xᘁ`
So: `η ≫ (θ ▷ Xᘁ ≫ X ◁ θ_{Xᘁ}) ≫ β ≫ β' = η`
  = `η ≫ (θ ▷ Xᘁ ≫ θ ▷ Xᘁ) ≫ β ≫ β' = η`  (using mate_coeval)
  = `η ≫ θ² ▷ Xᘁ ≫ β ≫ β' = η`

So: `η ≫ θ² ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ (β_ Xᘁ X).hom = η`   ... (coeval_identity)

From twist_tensor on ε: `θ_{Xᘁ⊗X} ≫ ε = ε`
  = `(θ_{Xᘁ} ⊗ₘ θ_X) ≫ β_{Xᘁ,X} ≫ β_{X,Xᘁ} ≫ ε = ε`

Using mate: θ_{Xᘁ} ⊗ₘ θ_X = θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ
  = θ_{Xᘁ} ▷ X ≫ θ_{Xᘁ} ▷ X (after composition with ε? NO — only after ε)

Actually, let's use braiding naturality instead:
`(θ_{Xᘁ} ⊗ₘ θ_X) ≫ (β_ Xᘁ X).hom = (β_ Xᘁ X).hom ≫ (θ_X ⊗ₘ θ_{Xᘁ})`
(by braiding naturality for both components)

Wait, not quite. Let me just use:
`(θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ_X) ≫ (β_ Xᘁ X).hom`
braiding_naturality_right on Xᘁ ◁ θ_X:
`Xᘁ ◁ θ_X ≫ (β_ Xᘁ X).hom = (β_ Xᘁ X).hom ≫ θ_X ▷ Xᘁ`
braiding_naturality_left on θ_{Xᘁ} ▷ X:
`θ_{Xᘁ} ▷ X ≫ (β_ Xᘁ X).hom = (β_ Xᘁ X).hom ≫ X ◁ θ_{Xᘁ}`

So: `(θ_{Xᘁ} ⊗ₘ θ_X) ≫ (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε = ε`
→ `(β_ Xᘁ X).hom ≫ X ◁ θ_{Xᘁ} ≫ θ_X ▷ Xᘁ... `

Hmm this is getting messy. Let me try yet another approach.

### APPROACH D: Directly use coeval_identity and eval_identity together

We have (from twist_tensor on η):
```
η ≫ θ² ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ (β_ Xᘁ X).hom = η   ... (A)
```

Rearranging: `η ≫ θ² ▷ Xᘁ ≫ (β_ X Xᘁ).hom = η ≫ (β_ Xᘁ X).inv`   ... (A')

We want: `η ≫ θ ▷ Xᘁ ≫ (β_ Xᘁ X).inv = η ≫ θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom`   ... (target)

From (A'): `η ≫ θ² ▷ Xᘁ ≫ (β_ X Xᘁ).hom = η ≫ (β_ Xᘁ X).inv`
→ `η ≫ θ ▷ Xᘁ ≫ (θ ▷ Xᘁ ≫ (β_ X Xᘁ).hom) = η ≫ (β_ Xᘁ X).inv`
→ `η ≫ θ ▷ Xᘁ ≫ θ ▷ Xᘁ ≫ (β_ X Xᘁ).hom = η ≫ (β_ Xᘁ X).inv`

Prepend θ⁻¹ ▷ Xᘁ to both sides (since the whole thing follows η):
Actually, the target can be rewritten as:
`η ≫ θ ▷ Xᘁ ≫ (β_ Xᘁ X).inv ≫ ε = η ≫ θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε`

From (A'): substitute `η ≫ (β_ Xᘁ X).inv = η ≫ θ² ▷ Xᘁ ≫ (β_ X Xᘁ).hom`:
LHS = `η ≫ θ ▷ Xᘁ ≫ θ² ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε`
    = `η ≫ θ³ ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε`

RHS = `η ≫ θ⁻¹ ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε`

So need: θ³ = θ⁻¹ after η, i.e., θ⁴ = id after η. SAME PROBLEM.

### CONCLUSION (2026-02-22)

ALL approaches that try to prove the spherical identity purely at the
"coevaluation end" or "evaluation end" lead to requiring θ⁴ = id.

The ONLY way to avoid this is to use both zigzag identities simultaneously,
i.e., work with the full closed loop η...ε as a single entity.

We need a completely different proof strategy. Options:
1. Use Kassel/Turaev style proof via colored ribbon graphs
2. Use the "insertion" technique: insert θ_{Xᘁ⊗X} (= id before ε) and expand
3. Use the property that the mate of the full trace expression simplifies

---

## STATUS UPDATE (2026-02-23)

### Current file state (Ribbon.lean)

Two helper lemmas added:
- `coeval_twist_sq_monodromy` (line 280) — **COMPILES** ✓
  `η ≫ θ² ▷ Xᘁ ≫ β_{X,Xᘁ} ≫ β_{Xᘁ,X} = η`
- `eval_twist_sq_monodromy` (line 308) — **FAILS** at line 334
  `(θ_{Xᘁ})² ▷ X ≫ β_{Xᘁ,X} ≫ β_{X,Xᘁ} ≫ ε = ε`

### eval_twist_sq_monodromy failure analysis

After steps 1-3, h_nat is:
```
θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ_X ≫ β ≫ β' ≫ ε = ε
```

After `braiding_naturality_right_assoc` and `braiding_naturality_left_assoc` on h_nat,
Lean gives h_nat as:
```
(β_ Xᘁ X).hom ≫ X ◁ (twist Xᘁ).hom ≫ (twist X).hom ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε = ε
```

The problem: braiding_naturality moved BOTH θ_{Xᘁ} AND θ_X past both braidings, not
just θ_X. The `braiding_naturality_right_assoc` was applied to the WRONG pair — it
matched `Xᘁ ◁ θ_X ≫ β` but braiding_naturality_left then also matched the first θ_{Xᘁ}.

Then `rw [mate_eval] at h_nat` fails because the pattern `(twist Xᘁ).hom ▷ X ≫ ε_ X Xᘁ`
doesn't appear — the ε is separated by `(β_ X Xᘁ).hom`.

### FIX for eval_twist_sq_monodromy

Instead of moving θ_X past braidings, leave h_nat as is and transform the GOAL to match:

```lean
-- h_nat: θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ_X ≫ β ≫ β' ≫ ε = ε
-- Goal: (θ_{Xᘁ} ≫ θ_{Xᘁ}) ▷ X ≫ β ≫ β' ≫ ε = ε
-- Expand goal: θ_{Xᘁ} ▷ X ≫ θ_{Xᘁ} ▷ X ≫ β ≫ β' ≫ ε = ε
-- Use eval_twist_sq_identity (from h_nat rearranged):
--   θ_{Xᘁ} ▷ X ≫ β ≫ β' ≫ ε = (Xᘁ ◁ θ_X)⁻¹ ≫ (θ_{Xᘁ} ▷ X)⁻¹ ≫ ε
-- i.e., θ_{Xᘁ} ▷ X ≫ β ≫ β' ≫ ε = Xᘁ ◁ θ_X⁻¹ ≫ θ_{Xᘁ}⁻¹ ▷ X ≫ ε
```

Actually simpler approach: DON'T touch h_nat at all. Transform the GOAL instead.

Goal: `(θ ≫ θ) ▷ X ≫ β ≫ β' ≫ ε = ε`
= `θ ▷ X ≫ θ ▷ X ≫ β ≫ β' ≫ ε = ε`  (comp_whiskerRight)

Now convert the SECOND `θ ▷ X` to `Xᘁ ◁ θ_X` using:
- mate_eval BACKWARDS: `Xᘁ ◁ θ_X ≫ ε = θ_{Xᘁ} ▷ X ≫ ε` means they differ
  But we need to convert θ_{Xᘁ} ▷ X somewhere NOT adjacent to ε.

Alternative: use `whisker_exchange` to reorder θ_{Xᘁ} ▷ X and parts of β.

Actually, the SIMPLEST fix: don't transform h_nat. Instead, suffices to show:
`θ_{Xᘁ} ▷ X ≫ β ≫ β' ≫ ε = (θ_{Xᘁ})⁻¹ ▷ X ≫ ε`  (from h_nat, rearranging)

Then goal `θ ▷ X ≫ θ ▷ X ≫ β ≫ β' ≫ ε = ε` becomes
`θ ▷ X ≫ θ⁻¹ ▷ X ≫ ε = ε`, i.e., `(θ ≫ θ⁻¹) ▷ X ≫ ε = ε`, i.e., `𝟙 ▷ X ≫ ε = ε`. ✓

### Concrete fix for eval_twist_sq_monodromy

```lean
private theorem eval_twist_sq_monodromy (X : C) :
    ((twist Xᘁ).hom ≫ (twist Xᘁ).hom) ▷ X ≫
      (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = ε_ X Xᘁ := by
  -- h_nat: θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ_X ≫ β ≫ β' ≫ ε = ε
  have h_nat : ... (same as before)
  -- Derive: θ ▷ X ≫ β ≫ β' ≫ ε = (Xᘁ ◁ θ_X)⁻¹ ≫ (θ ▷ X)⁻¹ ≫ ε
  -- i.e., θ ▷ X ≫ β ≫ β' ≫ ε = Xᘁ ◁ θ⁻¹ ≫ θ⁻¹ ▷ X ≫ ε
  have key : (twist Xᘁ).hom ▷ X ≫ (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ =
      Xᘁ ◁ (twist X).inv ≫ (twist Xᘁ).inv ▷ X ≫ ε_ X Xᘁ := by
    -- From h_nat: θ ▷ X ≫ Xᘁ ◁ θ ≫ β ≫ β' ≫ ε = ε
    -- So: θ ▷ X ≫ β ≫ β' ≫ ε = (Xᘁ ◁ θ)⁻¹ ≫ (θ ▷ X)⁻¹ ≫ ε
    rw [← cancel_epi ((twist Xᘁ).hom ▷ X), ← cancel_epi (Xᘁ ◁ (twist X).hom)]
    simp only [Category.assoc]
    -- LHS: Xᘁ ◁ θ ≫ θ ▷ X ≫ θ ▷ X ≫ β ≫ β' ≫ ε
    -- Use whisker_exchange: Xᘁ ◁ θ ≫ θ ▷ X = θ ▷ X ≫ Xᘁ ◁ θ
    rw [whisker_exchange_assoc]
    -- LHS: θ ▷ X ≫ Xᘁ ◁ θ ≫ θ ▷ X ≫ β ≫ β' ≫ ε
    -- Hmm, this is getting complex. Maybe simpler to just use:
    -- h_nat says θ ▷ X ≫ Xᘁ ◁ θ ≫ β ≫ β' ≫ ε = ε
    -- So (θ ▷ X ≫ Xᘁ ◁ θ) is invertible and its composite with β ≫ β' ≫ ε = ε
    sorry
  -- Now: goal is (θ ≫ θ) ▷ X ≫ β ≫ β' ≫ ε = ε
  rw [comp_whiskerRight, Category.assoc, key]
  -- Goal: θ ▷ X ≫ Xᘁ ◁ θ⁻¹ ≫ θ⁻¹ ▷ X ≫ ε = ε
  -- Use mate_eval: θ⁻¹ ▷ X ≫ ε = Xᘁ ◁ θ⁻¹ ≫ ε (mate for θ⁻¹)
  -- Then Xᘁ ◁ θ⁻¹ ≫ Xᘁ ◁ θ⁻¹ ≫ ε = Xᘁ ◁ (θ⁻¹ ≫ θ⁻¹) ≫ ε... getting worse
  sorry
```

Hmm, this key lemma approach is also getting complex. Let me try a MUCH SIMPLER approach.

### SIMPLEST approach for eval_twist_sq_monodromy

From h_nat: `θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ_X ≫ β ≫ β' ≫ ε = ε`

Rearrange: `Xᘁ ◁ θ_X ≫ β ≫ β' ≫ ε = (θ_{Xᘁ})⁻¹ ▷ X ≫ ε`

Compose on left with θ_{Xᘁ} ▷ X:
`θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ_X ≫ β ≫ β' ≫ ε = θ_{Xᘁ} ▷ X ≫ (θ_{Xᘁ})⁻¹ ▷ X ≫ ε = ε` ✓

That's just h_nat again. Not helpful directly.

The goal is: `(θ ≫ θ) ▷ X ≫ β ≫ β' ≫ ε = ε`
= `θ ▷ X ≫ (θ ▷ X ≫ β ≫ β' ≫ ε) = ε`

From h_nat rearranged:
`θ ▷ X ≫ β ≫ β' ≫ ε = (Xᘁ ◁ θ_X)⁻¹ ≫ (θ_{Xᘁ} ▷ X)⁻¹ ≫ ε`
= `Xᘁ ◁ θ_X⁻¹ ≫ θ_{Xᘁ}⁻¹ ▷ X ≫ ε`

So goal = `θ ▷ X ≫ Xᘁ ◁ θ⁻¹ ≫ θ⁻¹ ▷ X ≫ ε`

Use mate_eval on θ⁻¹: `θ_{Xᘁ}⁻¹ ▷ X ≫ ε = Xᘁ ◁ θ_X⁻¹ ≫ ε` (need mate for inv)

Then: `θ ▷ X ≫ Xᘁ ◁ θ⁻¹ ≫ Xᘁ ◁ θ⁻¹ ≫ ε`
= `θ ▷ X ≫ Xᘁ ◁ (θ⁻¹ ≫ θ⁻¹) ≫ ε`
= `θ ▷ X ≫ Xᘁ ◁ θ⁻² ≫ ε`

Use mate_eval on θ⁻²: `Xᘁ ◁ θ⁻² ≫ ε = ??? ▷ X ≫ ε`... this keeps going.

### THE REAL SIMPLE FIX

DON'T rearrange h_nat. Instead, in the GOAL, convert θ_{Xᘁ} ▷ X to Xᘁ ◁ θ_X
using `whisker_exchange` (they commute!) and then match h_nat.

Goal after `comp_whiskerRight; simp`: `θ ▷ X ≫ θ ▷ X ≫ β ≫ β' ≫ ε = ε`

Convert second θ_{Xᘁ} ▷ X: can't directly since whisker_exchange only works
when the two whiskers are ADJACENT. And they ARE adjacent here!

`whisker_exchange`: `f ▷ Y ≫ X' ◁ g = W ◁ g ≫ f ▷ Z` for f : W → X', g : Y → Z
But here both are right whiskers `θ ▷ X ≫ θ ▷ X`, same type, same whisker side.
`whisker_exchange` needs one left whisker and one right whisker.

So we CANNOT directly convert. We need to first convert ONE of them via mate.

But mate only works next to η or ε!

### ACTUALLY WORKING APPROACH

Go back to h_nat UNTOUCHED:
`θ_{Xᘁ} ▷ X ≫ Xᘁ ◁ θ_X ≫ β ≫ β' ≫ ε = ε`

We want: `θ_{Xᘁ} ▷ X ≫ θ_{Xᘁ} ▷ X ≫ β ≫ β' ≫ ε = ε`

Suffices: `θ_{Xᘁ} ▷ X ≫ β ≫ β' ≫ ε = (θ_{Xᘁ})⁻¹ ▷ X ≫ ε`
(then composing with θ on left gives `θ² ▷ X ≫ β ≫ β' ≫ ε = θ ≫ θ⁻¹ ▷ X ≫ ε = ε`)

From h_nat: `θ ▷ X ≫ (Xᘁ ◁ θ_X ≫ β ≫ β' ≫ ε) = ε`
So: `Xᘁ ◁ θ_X ≫ β ≫ β' ≫ ε = θ⁻¹ ▷ X ≫ ε`

Now we want: `θ ▷ X ≫ β ≫ β' ≫ ε = θ⁻¹ ▷ X ≫ ε`

From h_nat: `θ ▷ X ≫ Xᘁ ◁ θ ≫ β ≫ β' ≫ ε = ε`
We derived: `Xᘁ ◁ θ ≫ β ≫ β' ≫ ε = θ⁻¹ ▷ X ≫ ε`

We need: `θ ▷ X ≫ β ≫ β' ≫ ε = θ⁻¹ ▷ X ≫ ε`

These are DIFFERENT! LHS has `θ ▷ X ≫ β ≫ β' ≫ ε` (right whisker then monodromy)
while we know `Xᘁ ◁ θ ≫ β ≫ β' ≫ ε = θ⁻¹ ▷ X ≫ ε` (LEFT whisker then monodromy).

The issue is θ ▷ X ≠ Xᘁ ◁ θ_X in general. They only agree when composed with η or ε.

### BREAKTHROUGH IDEA: Use eval_twist_sq_monodromy with DUAL OBJECT

Apply `coeval_twist_sq_monodromy` to Xᘁ instead of X!

`coeval_twist_sq_monodromy Xᘁ`:
`η_ Xᘁ (Xᘁ)ᘁ ≫ (θ_{Xᘁ})² ▷ (Xᘁ)ᘁ ≫ β ≫ β' = η_ Xᘁ (Xᘁ)ᘁ`

Hmm, this involves (Xᘁ)ᘁ not X. Not directly useful.

### KEY REALIZATION: The toSphericalCategory proof needs a DIFFERENT strategy

The current approach (steps 1-7 in toSphericalCategory, reducing to
`η ≫ f ▷ Xᘁ ≫ θ ▷ Xᘁ ≫ β⁻¹ ≫ ε = η ≫ f ▷ Xᘁ ≫ θ⁻¹ ▷ Xᘁ ≫ β ≫ ε`)
hits the θ⁴=id wall.

**New strategy**: Don't reduce to a single η...ε equation at all. Instead, show
that leftTrace = rightTrace by showing both equal a THIRD expression.

Specifically, show both equal:
`η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ`
(the "braided trace" without any twist).

For this we'd need:
- leftTrace f = η ≫ β⁻¹ ≫ Xᘁ ◁ θ ≫ Xᘁ ◁ f ≫ ε
  = ... = η ≫ f ▷ Xᘁ ≫ β ≫ ε  (need θ to cancel somehow)
This doesn't work either since θ doesn't cancel.

### ACTUALLY, try the rightAdjointMate approach from scratch

Show: leftTrace f = rightTrace f by showing
  leftTrace f = trace of (rightAdjointMate composed expression)

The left trace involves η_ Xᘁ (Xᘁ)ᘁ and ε_ X Xᘁ,
the right trace involves η_ X Xᘁ and ε_ Xᘁ (Xᘁ)ᘁ.

These use DIFFERENT pairings. Perhaps the proof should work by converting
the leftTrace into an expression involving the SAME pairing as rightTrace.

TODO: Think about this more carefully. The key obstacle is always the same:
braiding inv and braiding hom are different maps (β⁻¹_{Xᘁ,X} ≠ β_{X,Xᘁ}),
and the twist relates them only up to θ².

### NEXT STEPS (for next session)

1. Fix `eval_twist_sq_monodromy` — try NOT transforming h_nat, just cancel:
   ```
   have h_rearranged : Xᘁ ◁ (twist X).hom ≫ (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ =
       (twist Xᘁ).inv ▷ X ≫ ε_ X Xᘁ := by
     rw [← cancel_epi ((twist Xᘁ).hom ▷ X)]
     simp only [Category.assoc, comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
     exact h_nat
   ```
   Then transform the goal using mate_eval to convert one θ ▷ X to Xᘁ ◁ θ,
   and apply h_rearranged.

2. For `toSphericalCategory`: consider rewriting the proof from scratch using
   the "insertion + zigzag" technique. Insert `𝟙 = θ_{Xᘁ⊗X}⁻¹ ≫ θ_{Xᘁ⊗X}`
   before ε, expand, and use zigzag identities to cancel.

3. Consider whether the DEFINITIONS of leftTrace/rightTrace should be
   reconsidered — maybe there's a simpler formulation that makes the proof easier.

---

## twist_unit: θ_𝟙 = id — **PROVED**

The proof uses:
1. `twist_tensor (𝟙_ C) (𝟙_ C)` + `β²_{𝟙,𝟙} = id` gives `θ_{𝟙⊗𝟙} = θ_𝟙 ⊗ θ_𝟙`
2. `twist_naturality (λ_ (𝟙_ C)).hom` gives naturality through left unitor
3. `tensorHom_def'` decomposes the tensor product of twists
4. Idempotent iso argument: θ = θ ∘ θ and θ is iso implies θ = id
