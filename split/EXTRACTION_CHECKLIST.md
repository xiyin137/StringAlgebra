# Domain Extraction Checklist

Use this checklist for each split repository (`Linfinity`, `MZV`, `VOA`, `MTC`).

## 1. Copy Source Surface

1. Copy `StringAlgebra/<Domain>/`.
2. Copy `StringAlgebra/<Domain>.lean`.
3. Do not copy unrelated sibling domain folders.

## 2. Install Build Scaffolding

1. Copy `templates/lean-toolchain` to repo root.
2. Copy the matching domain lakefile template to `lakefile.toml`.
3. Run `lake update` and `lake exe cache get`.

## 3. Verify Domain Build

1. `lake build StringAlgebra.<Domain>`
2. `rg -n '^\s*sorry\b' StringAlgebra/<Domain> --glob '*.lean'`
3. `rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra/<Domain> --glob '*.lean'`
4. `rg -n '\baxiom\b|\badmit\b|Classical\.choose|Classical\.epsilon|\bunsafe\b' StringAlgebra/<Domain> --glob '*.lean'`

## 4. Boundary Check

1. `rg -n '^import StringAlgebra\.' StringAlgebra/<Domain> --glob '*.lean'`
2. Confirm imports stay within `StringAlgebra.<Domain>.*` plus `Mathlib.*`.

## 5. Documentation Sync

1. Bring domain `TODO.md` into new repo root docs.
2. Add repo README with:
   - current `sorry` count
   - anti-smuggling policy
   - build command
   - dependency flow

## 6. CI Minimum

1. Build workflow for `lake build StringAlgebra.<Domain>`.
2. Audit workflow for `sorry` count + smuggling scan.
3. Required status checks enabled before protected-branch merge.
