# Split Repo Readiness Plan

Date: 2026-02-26

This document defines the staged plan for splitting `StringAlgebra` into four repositories:

1. `Linfinity`
2. `MZV`
3. `VOA`
4. `MTC`

It was intentionally gate-driven; the local cutover has now been executed.

## Cutover Status

1. Local split repos exist and are validated under `split/repos/`.
2. The old in-repo domain source folders were removed from this repo.
3. This repo is now split-control/docs/scripts only.

## Current Audit Snapshot

1. Build status:
   - `lake build StringAlgebra.Linfinity` passes.
   - `lake build StringAlgebra.MZV` passes.
   - `lake build StringAlgebra.VOA` passes.
   - `lake build StringAlgebra.MTC` passes.
2. Gap status:
   - `Linfinity`: 3 theorem-level `sorry`.
   - `MTC`: 16 theorem-level `sorry`.
   - `MZV`: 0.
   - `VOA`: 0.
   - Total: 19 theorem-level `sorry`.
3. Smuggling status:
   - No `class ...Axiom/Axioms/Assumption/Assumptions` wrappers in domain files.
   - No `axiom`, `admit`, `Classical.choose`, `Classical.epsilon`, `unsafe` usage in Lean code (outside plain-language comments/doc text).
4. Import-boundary status:
   - Import-edge audit currently shows no cross-domain compile imports among `Linfinity`, `MZV`, `VOA`, `MTC`.
   - Existing imports are internal to each domain (plus `Mathlib`).

## Hard Gates Before Actual Split

1. Anti-smuggling gate:
   - No new assumption-bundle classes or hidden-choice patterns.
   - Remaining proof debt stays theorem-local with explicit closure-route comments.
2. Interface freeze gate:
   - Domain entrypoints (`StringAlgebra/Linfinity.lean`, `MZV.lean`, `VOA.lean`, `MTC.lean`) remain stable for one focused cleanup cycle.
3. CI parity gate:
   - Each domain has an independent build check command and a `sorry` count check command.
4. Documentation parity gate:
   - Each domain has its own `README` + `TODO` with current `sorry` count and dependency flow.

## Target Repository Boundaries

1. `StringAlgebra-Linfinity`
   - Local path: `split/repos/StringAlgebra-Linfinity`
2. `StringAlgebra-MZV`
   - Local path: `split/repos/StringAlgebra-MZV`
3. `StringAlgebra-VOA`
   - Local path: `split/repos/StringAlgebra-VOA`
4. `StringAlgebra-MTC`
   - Local path: `split/repos/StringAlgebra-MTC`

## Staged Execution Plan

### Phase 0 - Continue Anti-Smuggling Closure

1. Close proof gaps by existing domain DAGs without adding wrappers.
2. Keep `README.md` and domain TODO ledgers synchronized with exact counts.
3. Exit criterion:
   - no architecture churn in core domain entry files for one cleanup cycle.

### Phase 1 - Split-Ready Packaging in Monorepo

1. Prepare per-domain `lakefile.toml` templates in `split/` for later extraction.
2. Prepare per-domain CI command set:
   - build target
   - `sorry` count
   - smuggling scan
3. Exit criterion:
   - dry-run extraction checklist validated locally.

Implemented artifacts (current monorepo):

1. `split/EXTRACTION_CHECKLIST.md`
2. `split/templates/lakefile.linfinity.toml`
3. `split/templates/lakefile.mzv.toml`
4. `split/templates/lakefile.voa.toml`
5. `split/templates/lakefile.mtc.toml`
6. `split/templates/lean-toolchain`
7. `split/split_audit.sh`
8. `split/dry_run_extract.sh`
9. `split/extract_domain.sh`

Dry-run extraction status (all domains validated locally in isolated temp repos):

1. `MZV`
   - build passed (`lake build StringAlgebra.MZV`)
   - `sorry`: `0`
   - no assumption-bundle/smuggling scan hits
   - no cross-domain imports
2. `VOA`
   - build passed (`lake build StringAlgebra.VOA`)
   - `sorry`: `0`
   - no assumption-bundle/smuggling scan hits
   - no cross-domain imports
3. `Linfinity`
   - build passed (`lake build StringAlgebra.Linfinity`)
   - `sorry`: `3` (theorem-level only)
   - no assumption-bundle/smuggling scan hits
   - no cross-domain imports
4. `MTC`
   - build passed (`lake build StringAlgebra.MTC`)
   - `sorry`: `16` (theorem-level only)
   - no assumption-bundle/smuggling scan hits
   - no cross-domain imports

### Phase 2 - Repository Extraction (One Domain at a Time)

Recommended order:

1. `MZV` (smallest/`sorry`-free)
2. `VOA` (`sorry`-free)
3. `Linfinity`
4. `MTC` (largest active debt surface)

For each extraction:

1. Copy domain sources + top-level module file.
2. Add domain `lakefile.toml`, `lean-toolchain`, and domain README/TODO.
3. Run domain build and audits.
4. Tag initial split commit and enable CI.

Current local execution status:

1. `MZV` extracted to `/tmp/StringAlgebra-MZV-20260226-164100`.
2. `VOA` extracted to `/tmp/StringAlgebra-VOA-20260226-164206`.
3. `Linfinity` extracted to `/tmp/StringAlgebra-Linfinity-20260226-164229`.
4. `MTC` extracted to `/tmp/StringAlgebra-MTC-20260226-164300`.

Each extracted repo passed:

1. Domain build (`lake build StringAlgebra.<Domain>`).
2. Anti-smuggling scans (no assumption-bundle classes, no axiom/admit/choose/epsilon/unsafe hits).
3. Import boundary checks (no cross-domain imports).

### Phase 3 - Monorepo Transition Cleanup

1. Update root README pointers from monorepo paths to new repo paths.
2. Keep a compatibility branch or archive tag in monorepo.
3. If needed, add thin meta-repo containing only cross-repo docs and release matrix.

## Command Checklist

```bash
# build checks
lake build StringAlgebra.Linfinity
lake build StringAlgebra.MZV
lake build StringAlgebra.VOA
lake build StringAlgebra.MTC

# proof-gap counts
rg -n '^\s*sorry\b' StringAlgebra/Linfinity --glob '*.lean' | wc -l
rg -n '^\s*sorry\b' StringAlgebra/MZV --glob '*.lean' | wc -l
rg -n '^\s*sorry\b' StringAlgebra/VOA --glob '*.lean' | wc -l
rg -n '^\s*sorry\b' StringAlgebra/MTC --glob '*.lean' | wc -l

# anti-smuggling scans
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra --glob '*.lean'
rg -n '\baxiom\b|\badmit\b|Classical\.choose|Classical\.epsilon|\bunsafe\b' StringAlgebra --glob '*.lean'

# cross-domain import scan
rg -n '^import StringAlgebra\.' StringAlgebra --glob '*.lean'
```

## Split Decision Rule

Proceed to actual split only after Phase 0 and Phase 1 exit criteria are both satisfied.
