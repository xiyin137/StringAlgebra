# StringAlgebra (Split Control Repo)

This repository is the split-control/orchestration repo for the StringAlgebra project.
Domain development now lives in standalone repositories.

## Domain Repositories

1. MZV: https://github.com/xiyin137/StringAlgebra-MZV
2. VOA: https://github.com/xiyin137/StringAlgebra-VOA
3. Linfinity: https://github.com/xiyin137/StringAlgebra-Linfinity
4. MTC: https://github.com/xiyin137/StringAlgebra-MTC

## What This Repo Contains

1. Split planning and status docs.
2. Extraction and dry-run scripts.
3. Template files for split repos.

Key files:

1. `SPLIT_REPO_READINESS.md`
2. `split/README.md`
3. `split/EXTRACTION_CHECKLIST.md`
4. `split/dry_run_extract.sh`
5. `split/extract_domain.sh`
6. `split/split_audit.sh`
7. `split/LOCAL_REPOS.md`

## Policy

1. Theorem-level `sorry` is acceptable as honest in-progress proof debt.
2. Smuggling is not allowed (`axiom` wrappers, hidden choice machinery, assumption bundles).
3. Cutover and repository boundary changes must be explicit and auditable.

## Active Development

Use the standalone domain repositories above as the primary development locations.
