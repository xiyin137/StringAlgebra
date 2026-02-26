# StringAlgebra (Split Control Repo)

This repository now acts as the split-control/orchestration repo.
The domain source trees were factored out of this repo into standalone local repos.

## Local Split Repos

Canonical local paths:

1. `/Users/xiyin/StringAlgebra/split/repos/StringAlgebra-MZV`
2. `/Users/xiyin/StringAlgebra/split/repos/StringAlgebra-VOA`
3. `/Users/xiyin/StringAlgebra/split/repos/StringAlgebra-Linfinity`
4. `/Users/xiyin/StringAlgebra/split/repos/StringAlgebra-MTC`

## What Remains Here

1. Split planning and status docs.
2. Extraction/dry-run scripts.
3. Template files for per-domain repo scaffolding.

Main files:

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
3. Cutover must remain explicit and auditable.

## Next Action

Use the standalone repos under `split/repos/` as the primary development locations.
