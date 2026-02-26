# Split Templates

This folder contains concrete templates and checklists for splitting the monorepo
into domain repositories without changing Lean module names.

## Contents

1. `EXTRACTION_CHECKLIST.md`
2. `templates/lakefile.linfinity.toml`
3. `templates/lakefile.mzv.toml`
4. `templates/lakefile.voa.toml`
5. `templates/lakefile.mtc.toml`
6. `templates/lean-toolchain`
7. `split_audit.sh`
8. `dry_run_extract.sh`
9. `extract_domain.sh`

## Design Choice

Split repos are expected to keep the existing module path prefix
`StringAlgebra.<Domain>...` to avoid immediate namespace churn.

That means each split repo should still expose a Lean library named
`StringAlgebra`, but with a domain-specific default target.

## Fast Dry Run

Run a local extraction dry run for one domain:

```bash
bash split/dry_run_extract.sh MZV
```

Supported domain arguments are `Linfinity`, `MZV`, `VOA`, `MTC`.

## Actual Local Extraction

Create a standalone local repo directory for a domain:

```bash
bash split/extract_domain.sh MZV /tmp/StringAlgebra-MZV
```

Add `--no-checks` to only scaffold files without running build/audits.
