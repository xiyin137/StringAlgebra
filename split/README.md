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

## Design Choice

Split repos are expected to keep the existing module path prefix
`StringAlgebra.<Domain>...` to avoid immediate namespace churn.

That means each split repo should still expose a Lean library named
`StringAlgebra`, but with a domain-specific default target.
