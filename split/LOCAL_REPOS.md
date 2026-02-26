# Local Split Repos

Date: 2026-02-26

Canonical local factoring paths:

1. `/Users/xiyin/StringAlgebra/split/repos/StringAlgebra-MZV`
2. `/Users/xiyin/StringAlgebra/split/repos/StringAlgebra-VOA`
3. `/Users/xiyin/StringAlgebra/split/repos/StringAlgebra-Linfinity`
4. `/Users/xiyin/StringAlgebra/split/repos/StringAlgebra-MTC`

Initial local split commits:

1. `StringAlgebra-MZV`: `77f24c3`
2. `StringAlgebra-VOA`: `7c7d3b6`
3. `StringAlgebra-Linfinity`: `bc09110`
4. `StringAlgebra-MTC`: `c3c06ff`

Validation status in local repos:

1. `lake build StringAlgebra.MZV` passes.
2. `lake build StringAlgebra.VOA` passes.
3. `lake build StringAlgebra.Linfinity` passes (theorem-level `sorry` warnings expected).
4. `lake build StringAlgebra.MTC` passes (theorem-level `sorry` warnings expected).

Notes:

1. `split/repos/` is intentionally ignored in monorepo `.gitignore`.
2. No push/publish action has been performed for these local split repos in this step.
