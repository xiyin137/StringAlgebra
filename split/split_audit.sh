#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-StringAlgebra}"

echo "== per-domain build checks =="
lake build StringAlgebra.Linfinity
lake build StringAlgebra.MZV
lake build StringAlgebra.VOA
lake build StringAlgebra.MTC

echo
echo "== proof-gap counts =="
echo "Linfinity $(rg -n '^\s*sorry\b' "$ROOT/Linfinity" --glob '*.lean' | wc -l | tr -d ' ')"
echo "MZV $(rg -n '^\s*sorry\b' "$ROOT/MZV" --glob '*.lean' | wc -l | tr -d ' ')"
echo "VOA $(rg -n '^\s*sorry\b' "$ROOT/VOA" --glob '*.lean' | wc -l | tr -d ' ')"
echo "MTC $(rg -n '^\s*sorry\b' "$ROOT/MTC" --glob '*.lean' | wc -l | tr -d ' ')"
echo "TOTAL $(rg -n '^\s*sorry\b' "$ROOT" --glob '*.lean' | wc -l | tr -d ' ')"

echo
echo "== anti-smuggling scan =="
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' "$ROOT" --glob '*.lean' || true
rg -n '\baxiom\b|\badmit\b|Classical\.choose|Classical\.epsilon|\bunsafe\b' "$ROOT" --glob '*.lean' || true

echo
echo "== cross-domain import scan =="
rg -n '^import StringAlgebra\.' "$ROOT" --glob '*.lean'
