#!/usr/bin/env bash
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: $0 <Domain>"
  echo "example: $0 MZV"
  exit 2
fi

DOMAIN="$1"
case "$DOMAIN" in
  Linfinity) TEMPLATE="lakefile.linfinity.toml" ;;
  MZV) TEMPLATE="lakefile.mzv.toml" ;;
  VOA) TEMPLATE="lakefile.voa.toml" ;;
  MTC) TEMPLATE="lakefile.mtc.toml" ;;
  *)
    echo "unsupported domain: $DOMAIN"
    echo "supported: Linfinity | MZV | VOA | MTC"
    exit 2
    ;;
esac

ROOT_REPO="$(cd "$(dirname "$0")/.." && pwd)"
DOMAIN_LOWER="$(printf '%s' "$DOMAIN" | tr '[:upper:]' '[:lower:]')"
DRYRUN_DIR="$(mktemp -d "/tmp/stringalgebra-${DOMAIN_LOWER}-dryrun.XXXXXX")"

mkdir -p "$DRYRUN_DIR/StringAlgebra"
cp -R "$ROOT_REPO/StringAlgebra/$DOMAIN" "$DRYRUN_DIR/StringAlgebra/$DOMAIN"
cp "$ROOT_REPO/StringAlgebra/$DOMAIN.lean" "$DRYRUN_DIR/StringAlgebra/$DOMAIN.lean"
cp "$ROOT_REPO/split/templates/$TEMPLATE" "$DRYRUN_DIR/lakefile.toml"
cp "$ROOT_REPO/split/templates/lean-toolchain" "$DRYRUN_DIR/lean-toolchain"
cp "$ROOT_REPO/lake-manifest.json" "$DRYRUN_DIR/lake-manifest.json"

mkdir -p "$DRYRUN_DIR/.lake"
ln -s "$ROOT_REPO/.lake/packages" "$DRYRUN_DIR/.lake/packages"

echo "== dry-run repo =="
echo "$DRYRUN_DIR"

echo
echo "== build =="
(
  cd "$DRYRUN_DIR"
  lake build "StringAlgebra.$DOMAIN"
)

echo
echo "== sorry count =="
SORRY_COUNT="$( (rg -n '^\s*sorry\b' "$DRYRUN_DIR/StringAlgebra/$DOMAIN" --glob '*.lean' || true) | wc -l | tr -d ' ' )"
echo "$DOMAIN $SORRY_COUNT"

echo
echo "== anti-smuggling scans =="
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' \
  "$DRYRUN_DIR/StringAlgebra/$DOMAIN" --glob '*.lean' || true
rg -n '^\s*axiom\s|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\s' \
  "$DRYRUN_DIR/StringAlgebra/$DOMAIN" --glob '*.lean' || true

echo
echo "== import-boundary scan =="
IMPORTS="$(rg -n '^import StringAlgebra\.' \
  "$DRYRUN_DIR/StringAlgebra/$DOMAIN" "$DRYRUN_DIR/StringAlgebra/$DOMAIN.lean" --glob '*.lean')"
echo "$IMPORTS"

CROSS_IMPORTS="$(printf '%s\n' "$IMPORTS" | rg -v "import StringAlgebra\\.$DOMAIN(\\.|$)" || true)"
if [ -n "$CROSS_IMPORTS" ]; then
  echo
  echo "cross-domain imports detected:"
  echo "$CROSS_IMPORTS"
  exit 1
fi

echo
echo "dry-run extraction checks passed for $DOMAIN"
