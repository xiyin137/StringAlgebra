#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: $0 <Domain> <TargetDir> [--no-checks]"
  echo "example: $0 MZV /tmp/StringAlgebra-MZV"
  exit 2
}

if [ $# -lt 2 ] || [ $# -gt 3 ]; then
  usage
fi

DOMAIN="$1"
TARGET_DIR="$2"
RUN_CHECKS="yes"

if [ "${3:-}" = "--no-checks" ]; then
  RUN_CHECKS="no"
elif [ "${3:-}" != "" ]; then
  usage
fi

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

if [ -e "$TARGET_DIR" ] && [ -n "$(ls -A "$TARGET_DIR" 2>/dev/null || true)" ]; then
  echo "target directory exists and is not empty: $TARGET_DIR"
  exit 1
fi

mkdir -p "$TARGET_DIR/StringAlgebra"
cp -R "$ROOT_REPO/StringAlgebra/$DOMAIN" "$TARGET_DIR/StringAlgebra/$DOMAIN"
cp "$ROOT_REPO/StringAlgebra/$DOMAIN.lean" "$TARGET_DIR/StringAlgebra/$DOMAIN.lean"
cp "$ROOT_REPO/split/templates/$TEMPLATE" "$TARGET_DIR/lakefile.toml"
cp "$ROOT_REPO/split/templates/lean-toolchain" "$TARGET_DIR/lean-toolchain"
cp "$ROOT_REPO/lake-manifest.json" "$TARGET_DIR/lake-manifest.json"

cat > "$TARGET_DIR/.gitignore" <<'EOF'
/build/
/.lake/
.DS_Store
EOF

if [ -f "$TARGET_DIR/StringAlgebra/$DOMAIN/TODO.md" ]; then
  cp "$TARGET_DIR/StringAlgebra/$DOMAIN/TODO.md" "$TARGET_DIR/TODO.md"
fi

SORRY_COUNT="$( (rg -n '^\s*sorry\b' "$TARGET_DIR/StringAlgebra/$DOMAIN" --glob '*.lean' || true) | wc -l | tr -d ' ' )"
TODAY="$(date +%F)"

cat > "$TARGET_DIR/README.md" <<EOF
# StringAlgebra $DOMAIN

Standalone extraction of \`StringAlgebra.$DOMAIN\` from the StringAlgebra monorepo.

## Status ($TODAY)

1. Theorem-level \`sorry\` count in \`StringAlgebra/$DOMAIN\`: $SORRY_COUNT
2. Anti-smuggling policy: no \`axiom\` smuggling, no assumption-bundle wrapper classes.
3. Build target: \`lake build StringAlgebra.$DOMAIN\`

## Quick Audit Commands

\`\`\`bash
lake build StringAlgebra.$DOMAIN
rg -n '^\\s*sorry\\b' StringAlgebra/$DOMAIN --glob '*.lean'
rg -n '^\\s*class\\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra/$DOMAIN --glob '*.lean'
rg -n '^\\s*axiom\\s|\\badmit\\b|Classical\\.choose|Classical\\.epsilon|^\\s*unsafe\\s' StringAlgebra/$DOMAIN --glob '*.lean'
\`\`\`
EOF

# Prefer local package cache linkage so extraction can be validated offline.
mkdir -p "$TARGET_DIR/.lake"
if [ ! -e "$TARGET_DIR/.lake/packages" ]; then
  ln -s "$ROOT_REPO/.lake/packages" "$TARGET_DIR/.lake/packages"
fi

echo "extracted domain repo at: $TARGET_DIR"

if [ "$RUN_CHECKS" = "yes" ]; then
  echo
  echo "== build check =="
  (
    cd "$TARGET_DIR"
    lake build "StringAlgebra.$DOMAIN"
  )

  echo
  echo "== anti-smuggling scans =="
  rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' \
    "$TARGET_DIR/StringAlgebra/$DOMAIN" --glob '*.lean' || true
  rg -n '^\s*axiom\s|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\s' \
    "$TARGET_DIR/StringAlgebra/$DOMAIN" --glob '*.lean' || true

  echo
  echo "== import-boundary scan =="
  IMPORTS="$(rg -n '^import StringAlgebra\.' \
    "$TARGET_DIR/StringAlgebra/$DOMAIN" "$TARGET_DIR/StringAlgebra/$DOMAIN.lean" --glob '*.lean')"
  echo "$IMPORTS"

  CROSS_IMPORTS="$(printf '%s\n' "$IMPORTS" | rg -v "import StringAlgebra\\.$DOMAIN(\\.|$)" || true)"
  if [ -n "$CROSS_IMPORTS" ]; then
    echo
    echo "cross-domain imports detected:"
    echo "$CROSS_IMPORTS"
    exit 1
  fi

  echo
  echo "extraction checks passed for $DOMAIN"
fi
