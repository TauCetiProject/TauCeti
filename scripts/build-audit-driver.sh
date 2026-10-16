#!/usr/bin/env bash
# Build only trusted sources and the pinned Lean sysroot. No candidate artifacts or cache.
# build-audit-driver.sh PROJECT_ROOT TRUSTED_SCRIPTS OUT_DIR
set -euo pipefail
PROJECT_ROOT="$(cd "${1:?project root required}" && pwd)"
TRUSTED_SCRIPTS="$(cd "${2:?trusted scripts required}" && pwd)"
OUT_DIR="${3:?output directory required}"
mkdir -p "$OUT_DIR"
WS="$(mktemp -d "$OUT_DIR/audit-ws.XXXXXX")"
trap 'rm -rf "$WS"' EXIT
mkdir -p "$WS/scripts"
cp "$TRUSTED_SCRIPTS/Axioms.lean" "$WS/scripts/"
cp "$PROJECT_ROOT/lean-toolchain" "$WS/lean-toolchain"
cat > "$WS/lakefile.toml" <<'TOML'
name = "audit-driver"

[[lean_exe]]
name = "audit-driver"
root = "scripts.Axioms"
TOML
(cd "$WS" && env -u ELAN_TOOLCHAIN -u LAKE_CONFIG -u LEAN_PATH -u LEAN_SRC_PATH \
  -u LAKE_PKG_URL_MAP LAKE_CACHE_DIR= LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false \
  LAKE_NO_CACHE=true lake build audit-driver)
install -m 0555 "$WS/.lake/build/bin/audit-driver" "$OUT_DIR/audit-driver"
