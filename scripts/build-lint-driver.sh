#!/usr/bin/env bash
# build-lint-driver.sh PROJECT_ROOT DRIVER_SOURCE OUT_DIR
#
# Compile the environment-lint driver (scripts/LintEnvDriver.lean) into OUT_DIR/lint-env-driver,
# in a throwaway Lake workspace under OUT_DIR whose only dependency is PROJECT_ROOT's Batteries
# checkout, by path, with PROJECT_ROOT's toolchain. Only DRIVER_SOURCE and the Batteries modules it
# imports are compiled.
#
# The result is trusted only if that Batteries checkout was pristine when this ran. pr-build.yml
# therefore runs this on the host before any candidate code executes and mounts OUT_DIR read-only
# into the sandbox: a candidate's build can rewrite .lake/packages/batteries, and lint-env.sh
# refuses to compile the driver itself inside the sandbox. Post-merge CI and local runs, which lint
# main, build it through lint-env.sh.
set -euo pipefail

PROJECT_ROOT="$(cd "${1:?usage: build-lint-driver.sh PROJECT_ROOT DRIVER_SOURCE OUT_DIR}" && pwd)"
DRIVER_SOURCE="${2:?usage: build-lint-driver.sh PROJECT_ROOT DRIVER_SOURCE OUT_DIR}"
OUT_DIR="${3:?usage: build-lint-driver.sh PROJECT_ROOT DRIVER_SOURCE OUT_DIR}"

BATTERIES_DIR="$PROJECT_ROOT/.lake/packages/batteries"
if [ ! -f "$BATTERIES_DIR/Batteries/Tactic/Lint.lean" ]; then
  echo "build-lint-driver: no Batteries checkout at $BATTERIES_DIR; fetch dependencies first" >&2
  exit 1
fi

mkdir -p "$OUT_DIR"
WS="$(mktemp -d "$OUT_DIR/ws.XXXXXX")"
cp "$DRIVER_SOURCE" "$WS/LintEnvDriver.lean"
cp "$PROJECT_ROOT/lean-toolchain" "$WS/lean-toolchain"
cat > "$WS/lakefile.toml" <<TOML
name = "lint-env-driver"

[[require]]
name = "batteries"
path = "$BATTERIES_DIR"

[[lean_exe]]
name = "lint-env-driver"
root = "LintEnvDriver"
supportInterpreter = true
TOML
# Build from sources and build directories only. pr-build.yml exports Lake artifact-cache settings
# for the whole job, and that cache can hold artifacts from a candidate's build (a merge-group rerun
# reuses exact-head outputs), so reading it here would let candidate artifacts into the driver.
# An empty LAKE_CACHE_DIR disables Lake's cache directory (unset, Lake falls back to a global one).
# The other variables could redirect the toolchain, configuration or search paths, so clear them.
(cd "$WS" && env -u ELAN_TOOLCHAIN -u LAKE_CONFIG -u LEAN_PATH -u LEAN_SRC_PATH \
  -u LAKE_PKG_URL_MAP LAKE_CACHE_DIR= LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false \
  LAKE_NO_CACHE=true lake build lint-env-driver)
install -m 0555 "$WS/.lake/build/bin/lint-env-driver" "$OUT_DIR/lint-env-driver"
rm -rf "$WS"
