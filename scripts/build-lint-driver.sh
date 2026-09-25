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
(cd "$WS" && lake build lint-env-driver)
install -m 0555 "$WS/.lake/build/bin/lint-env-driver" "$OUT_DIR/lint-env-driver"
rm -rf "$WS"
