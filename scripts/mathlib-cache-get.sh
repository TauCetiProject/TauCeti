#!/usr/bin/env bash
# Best-effort Mathlib cache restore. The caller must still build and audit from source
# when artifacts are unavailable. PR callers use the workflow-pinned copy of this script.
set -euo pipefail

PROJECT_DIR="${1:?usage: mathlib-cache-get.sh <project-dir> <log-file>}"
LOG_FILE="${2:?usage: mathlib-cache-get.sh <project-dir> <log-file>}"
cd "$PROJECT_DIR"

if ! lake exe cache get 2>&1 | tee "$LOG_FILE"; then
  echo "::warning::lake exe cache get failed; forcing a full refetch"
  if ! lake exe cache get! 2>&1 | tee -a "$LOG_FILE"; then
    echo "::warning::Mathlib cache restore failed twice; the build will compile missing dependencies from source"
  fi
fi

# Mathlib also returns success on a partial hit. Report it without blocking the build.
if grep -qF 'some files were not found in the cache' "$LOG_FILE"; then
  echo "::warning::Mathlib cache is incomplete; the build will compile missing dependencies from source"
fi
