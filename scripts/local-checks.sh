#!/usr/bin/env bash
# Workers already provide the pinned Tools interpreter; standalone checkouts use uvx.
set -euo pipefail
if [ -n "${TAUCETI_VERIFY_PYTHON:-}" ]; then
  exec "$TAUCETI_VERIFY_PYTHON" -m tauceti_tools script local_checks.py "$@"
else
  exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@fddd772584e81a08d56ea573169f37411f01a201 tauceti-tools script local_checks.py "$@"
fi
