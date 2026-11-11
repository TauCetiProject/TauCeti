#!/usr/bin/env bash
# Workers already provide the pinned Tools interpreter; standalone checkouts use uvx.
set -euo pipefail
if [ -n "${TAUCETI_VERIFY_PYTHON:-}" ]; then
  exec "$TAUCETI_VERIFY_PYTHON" -m tauceti_tools script local_checks.py "$@"
else
  exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@3b5a8cf7e28f2d51fc6f5e5a13941840db612c0e tauceti-tools script local_checks.py "$@"
fi
