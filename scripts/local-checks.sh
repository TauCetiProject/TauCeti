#!/usr/bin/env bash
# Workers already provide the pinned Tools interpreter; standalone checkouts use uvx.
set -euo pipefail
if [ -n "${TAUCETI_VERIFY_PYTHON:-}" ]; then
  exec "$TAUCETI_VERIFY_PYTHON" -m tauceti_tools script local_checks.py "$@"
else
  exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@3efe7c2dac753c6acaec93b9398cd2260493735d tauceti-tools script local_checks.py "$@"
fi
