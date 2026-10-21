#!/usr/bin/env python3
"""Compatibility entrypoint; implementation is pinned through TauCetiTools."""
import sys
from tauceti_tools.templates import import_shared, run_script

if __name__ == "__main__":
    raise SystemExit(run_script('pipeline_health.py', sys.argv[1:]))
else:
    implementation = import_shared('pipeline_health.py', __name__)
    globals().update(vars(implementation))
    sys.modules[__name__] = implementation
