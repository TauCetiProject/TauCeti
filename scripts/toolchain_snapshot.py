#!/usr/bin/env python3
"""Compatibility entrypoint; implementation is pinned through TauCetiTools."""
import sys
from tauceti_tools.templates import import_shared, run_script

if __name__ == "__main__":
    raise SystemExit(run_script('toolchain_snapshot.py', sys.argv[1:]))
else:
    implementation = import_shared('toolchain_snapshot.py', __name__)
    globals().update(vars(implementation))
    sys.modules[__name__] = implementation
