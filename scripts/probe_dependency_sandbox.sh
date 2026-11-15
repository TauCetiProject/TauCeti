#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@3b5a8cf7e28f2d51fc6f5e5a13941840db612c0e tauceti-tools script probe_dependency_sandbox.sh "$@"
