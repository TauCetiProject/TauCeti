#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@4c7381d3a47fd9b9f7aa786dd2a28c375e36fee6 tauceti-tools script probe_dependency_sandbox.sh "$@"
