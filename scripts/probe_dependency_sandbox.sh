#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@fddd772584e81a08d56ea573169f37411f01a201 tauceti-tools script probe_dependency_sandbox.sh "$@"
