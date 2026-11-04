#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@b49bb4fd588d9e9b96660ce38aa1a37ba1e95d46 tauceti-tools script sandbox-build.sh "$@"
