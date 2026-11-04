#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@2bac9bc93d54be82ded88d135445f164e82b9109 tauceti-tools script sandbox-build.sh "$@"
