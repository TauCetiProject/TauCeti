#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@e29d8d82f21200c96510116cd3e004e9d33bcaea tauceti-tools script lint-env.sh "$@"
