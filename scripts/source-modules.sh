#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@4c54de2c219ff88229741c02faba876b8fa2b094 tauceti-tools script source-modules.sh "$@"
