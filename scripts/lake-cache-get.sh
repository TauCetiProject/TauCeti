#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@8bad7a00af97c00c90a9777c195618c857dbf91c tauceti-tools script lake-cache-get.sh "$@"
