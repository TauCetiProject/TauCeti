#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@ad4e955b398d1419b0931e3c825a925f1c6a6e9b tauceti-tools script build-lint-driver.sh "$@"
