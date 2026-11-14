#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@11e608b37033d5a3e775786b14a8ae97603d949a tauceti-tools script lint-style.sh "$@"
