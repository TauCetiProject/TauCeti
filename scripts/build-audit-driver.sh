#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@02db6ea51c27553cb6271e605612a56169ae72f6 tauceti-tools script build-audit-driver.sh "$@"
