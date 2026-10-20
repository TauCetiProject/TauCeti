#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@970da34361efb9036d37baafdd887096e94caa01 tauceti-tools script probe_dependency_sandbox.sh "$@"
