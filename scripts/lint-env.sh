#!/usr/bin/env bash
# The implementation is TauCetiTools main; CI materializes it from there too.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@main tauceti-tools script lint-env.sh "$@"
