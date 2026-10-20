#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@38690d9addbc153e679580ae777d2c3fe40cbcca tauceti-tools script source-modules.sh "$@"
