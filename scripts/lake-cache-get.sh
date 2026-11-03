#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@ac879910a87ec1605cbb52191cee551fafeddb0c tauceti-tools script lake-cache-get.sh "$@"
