#!/usr/bin/env bash
# Implementation is pinned in tauceti.toml; CI materializes it from TauCetiTools.
exec uvx --from git+https://github.com/TauCetiProject/TauCetiTools@5d8bd99dabfbf0730e301825f378bbb0b93db25b tauceti-tools script lint-style.sh "$@"
