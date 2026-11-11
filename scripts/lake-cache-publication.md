# Native Lake publication

The producer's final build writes the native map with `lake build --iofail --rehash -o .lake/outputs.jsonl` when artifact caching is enabled. This is one build, with no subsequent whole-graph output scan. Native `lake cache stage` copies the full map and artifacts after the required checks. Lake already preserves restored archives for publication.

After candidate processes exit, `lake_cache_publish.py stage` accepts only a complete flat map and ordinary archive files, copying them into a fresh host-owned directory. The isolated publisher repeats this small data boundary before receiving the upload key. Neither copy invokes candidate code or performs network requests. There is no additional publication manifest, omission protocol, inherited-object probe or digest database.

The publisher uses stock `lake cache put-staged` with the explicit revision, repository and toolchain. It does not configure a candidate workspace. Lake uploads artifacts before the revision map. A failed upload is retryable from the complete staged artifact; no producer rerun or full-publication switch is required. The finalizer still requires the exact map to be publicly readable before landing.

Full publication intentionally transfers all mapped artifacts. Measure total preparation, transfer and publication time and bytes; preserve native cache validation and credential isolation when optimizing further.

Run `python3 scripts/test_lake_cache_publish.py --integration` with stock Lean/Lake, curl and openssl. The local TLS fixture checks failed upload ordering, retry, fresh restoration, changed-source rebuilding, archive reuse and corrupt-download rejection using dummy credentials only.
