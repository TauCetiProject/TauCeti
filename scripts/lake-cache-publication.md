# Incremental Lake publication

Only the existing audited main and merge-group producers publish. Ordinary PRs
never stage compiled files for the shared cache. Exact builds, audits, eligibility
and map availability gates are unchanged. Hashes check byte integrity; the audits
establish proof correctness.

The producer keeps a toolchain-scoped snapshot of downloaded archive associations
and SHA-256 digests outside the candidate's writable checkout. After all audits,
stock Lake validates current traces and writes the **full** map using
`--no-build --rehash`; candidate-written hash sidecars cannot select reused bytes.
After the sandbox exits, workflow-pinned tooling reads archive bytes without
following symlinks, stages changed objects, and omits only objects matching the
snapshot and a public HEAD's size/MD5 ETag. HEAD is an optimization filter, not the
final integrity check. Unknown ETags, missing/corrupt objects, changed toolchains
and stale snapshots fall back to staging built bytes. Public reads share curl
connections in batches of at most 128 objects with 64 active transfers. No new
availability batch starts after 60 seconds or 32 observed misses; outstanding
HEAD requests have a 15-second timeout.

The isolated publisher rejects unrecognized map schemas, unsafe names, nested
paths, symlinks, nonregular entries, extra files and inconsistent manifests. It
GETs every omitted object and checks SHA-256, size and MD5 against the expected
record, with three attempts of at most 30 seconds per transfer. Verified objects
are retained within each batch, so retries fetch only missing/corrupt objects.
A failed batch stops further verification and prevents publication. The publisher freezes the
validated upload files and URL plan outside the hostile staging directory. Only
inline workflow shell and curl receive credentials: artifacts upload first with
bounded retries, then the full map uploads and is confirmed byte for byte using
workflow-pinned, key-free tooling. Partial artifact uploads are safe to retry;
they do not install a partial revision map. A staging tree without
`publication.json` is treated as full staging: every mapped object is hashed and
uploaded.

If an inherited object disappears after producer staging, publication fails
closed. Set repository variable `LAKE_CACHE_FULL_PUBLICATION=1` and launch a
**new producer run** to transfer every built archive and repair missing objects.
Clearing the variable restores incremental staging. Re-running only the publisher
cannot recover bytes absent from its artifact; a new producer run is required.
No credentials are given to that producer.

Staging logs report full/staged archive bytes, reused and fallback object counts,
and seconds. Publisher logs report upload bytes, SHA verification download bytes
and elapsed verification/upload time. Map/manifest and protocol overhead are not
included in archive-byte totals. Inherited SHA verification consumes downloads;
repeated IDs alone do not establish net byte or elapsed savings. Compare complete
staging, artifact transfer, verification and upload phases when measuring savings.
A workflow rerun uses the same pinned tooling as its original run; create a new
run to exercise an updated workflow.

Run regression checks with:

```bash
python3 scripts/test_lake_cache_publish.py --integration
python3 scripts/test_lake_cache_reuse.py --integration
python3 scripts/test_lake_cache_probe.py
python3 scripts/test_lake_cache_get.py
```

The publication integration test uses stock Lake and a temporary HTTPS cache with
a local certificate. It exercises actual upload workflow shell, omission, changed
objects, missing/corrupt inheritance, interrupted/retried uploads, full fallback,
fresh-checkout restoration and stale-source rejection. It uses only dummy keys
and never contacts the production write endpoint.
