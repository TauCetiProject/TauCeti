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

## Optional prepared root outputs

`bulk-unpack-cache.py` can assemble a fresh private build from a trusted immutable
seed plus the archive selection already made by native Lake. The ordinary command
keeps its existing bulk path; no workflow currently supplies `--seed`.

A caller supplying that option must authenticate the seed through the image or
payload owner, keep its source immutable for the entire operation, and keep it
outside the candidate's normalized `.lake`. A manifest alone does not establish
trust. The manifest binds the default layout, platform, official toolchain,
configuration bytes, published revision, producer revision and each module's
archive name, SHA-256 provenance and exact complete output inventory. Matching is by the exact selected archive per module;
the installer never chooses an ancestor or changes publication eligibility.
A content-stable archive may serve different native input identities. In that
case the private trace receives the selected record's input hash, exactly as stock
`leantar` writes it; its output hashes remain unchanged. The source trace schema
and original input binding must match, and the current archive must match the
seed’s SHA-256. Every other trace byte, including replayed Unicode log messages,
is preserved. A candidate change without a corresponding
selected native record still fails normal input validation and rebuilds.

Keep the order: native cache fetch, applicable repair, pre-build publication
snapshot, prepared/bulk installation, native build, audits, then publication.
All misses share one bulk extraction into private staging. Only supported,
disjoint matching seed outputs join that staging tree. The helper publishes the
combined tree before removing satisfied mappings; mappings for deleted sources
and other unsatisfied work remain. Archive bytes and the publication snapshot
remain available for ordinary restoration and reconnect.

The trusted producer supplies the complete extracted file inventory for each
module; the consumer checks its supported paths and required core outputs. Seed
files may be read-only. Candidate files have independent inodes and owner
write permission so native Lake can invalidate and rebuild them. The installer
probes the actual clone operation under its consumer UID, then uses private copies
when that operation is unsupported. Permission, space and corruption errors retain
the original records and ordinary restoration path. No shared writable cache or
candidate-to-seed hard links are introduced.

Trusted producers may call `export_seed` after a successful native main build,
using the existing pre-build snapshot. It checks the snapshot's archive digests,
extracts the recorded archives, and includes only outputs whose bytes match that
validated build. It publishes the complete seed directory at once. This API does
not run builds, choose revisions or authorize candidate publication. Image
installation and rollout require separate full-size guest validation and cost
measurements.
