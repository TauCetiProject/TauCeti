# Lake artifact cache infrastructure

Where the build cache lives, who owns it, and which knob feeds which workflow.

## Mathlib download cache (GitHub Actions)

The main `ci.yml` workflow maintains a narrow snapshot of Mathlib's compressed download store:
`$MATHLIB_CACHE_DIR/*.ltar`. The `.ltar` files are content-addressed; cache-tool scratch files,
executables, and the unpacked `.lake` tree are not included. The local
`.github/actions/restore-mathlib-ltars` action sets `MATHLIB_CACHE_DIR` job-wide through
`$GITHUB_ENV`, defaulting to `$GITHUB_WORKSPACE/.mathlib-ltar-cache`; its `cache-dir` input can
override that location. Main publishes only after a non-exact restore: an exact key is immutable
and already contains this pin's snapshot. Before publishing, main runs `lake exe cache clean` so
the snapshot contains only files needed by the current pin; if pruning fails, it skips publication
instead of saving an unpruned snapshot. PR and merge-group jobs in `pr-build.yml` may restore this
trusted snapshot but never publish one. `pages.yml` and
`pr-profile.yml` are intentionally outside this initial rollout: `ci.yml` is included as the sole
publisher and `pr-build.yml` as the highest-volume consumer. `pr-profile.yml` has comparable
per-PR fetch volume but remains outside as a rollout control. Both excluded workflows continue
fetching into Mathlib's default cache directory.

Keys have the shape
`mathlib-ltar-v1-<os>-<arch>-<lean-toolchain hash>-<lake-manifest hash>`. An exact match reuses the
current pin. The restore prefix omits the manifest hash, so a Mathlib-only pin bump can start from
the newest snapshot for the same Lean toolchain and fetch only missing files. A toolchain bump has
no prefix match. In every case, `lake exe cache get` remains authoritative and downloads whatever
the snapshot lacks. This design mirrors Mathlib's own cache-snapshot warming in
`.github/workflows/build_template.yml` and `.github/actions/get-cache`, using `actions/cache`
instead of per-run artifacts.

GitHub Actions cache entries are immutable. If an entry is poisoned or the format becomes
incompatible, bump `mathlib-ltar-v1` once in
`.github/actions/restore-mathlib-ltars/action.yml`. To discard a single entry instead, find it with
`gh cache list --repo TauCetiProject/TauCeti` and delete its exact key with
`gh cache delete <key> --repo TauCetiProject/TauCeti`. A failed fetch also retries once with
`lake exe cache get!`, which forces every linked file to be downloaded and unpacked again.

Downloads go to the cache tool's default read endpoint. The escape hatch is a repository
variable. Every workflow that runs `lake exe cache get` (`ci.yml`, `pr-build.yml`,
`pr-profile.yml`, `nightly-verify.yml`, `pages.yml`) exports
`MATHLIB_CACHE_DEBUG_USE_LEGACY` from `vars.MATHLIB_CACHE_DEBUG_USE_LEGACY`. An operator
sets the variable to `1` to send reads back to the legacy storage endpoint, and clears it
to return to the default endpoint. Both changes apply on the next run, with no code
change: the tool treats unset, empty, `0`, and `false` alike as off. Local and radar runs
need no wiring; the cache tool reads the variable from the caller's environment.

The flag is temporary. It exists only for an easy rollback during the transition to the
default endpoint that leanprover-community/mathlib4@03616a12 introduced, and upstream
plans to retire it together with direct reads from the storage account. Remove this
wiring when the pinned cache tool drops the flag.

## Cloudflare account

The 2026 account migration is complete. The live bucket, zone, custom domain,
repository variables, and publisher credential are all in the dedicated
TauCeti account. The source bucket in the personal account was deleted after
anonymous reads and an exact trusted publication succeeded.

| | |
|---|---|
| Account | `tauceti` (accessible to `kim@lean-fro.org`) |
| Account ID | `ec2169bdf033f56b009956d4b64ba8ef` |
| Dashboard | https://dash.cloudflare.com/ec2169bdf033f56b009956d4b64ba8ef |
| R2 bucket | `tauceti-cache` |
| Registrar | `taucetiproject.org`, bought through Cloudflare Registrar in this same account |

The account ID is not a secret: it is the subdomain of the S3 endpoint below. If the dashboard
link 404s, the login you used is not a member of that account.

This account is the TauCeti boundary. It should contain no Hex or Palomar resources.

## Endpoints

Reads are anonymous. Lake's download path issues plain unauthenticated `curl` GETs and has no way
to sign them, so the read host must be public; only uploads use a key.

| Purpose | Value | Used by |
|---|---|---|
| `LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC` | `https://cache.taucetiproject.org/artifacts` | `pr-build.yml` read |
| `LAKE_CACHE_REVISION_ENDPOINT_PUBLIC` | `https://cache.taucetiproject.org/revisions` | `pr-build.yml` read |
| `LAKE_CACHE_ARTIFACT_ENDPOINT` | `https://ec2169bdf033f56b009956d4b64ba8ef.r2.cloudflarestorage.com/tauceti-cache/artifacts` | `ci.yml` upload |
| `LAKE_CACHE_REVISION_ENDPOINT` | `https://ec2169bdf033f56b009956d4b64ba8ef.r2.cloudflarestorage.com/tauceti-cache/revisions` | `ci.yml` upload |
| `LAKE_CACHE_KEY` (secret) | `<ACCESS_KEY_ID>:<SECRET>`, read-write | `ci.yml`, `publish-lake-cache` job only |

Lake service names: `tauceti-public` for reads, `tauceti-r2` for uploads. Object keys are
`artifacts/TauCetiProject/TauCeti/<hash>.art`, so the endpoint variables hold only the prefix and
Lake appends the scope.

## Publisher credential

The GitHub Actions secret `LAKE_CACHE_KEY` contains the S3 access-key pair for
the non-expiring Cloudflare token named **TauCeti Lake cache R2 publisher**.
The token belongs to the `tauceti` account and is restricted to object
read/write/list access in `tauceti-cache`; it has no bucket-administration,
Worker, DNS, Registrar, or billing authority.

When rotating it, create the replacement in the `tauceti` account, install the
new `<ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>` pair as `LAKE_CACHE_KEY`, and let an
isolated `publish-lake-cache` job publish an exact revision before revoking the
old token. Do not put the token value in a repository variable or expose it to
the build job.

## Contributors

The read endpoints above are anonymous and are not secrets, so `scripts/lake-cache-get.sh` defaults
to them and a contributor needs no configuration:

```bash
bash scripts/lake-cache-get.sh .
```

This is the second half of a working local build and the README documents it as such. Skipping it
does not fail anything; it compiles the whole library from source instead, which is why its absence
went unnoticed for as long as it did. CI keeps passing the endpoints explicitly from the
`LAKE_CACHE_*_PUBLIC` repo variables and reaches the script only when those are set, so the defaults
never decide what CI does.

Anything else reading this cache, including the worker exemplar in
[`TauCetiProject/TauCetiWorker`](https://github.com/TauCetiProject/TauCetiWorker), must use the custom domain rather
than the bucket's `pub-<id>.r2.dev` development URL. Public access on that development URL is off and
it answers 401 for every path, which a caller whose cache miss is non-fatal cannot tell from a cold
revision.

## Why the upload is its own job

`ci.yml` publishes in two jobs. `build` compiles main and *stages* the artifacts; the separate
`publish-lake-cache` job holds `LAKE_CACHE_KEY` and uploads them. The split is a trust boundary,
not a convenience.

`build` runs `lake build` unsandboxed, as the runner user, on whatever landed on main, and Lean
executes code at elaboration time. `run_cmd`, `initialize` and macro-time IO are all unrestricted:
the scope, import-boundary and `set_option` guards are textual scans, and a file that writes
during elaboration exits 0 with no diagnostic. Such code runs with the runner user's privileges,
so it can rewrite `$HOME/.elan/bin/lake`, prepend a directory to every later step's `PATH` through
`$GITHUB_PATH`, or set `LD_PRELOAD` or `BASH_ENV` for every later step through `$GITHUB_ENV`.
Hardening the individual commands that touch the key does not help: any secret placed in a later
step of that job is a secret placed in reach of code that landed on main. (This is not reachable
from an unmerged PR, which compiles only under bwrap in `pr-build.yml`, with writes confined to
`pr/.lake` and no secret in the sandbox's `--env` allowlist.)

After the build and audits, stock Lake validates the current inputs and emits the complete
revision map with `--no-build --rehash`. The workflow-pinned `lake_cache_publish.py stage`
planner compares archive bytes with the downloaded records saved before candidate code ran.
It stages changed archives and availability-check misses, retaining the full map and a digest
manifest for inherited objects. Anonymous HEAD checks are an optimization filter; their size/MD5
ETags are not the publisher's final integrity check. Merge-group staging runs on the host after
the sandbox exits. Ordinary PR outputs never enter shared publication.

The flat staging directory is passed to the reusable `publish-lake-cache` workflow as a workflow
artifact. The publisher has no Lake workspace or project dependencies. Only `lean-toolchain`
comes from the immutable revision being published; the planning, probe and file helpers are
checked out at `github.workflow_sha`. The pin must name an official `leanprover/lean4:` release
and match the reported toolchain. Neither the reported values nor the staged data are trusted.

Before credentials are present, the workflow-pinned planner's `prepare()` validates the map
schema and hash/archive names, rejects symlinks, nesting, nonregular files and extra entries,
and checks that the manifest and staged objects cover the full map consistently. It hashes
staged objects itself and GETs every inherited object from the public endpoint, verifying its
SHA-256, MD5 and size. Public reads share connections in bounded batches; failed transfers or
digest mismatches get bounded retries, and a failed batch prevents publication. A staging tree
without a manifest is full staging, so every mapped object must be present and is hashed.

The planner freezes the validated files and URL plan outside the staging tree. Only inline
workflow shell and curl execute in the credential-bearing step: all required artifact uploads
finish first, then the complete map uploads. A separate, key-free step confirms the map's exact
bytes on the public endpoint. No candidate code or repository helper executes with the upload
key, and partially uploaded artifacts never install a partial revision map.

The publisher constructs the scope from the immutable revision and independently checked
pin: `revisions/TauCetiProject/TauCeti/tc/leanprover--lean4---<version>/<rev>.jsonl`.
The platform is absent because `lakefile.toml` sets `platformIndependent = true`; staging fails
if that stops being true or if `fixedToolchain`/`bootstrap` would remove the toolchain scope.
This keeps publication aligned with the scopes consumers read without loading a workspace in
the publisher.

Digests establish byte integrity; the existing exact-candidate builds and audits establish
proof correctness and producer eligibility. If inherited bytes disappear after staging,
publication fails closed. A new producer run with `LAKE_CACHE_FULL_PUBLICATION=1` transfers all
built objects to repair the cache. See [incremental publication operations](../scripts/lake-cache-publication.md)
for the fallback bounds, retry behavior and byte/time fields to compare.

## Why a custom domain

Cloudflare rate-limits `r2.dev` public bucket URLs and documents them as development-only
(https://developers.cloudflare.com/r2/buckets/public-buckets/); exceeding the limit returns HTTP 429
with Cloudflare error 1015
(https://developers.cloudflare.com/support/troubleshooting/http-status-codes/cloudflare-1xxx-errors/).
An R2 custom domain carries no such limit, so reads go through `cache.taucetiproject.org`. The
bucket's `r2.dev` URL is disabled, so there is nothing to silently fall back to.

A custom domain requires the zone in the same Cloudflare account as the bucket
(https://developers.cloudflare.com/r2/buckets/public-buckets/#add-your-domain-to-cloudflare).
Attaching only a subdomain while keeping DNS elsewhere needs Business (partial CNAME setup,
https://developers.cloudflare.com/dns/zone-setups/partial-setup/) or Enterprise (subdomain zone,
https://developers.cloudflare.com/dns/zone-setups/subdomain-setup/), hence a domain registered
in-account.

## Edge cache

`.art` is not one of the extensions Cloudflare caches by default
(https://developers.cloudflare.com/cache/concepts/default-cache-behavior/), so artifact reads are
cached by an explicit Cache Rule. Dashboard: Caching, then Cache Rules, on the
`taucetiproject.org` zone.

Rule expression:

```
(http.host eq "cache.taucetiproject.org" and starts_with(http.request.uri.path, "/artifacts/"))
```

Settings: cache eligibility "Eligible for cache"; Edge TTL "Ignore cache-control header and use
this TTL", one month. Browser TTL left at the default.

The rule is scoped to `/artifacts/` on purpose. Those keys are immutable content hashes, so a long
TTL is always safe. `/revisions/` is deliberately left uncached: a lookup for a revision that has
not been published yet returns 404, and a long-cached 404 would hide it from a later build once
main publishes it. Revision lookups are a handful of requests per build against a thousand or more
artifact fetches, so nothing is lost by leaving them alone.

Tiered Cache is a separate per-zone toggle and is not part of the rule above: Cloudflare documents
it as something you enable, under Caching, then Tiered Cache
(https://developers.cloudflare.com/cache/how-to/tiered-cache/). Smart topology is available on
every plan and needs no further configuration once Tiered Cache is on. Check the toggle on the
`taucetiproject.org` zone rather than assuming it; the Cache Rule above is what does the work
either way.

To check the rule is live, request the same artifact twice. `curl -I` works as well as a GET:
Cloudflare converts a cacheable `HEAD` into a `GET`, fetching and caching the full response and
returning only the headers (https://developers.cloudflare.com/cache/concepts/cache-behavior/), so a
`HEAD` reports the same `cf-cache-status` a `GET` would.

```bash
U=https://cache.taucetiproject.org/artifacts/TauCetiProject/TauCeti/<hash>.art
curl -s -o /dev/null -D - "$U" | grep -i cf-cache-status   # MISS on the first request
curl -s -o /dev/null -D - "$U" | grep -i cf-cache-status   # HIT on the second
```

`DYNAMIC` means the expression is not matching; `BYPASS` means something overrides it.
The hit ratio that actually determines the saving is under Caching, then Analytics.

## Cost

Egress from R2 is free. Reads are Class B operations: 10M per month free, then $0.36 per million
(https://developers.cloudflare.com/r2/pricing/, standard storage, prices read 2026-08-04).

Measured 2026-08-04:

| | |
|---|---|
| Artifacts fetched per build | 1,224 |
| Mean artifact size | 14 KiB, so about 17 MiB per build across those 1,224 fetches |
| `pr-build` runs per day | 734 |
| Class B reads | about 27M per month |
| Billable after the 10M free tier | about 17M, so roughly **$6 per month** |
| Egress | about 375 GB per month, free |
| Storage and Class A writes | a few GB and well inside the 1M free writes, so negligible |

Treat that as a range of roughly $4 to $9. The run count came from one busy day, and the artifact
count per build varies with how much of the dependency cone a PR invalidates.

To re-estimate, take an artifact count from any `sandboxed-build` job and a day's run count:

```bash
JOB=$(gh run view --repo TauCetiProject/TauCeti <run-id> \
        --json jobs -q '.jobs[]|select(.name=="sandboxed-build")|.databaseId' | head -1)
gh run view --repo TauCetiProject/TauCeti --job "$JOB" --log | grep -c 'downloaded artifact'
gh api -X GET repos/TauCetiProject/TauCeti/actions/workflows/pr-build.yml/runs \
  -f created=YYYY-MM-DD -q .total_count
```

Then reads per month is roughly `artifacts x runs_per_day x 30`, and the bill is
`max(0, reads - 10e6) / 1e6 x $0.36`.

That arithmetic charges every artifact fetch as a Class B read, so it is the bill without the edge
cache, and an upper bound on the real one. A custom domain puts Cloudflare Cache in front of the
bucket (https://developers.cloudflare.com/r2/buckets/public-buckets/#caching), and the Cache Rule
under [Edge cache](#edge-cache) is what claims that saving: a request answered at the edge never
reaches R2 and so is never billed as a Class B operation. The hit ratio under Caching, then
Analytics says how much of the 27M is still reaching the bucket.

## Related

- `scripts/lake-cache-get.sh` keeps hash-verified artifacts while retrying only
  missing downloads. If all three attempts remain incomplete, it discards the
  partial cache rather than handing it to the offline sandbox.
- https://github.com/leanprover/lean4/issues/14670, open: Lake fails a build over a cache miss it
  has already recovered from.
- https://github.com/leanprover/lean4/pull/14651, merged: `lake cache get` exit status was
  unreliable. Ships in v4.34.0, not backported to v4.33.0.
