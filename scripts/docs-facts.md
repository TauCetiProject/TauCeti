# Immutable documentation facts (v1)

Progress reporting reads declaration facts (names, kinds, canonical documentation links, source
files and line ranges, docstrings) for one exact documented commit. The HTML site cannot promise
that: its index and module pages are independent URLs that a deploy can replace between two
reads. Each documentation build therefore also exports one compact, content-addressed
*generation*, and a single mutable pointer names the newest complete one. A reader saves the
generation it planned against and can read it again after later deploys.

This file is the producer side of the contract. The consumer is TauCetiProgress
(https://github.com/TauCetiProject/TauCetiProgress/issues/26, `progress/immutable_docs.py`).

## Layout

Everything lives under a public facts base (repository variable `DOCS_FACTS_BASE_PUBLIC`):

```text
v1/current.json                                              the only mutable object
v1/generations/<source_commit>/<facts_sha256>/facts.json.gz  immutable
v1/generations/<source_commit>/<facts_sha256>/manifest.json  immutable
```

All JSON is UTF-8 with sorted keys, no insignificant whitespace and one trailing newline. Hashes
are lowercase SHA-256 of the exact published bytes.

- `current.json`: `schema_version` (integer 1), `source_commit` (40-character lowercase sha),
  `manifest_path` (relative to the base) and `manifest_sha256`.
- `manifest.json`: `schema_version`, `source_commit`, `generation` (the directory holding it),
  `facts_sha256` (of the **compressed** bundle), `compressed_bytes`, `uncompressed_bytes`,
  `modules` (sorted source paths of every documented module, declaration-free ones included) and
  `provenance` (`toolchain`, `doc_gen` as `<repository>@<rev>`, and `docs_base`).
- `facts.json.gz`: gzip of `{"schema_version", "source_commit", "modules"}`, where `modules` maps
  each covered source path to `{full_name: {kind, url, file, start, end, doc}}`. `kind` is
  doc-gen4's rendered kind (`theorem`, `def`, `abbrev`, `noncomputable instance`, ...), `url` the
  canonical page and fragment under the documentation base, `start`/`end` inclusive 1-based lines
  (both null when doc-gen4 has no range), `doc` the raw docstring source text (empty when none).
  A declaration-free module maps to `{}`. Manifest and bundle coverage agree exactly.

Declarations are the ones doc-gen4 renders as declarations on module pages, as the legacy HTML
reader saw them: compiler-generated ones (`deriving` instances and their fields) are included,
constructors and structure fields (rendered inside their parent) are not.

`docs_facts_fixture/published/` is a complete generation and pointer produced by this exporter
from real doc-gen4 output; `docs_facts_fixture/contract/` is the consumer's own fixture, which
this producer reproduces byte for byte. `scripts/test_docs_facts.py` checks both.

## Producer

`scripts/docs_facts.py export` runs in `api-docs.yml` right after doc-gen4, reading only its
output: the module pages, `declarations/declaration-data.bmp` and the `api-docs.db` analysis
database. No Lean runs and no source is parsed. It refuses, and exports nothing, unless:

- the documented modules are exactly the `TauCeti/` Lean files at `SOURCE_SHA`;
- every page declaration appears in the index at that page and in the database for that module,
  with matching ranges, and every source link names its module's database source URL;
- every module analyzed at an older commit (doc-gen4 analysis is incremental) is byte-identical
  at `SOURCE_SHA`.

The generation is written into the doc tree's reserved `FACTS_V1/` directory, so it is cached
with the `SOURCE_SHA` it describes. `pages.yml` removes it from the deployed site and, after the
deploy and the `docgen` update, `publish-docs-facts` publishes it with
`scripts/docs_facts.py publish`:

1. validate the generation as strictly as the consumer does, and require its source commit to be
   the deployed tree's `SOURCE_SHA` (not the Pages run's checkout);
2. PUT `facts.json.gz`, then `manifest.json`, unless already present with identical bytes;
   different bytes at an immutable key are an error;
3. read both back from the public base and check their hashes;
4. replace `v1/current.json` with one PUT (`Cache-Control: no-cache`), then read it back.

An interruption before step 4 leaves the pointer on the last good generation; the objects already
written are reused by the next attempt. Republishing an unchanged tree writes nothing.

## Failure, retry and rollback

Facts never block the documentation. A failed export saves the docs tree without `FACTS_V1/`
(warning in `api-docs.yml`; the next hourly run exports again). A missing generation or failed
publication fails only `publish-docs-facts`, after the deploy; `report-data-freshness` turns the
Pages run red, which the stuck-alerts failing-scheduler check reports, and the next scheduled
Pages run (every three hours) retries. Rollback: remove the `publish-docs-facts` job or clear the
variables below. Published generations and the last pointer stay where they are.

## Deployment

- `DOCS_FACTS_ENDPOINT`: S3-compatible write URL of the facts prefix, for example
  `https://<account>.r2.cloudflarestorage.com/tauceti-cache/docs-facts`.
- `DOCS_FACTS_BASE_PUBLIC`: the same prefix's public URL, for example
  `https://cache.taucetiproject.org/docs-facts`.
- secret `DOCS_FACTS_KEY` (`<access key id>:<secret>`), defaulting to `LAKE_CACHE_KEY`.
- optional `DOCS_BASE_URL`: documentation base for canonical URLs (default
  `https://taucetiproject.org/docs`).

Unconfigured, `publish-docs-facts` logs a notice and succeeds. The producer never deletes. Any
storage lifecycle rule on `v1/generations/` must keep objects for at least 30 days, and must not
expire the generation `v1/current.json` names; a reader whose pinned generation has expired must
replan rather than advance.
