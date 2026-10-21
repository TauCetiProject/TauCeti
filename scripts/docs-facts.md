# Documentation facts file

Progress reporting needs, for one exact documented commit, the declarations TauCeti contains:
names, kinds, canonical documentation links, source files and line ranges, and docstrings. Read
from the HTML site, that is the declaration index plus thousands of module pages, and a deploy can
land between any two of those requests, so a reader can mix two builds. The same facts are
therefore also served as one file, `/docs/facts.json.gz`, deployed together with the pages it
summarizes. One request returns one build.

The consumer is TauCetiProgress
(https://github.com/TauCetiProject/TauCetiProgress/issues/26). A reader that needs the same facts
again later, for example to resume a report after another deploy, keeps its own copy: the site
only serves the current file.

## Format

Gzipped UTF-8 JSON with sorted keys and no insignificant whitespace:

- `schema_version`: integer 1.
- `source_commit`: the documented commit, the same as `/docs/SOURCE_SHA`.
- `provenance`: `toolchain` (the `lean-toolchain` pin) and `doc_gen` (`<repository>@<rev>`).
- `modules`: every documented source path, declaration-free modules included (as `{}`), mapped to
  `{full_name: {kind, url, file, start, end, doc}}`. `kind` is doc-gen4's rendered kind
  (`theorem`, `def`, `abbrev`, `noncomputable instance`, ...), `url` the canonical page and
  fragment under the documentation base, `start`/`end` inclusive 1-based lines (both null when
  doc-gen4 has no range), and `doc` the raw docstring source text (empty when none).

Declarations are the ones doc-gen4 renders as declarations on module pages, as the legacy HTML
reader saw them: compiler-generated ones (`deriving` instances and their fields) are included,
constructors and structure fields (rendered inside their parent) are not.
`docs_facts_fixture/facts.json` is the uncompressed file for real doc-gen4 output of three small
modules; `scripts/test_docs_facts.py` keeps it current.

## Producer

`scripts/docs_facts.py export` runs in `api-docs.yml` right after doc-gen4 and reads only its
output: the module pages, `declarations/declaration-data.bmp` and the `api-docs.db` analysis
database. No Lean runs and no source is parsed. It refuses, and writes nothing, unless:

- the documented modules are exactly the `TauCeti/` Lean files at `SOURCE_SHA`;
- each page shows exactly the declarations the database marks for rendering (less constructors),
  each appears in the index at that page, ranges agree with the database (including whether there
  is one), and every source link names its module's database source URL;
- every module analyzed at an older commit (doc-gen4 analysis is incremental) is byte-identical
  at `SOURCE_SHA`.

The file is written beside `SOURCE_SHA`, so it is cached and deployed with the tree it describes,
including when a Pages run reuses an older tree. A failed export only leaves the file out of that
tree, with a warning; the documentation still deploys, readers fall back to the HTML pages, and
the next hourly `api-docs.yml` run exports again. Set the repository variable `DOCS_BASE_URL` to
change the documentation base used in `url` (default `https://taucetiproject.org/docs`).
