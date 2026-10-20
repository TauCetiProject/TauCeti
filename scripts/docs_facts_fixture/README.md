# Documentation facts fixture

Fixtures for `scripts/test_docs_facts.py`; the contract is in `scripts/docs-facts.md`.

- `sources.json`, `doc/` and `api-docs.sql` are real doc-gen4 output. A three-module Lake project
  (`Demo/A.lean`, the declaration-free `Demo/Empty.lean`, and `Demo/Sub/B.lean`) was documented
  with the doc-gen4 revision pinned in `docbuild/lakefile.toml`, on `lean-toolchain`, with
  `DOCGEN_LOCAL_MODULE_ROOTS=Demo`. `doc/` holds its module pages and declaration index;
  `api-docs.sql` holds the `modules`, `name_info`, `declaration_markdown_docstrings` and
  `declaration_ranges` rows of its `api-docs.db` (type blobs emptied). Source links name the
  recorded commit `937b7d87c3dec2f992a6791337a04a2cafd0d243`, which the tests replace.
- `published/` is the generation and pointer this producer emits for that output, laid out as
  served from a facts base, plus the uncompressed `facts.json`. Regenerate it with
  `python3 scripts/test_docs_facts.py --regenerate`.
- `contract/` is TauCetiProgress's consumer fixture (`tests/fixtures/facts-v1` at
  081eaa8d3f3a0faa7a7264824f617918de517d70), copied unchanged.
