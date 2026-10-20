#!/usr/bin/env python3
"""Export and publish immutable documentation facts generations (schema version 1).

Progress reporting needs declaration facts that describe exactly one documented source commit.
Reading them from the live documentation site cannot guarantee that: the declaration index and
thousands of module pages are separate URLs, and a deploy can land between any two reads. This
script turns one finished doc-gen4 tree into a single content-addressed object instead, and
publishes it so that a reader can pin it across later deploys. See `docs-facts.md` beside this
file for the producer/consumer contract and the deployment settings.

Three subcommands:

* `export` runs in api-docs.yml, straight after doc-gen4, while its SQLite database is still on
  disk. It writes `manifest.json` and `facts.json.gz` into the doc tree's reserved `FACTS_V1/`
  directory, so the generation travels with the tree, and with its `SOURCE_SHA`, through the
  actions cache. A Pages run that reuses an older tree therefore publishes the commit that tree
  documents, not the commit the Pages run checked out.
* `check` validates a generation directory offline, exactly as a consumer would.
* `publish` runs in pages.yml after the deploy. It uploads the immutable objects, reads them back
  from the public base, and only then replaces `v1/current.json` with one PUT.

Nothing here parses Lean. Every fact comes from doc-gen4's own output: the rendered module pages
(declaration names, kinds and source links, the same markup the legacy reader used), the
declaration index (every declaration's canonical page), and the analysis database (raw docstring
text and each module's source URL). The three are cross-checked against one another and against
git, and any disagreement refuses the export rather than publishing a partial generation.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import html
import json
import os
import pathlib
import re
import sqlite3
import subprocess
import sys
import tempfile
import time
import urllib.parse

SCHEMA_VERSION = 1
# The reserved directory inside the doc tree. Upper case, like SOURCE_SHA, so that it cannot be
# mistaken for (or collide with) anything doc-gen4 writes.
FACTS_DIR = "FACTS_V1"
FACTS_NAME = "facts.json.gz"
MANIFEST_NAME = "manifest.json"
POINTER_KEY = "v1/current.json"

IMMUTABLE_CACHE_CONTROL = "public, max-age=31536000, immutable"
POINTER_CACHE_CONTROL = "no-cache"

_SHA40 = re.compile(r"[0-9a-f]{40}")
_SHA64 = re.compile(r"[0-9a-f]{64}")
_GENERATION = re.compile(r"v1/generations/([0-9a-f]{40})/([0-9a-f]{64})")

# doc-gen4's own markup, as in TauCetiProgress's legacy HTML reader. `export` refuses a page whose
# markup stops matching rather than reading it as a page with no declarations.
_DECL_RE = re.compile(r'<div class="decl(?: [^"]*)?" id="([^"]+)">')
_KIND_RE = re.compile(r'<span class="decl_kind">([^<]+)</span>')
_GH_LINK_RE = re.compile(r'<div class="gh_link"><a href="([^"]*)">')
_NAV_LINK_RE = re.compile(r'<p class="gh_nav_link"><a href="([^"]*)">')
_SOURCE_URL_RE = re.compile(r"https://github\.com/[^/]+/[^/]+/blob/([0-9a-f]{40})/([^#?]+)")
_RANGE_RE = re.compile(r"L(\d+)-L(\d+)")


class FactsError(RuntimeError):
    """The documentation output or a generation is unusable; nothing may be published from it."""


class ConflictError(FactsError):
    """An immutable key already holds different bytes."""


def _require(condition, message, error=FactsError):
    if not condition:
        raise error(message)


def encode(value) -> bytes:
    """Canonical JSON bytes: sorted keys, no insignificant whitespace, one trailing newline."""
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _strict_json(raw: bytes, label: str):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            _require(key not in result, f"{label}: duplicate JSON key {key}")
            result[key] = value
        return result

    try:
        value = json.loads(raw, object_pairs_hook=unique)
    except (ValueError, UnicodeError) as exc:
        raise FactsError(f"{label}: invalid JSON: {exc}") from exc
    _require(isinstance(value, dict), f"{label}: expected an object")
    return value


def _source_path(value) -> bool:
    return (isinstance(value, str) and value.endswith(".lean") and not value.startswith("/")
            and "\\" not in value and all(p not in ("", ".", "..") for p in value.split("/")))


# ----- export --------------------------------------------------------------------------------


def _git(repo, *args) -> str:
    try:
        return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                              text=True).stdout
    except subprocess.CalledProcessError as exc:
        raise FactsError(f"git {' '.join(args)} failed: {exc.stderr.strip()}") from exc


def _tree_blobs(repo, commit, root) -> dict[str, str]:
    """`{path: blob}` for every Lean file under `root` at `commit`."""
    out = {}
    for line in _git(repo, "ls-tree", "-r", "-z", commit, "--", f"{root}/").split("\0"):
        if not line:
            continue
        meta, path = line.split("\t", 1)
        if path.endswith(".lean"):
            out[path] = meta.split()[2]
    return out


def _parse_page(text: str, page: str):
    """`(nav_source_url, [(name, kind, gh_link_href)])` from one rendered module page."""
    nav = _NAV_LINK_RE.search(text)
    _require(nav is not None, f"{page}: no source link in the navigation; unrecognized doc-gen4 markup")
    marks = [(m.start(), html.unescape(m.group(1))) for m in _DECL_RE.finditer(text)]
    decls = []
    for i, (pos, name) in enumerate(marks):
        segment = text[pos:marks[i + 1][0] if i + 1 < len(marks) else len(text)]
        kind = _KIND_RE.search(segment)
        link = _GH_LINK_RE.search(segment)
        _require(kind is not None and link is not None,
                 f"{page}: declaration {name} has no kind or source link; unrecognized markup")
        decls.append((name, html.unescape(kind.group(1)).strip(), html.unescape(link.group(1))))
    return html.unescape(nav.group(1)), decls


def _db_rows(db_path):
    """Module source URLs and `{module: {name: docstring}}` from doc-gen4's analysis database."""
    _require(pathlib.Path(db_path).is_file(), f"{db_path}: doc-gen4 database not found")
    db = sqlite3.connect(f"file:{pathlib.Path(db_path).resolve()}?mode=ro", uri=True)
    try:
        sources = dict(db.execute("SELECT name, source_url FROM modules"))
        docs: dict[str, dict[str, str | None]] = {}
        ranges: dict[tuple[str, str], tuple[int, int]] = {}
        rows = db.execute(
            "SELECT n.module_name, n.name, d.text, r.start_line, r.end_line FROM name_info n"
            " LEFT JOIN declaration_markdown_docstrings d USING (module_name, position)"
            " LEFT JOIN declaration_ranges r USING (module_name, position)")
        for module, name, text, start, end in rows:
            docs.setdefault(module, {})[name] = text
            if start is not None:
                ranges[(module, name)] = (start, end)
    except sqlite3.Error as exc:
        raise FactsError(f"{db_path}: unreadable doc-gen4 database: {exc}") from exc
    finally:
        db.close()
    return sources, docs, ranges


def collect(doc_dir, db_path, repo, root, source_commit, docs_base):
    """The facts payload for one doc-gen4 tree, cross-checked against its index, database and git.

    Raises FactsError on any inconsistency: a generation that is not provably complete and
    provably about `source_commit` must not exist at all.
    """
    doc_dir = pathlib.Path(doc_dir)
    _require(_SHA40.fullmatch(source_commit or "") is not None, "source commit is not a 40-character sha")
    docs_base = docs_base.rstrip("/")
    parsed = urllib.parse.urlsplit(docs_base)
    _require(parsed.scheme in ("http", "https") and parsed.netloc and not parsed.query
             and not parsed.fragment, f"invalid documentation base {docs_base!r}")

    # Coverage is what git says the documented commit contains, not what the pages happen to be.
    expected = _tree_blobs(repo, source_commit, root)
    _require(expected, f"no {root}/ Lean files at {source_commit}")

    index_path = doc_dir / "declarations" / "declaration-data.bmp"
    try:
        index = json.loads(index_path.read_bytes())
    except (OSError, ValueError) as exc:
        raise FactsError(f"{index_path}: unreadable declaration index: {exc}") from exc
    index_modules = {m: v.get("url") for m, v in (index.get("modules") or {}).items()
                     if m == root or m.startswith(root + ".")}
    index_decls = index.get("declarations")
    _require(isinstance(index_decls, dict), f"{index_path}: no declarations map")

    sources, db_docs, db_ranges = _db_rows(db_path)

    modules: dict[str, dict] = {}
    link_commits: dict[str, str] = {}
    seen_names: set[str] = set()
    for module, page_url in sorted(index_modules.items()):
        _require(isinstance(page_url, str) and page_url.startswith("./") and page_url.endswith(".html"),
                 f"index: module {module} has no page")
        page = page_url[2:]
        source_url = sources.get(module)
        match = _SOURCE_URL_RE.fullmatch(source_url or "")
        _require(match is not None, f"database: module {module} has no source URL")
        commit, path = match.group(1), urllib.parse.unquote(match.group(2))
        _require(_source_path(path) and path == page[:-5] + ".lean",
                 f"{module}: source {path} does not match page {page}")
        _require(path not in modules, f"two modules claim {path}")
        try:
            text = (doc_dir / page).read_text(encoding="utf-8")
        except OSError as exc:
            raise FactsError(f"{page}: module page missing: {exc}") from exc
        nav, decls = _parse_page(text, page)
        _require(nav == source_url, f"{page}: navigation source {nav} differs from the database's {source_url}")
        declarations = {}
        for name, kind, href in decls:
            _require(name and name not in seen_names, f"{page}: empty or duplicate declaration {name!r}")
            seen_names.add(name)
            base, _, fragment = href.partition("#")
            _require(base == source_url, f"{page}: {name} links to {base}, not the module source {source_url}")
            start = end = None
            if fragment:
                rng = _RANGE_RE.fullmatch(fragment)
                _require(rng is not None, f"{page}: {name} has an unrecognized source range {fragment}")
                start, end = int(rng.group(1)), int(rng.group(2))
                _require(1 <= start <= end, f"{page}: {name} has an invalid range {start}-{end}")
                _require(db_ranges.get((module, name)) == (start, end),
                         f"{page}: {name} range {start}-{end} differs from the database")
            entry = index_decls.get(name)
            _require(isinstance(entry, dict) and entry.get("docLink") == f"./{page}#{name}",
                     f"index: {name} does not link to {page}")
            _require(name in db_docs.get(module, {}), f"database: {name} is not recorded in {module}")
            declarations[name] = {
                "kind": kind,
                "url": f"{docs_base}/{page}#{name}",
                "file": path,
                "start": start,
                "end": end,
                "doc": (db_docs[module][name] or "").strip(),
            }
        modules[path] = declarations
        link_commits[path] = commit

    missing = sorted(set(expected) - set(modules))
    extra = sorted(set(modules) - set(expected))
    _require(not missing and not extra,
             f"module coverage differs from {source_commit}: missing {missing[:5]} "
             f"({len(missing)}), deleted but documented {extra[:5]} ({len(extra)})")

    # doc-gen4 re-analyzes only modules whose build changed, so an unchanged module keeps source
    # links naming the commit it was last analyzed at. Its facts hold at `source_commit` exactly
    # when the file is byte-identical there; anything else is a stale analysis.
    stale = {c for c in link_commits.values() if c != source_commit}
    for commit in sorted(stale):
        then = _tree_blobs(repo, commit, root)
        for path, linked in link_commits.items():
            if linked == commit:
                _require(then.get(path) == expected[path],
                         f"{path} was analyzed at {commit[:12]} and has changed since; "
                         f"its documentation does not describe {source_commit[:12]}")

    return {"schema_version": SCHEMA_VERSION, "source_commit": source_commit, "modules": modules}


def build_generation(facts: dict, provenance: dict):
    """`(manifest_bytes, facts_gz_bytes)` for a facts payload."""
    raw = encode(facts)
    packed = gzip.compress(raw, mtime=0)
    digest = sha256(packed)
    commit = facts["source_commit"]
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "source_commit": commit,
        "generation": f"v1/generations/{commit}/{digest}",
        "facts_sha256": digest,
        "compressed_bytes": len(packed),
        "uncompressed_bytes": len(raw),
        "modules": sorted(facts["modules"]),
        "provenance": provenance,
    }
    return encode(manifest), packed


def pointer_for(manifest_bytes: bytes) -> bytes:
    manifest = json.loads(manifest_bytes)
    return encode({
        "schema_version": SCHEMA_VERSION,
        "source_commit": manifest["source_commit"],
        "manifest_path": f"{manifest['generation']}/{MANIFEST_NAME}",
        "manifest_sha256": sha256(manifest_bytes),
    })


def write_generation(out_dir, manifest_bytes, packed):
    """Create `out_dir` holding exactly the two files, or leave nothing behind."""
    out = pathlib.Path(out_dir)
    _require(not out.exists() and not out.is_symlink(), f"{out} already exists; refusing to overwrite it")
    tmp = pathlib.Path(tempfile.mkdtemp(prefix=".facts-", dir=out.parent))
    try:
        (tmp / FACTS_NAME).write_bytes(packed)
        (tmp / MANIFEST_NAME).write_bytes(manifest_bytes)
        os.rename(tmp, out)
    except OSError:
        for child in tmp.iterdir():
            child.unlink()
        tmp.rmdir()
        raise


# ----- validation ----------------------------------------------------------------------------


def validate(manifest_bytes: bytes, packed: bytes) -> dict:
    """Check a generation as strictly as TauCetiProgress's reader does; return the manifest."""
    manifest = _strict_json(manifest_bytes, "manifest")
    _require(manifest.get("schema_version") == SCHEMA_VERSION
             and type(manifest.get("schema_version")) is int, "manifest: unsupported schema_version")
    commit = manifest.get("source_commit")
    _require(isinstance(commit, str) and _SHA40.fullmatch(commit) is not None, "manifest: invalid source commit")
    digest = manifest.get("facts_sha256")
    _require(isinstance(digest, str) and _SHA64.fullmatch(digest) is not None, "manifest: invalid facts hash")
    _require(manifest.get("generation") == f"v1/generations/{commit}/{digest}",
             "manifest: generation path does not match source commit and facts hash")
    _require(sha256(packed) == digest, "facts: SHA-256 does not match the manifest")
    for key in ("compressed_bytes", "uncompressed_bytes"):
        _require(type(manifest.get(key)) is int and manifest[key] > 0, f"manifest: invalid {key}")
    _require(len(packed) == manifest["compressed_bytes"], "facts: compressed length mismatch")
    provenance = manifest.get("provenance")
    _require(isinstance(provenance, dict) and all(
        isinstance(provenance.get(k), str) and provenance[k] for k in ("toolchain", "doc_gen")),
        "manifest: missing toolchain/doc-gen provenance")
    coverage = manifest.get("modules")
    _require(isinstance(coverage, list) and coverage and all(_source_path(p) for p in coverage)
             and len(coverage) == len(set(coverage)), "manifest: invalid module coverage")
    try:
        raw = gzip.decompress(packed)
    except (OSError, EOFError) as exc:
        raise FactsError(f"facts: invalid gzip: {exc}") from exc
    _require(len(raw) == manifest["uncompressed_bytes"], "facts: uncompressed length mismatch")
    data = _strict_json(raw, "facts")
    _require(data.get("schema_version") == SCHEMA_VERSION and type(data["schema_version"]) is int,
             "facts: unsupported schema_version")
    _require(data.get("source_commit") == commit, "facts: source commit mismatch")
    modules = data.get("modules")
    _require(isinstance(modules, dict) and sorted(modules) == sorted(coverage),
             "facts: module coverage differs from manifest")
    names = set()
    for path, declarations in modules.items():
        _require(isinstance(declarations, dict), f"facts: invalid module {path}")
        for name, info in declarations.items():
            _require(isinstance(name, str) and name and name not in names,
                     "facts: empty or duplicate declaration name")
            names.add(name)
            _require(isinstance(info, dict) and isinstance(info.get("kind"), str) and info["kind"]
                     and isinstance(info.get("doc"), str), f"facts: invalid kind/doc for {name}")
            url = urllib.parse.urlsplit(info.get("url") if isinstance(info.get("url"), str) else "")
            _require(url.scheme in ("http", "https") and url.netloc
                     and url.path.endswith("/" + path[:-5] + ".html") and url.fragment == name,
                     f"facts: canonical URL does not match module/declaration {name}")
            _require(info.get("file") == path, f"facts: source file mismatch for {name}")
            start, end = info.get("start"), info.get("end")
            _require("start" in info and "end" in info and (
                (start is None and end is None)
                or (type(start) is int and type(end) is int and 1 <= start <= end)),
                f"facts: invalid source range for {name}")
    return manifest


def read_generation(gen_dir):
    """`(manifest_bytes, facts_gz_bytes)` from a directory holding exactly the two files."""
    gen = pathlib.Path(gen_dir)
    _require(gen.is_dir() and not gen.is_symlink(), f"{gen}: no generation directory")
    names = sorted(p.name for p in gen.iterdir())
    _require(names == sorted([FACTS_NAME, MANIFEST_NAME]), f"{gen}: unexpected contents {names}")
    files = []
    for name in (MANIFEST_NAME, FACTS_NAME):
        path = gen / name
        _require(path.is_file() and not path.is_symlink(), f"{path}: not a regular file")
        files.append(path.read_bytes())
    return files[0], files[1]


# ----- publication ---------------------------------------------------------------------------


class CurlStore:
    """Object storage over curl: SigV4-signed reads and writes, and unsigned public reads.

    The key reaches curl on stdin, never on its command line.
    """

    def __init__(self, write_base, public_base, key, curl="curl"):
        self.write_base = write_base.rstrip("/")
        self.public_base = public_base.rstrip("/")
        self.key = key
        self.curl = curl

    def _run(self, args, url, signed, body=None):
        with tempfile.TemporaryDirectory() as tmp:
            out = pathlib.Path(tmp) / "body"
            cmd = [self.curl, "--silent", "--show-error", "--retry", "2", "--max-time", "300",
                   "--output", str(out), "--write-out", "%{http_code}"]
            config = ""
            if signed:
                cmd += ["--aws-sigv4", "aws:amz:auto:s3", "--config", "-"]
                escaped = self.key.replace("\\", "\\\\").replace('"', '\\"')
                config = f'user = "{escaped}"\n'
            if body is not None:
                src = pathlib.Path(tmp) / "upload"
                src.write_bytes(body)
                cmd += ["--upload-file", str(src)]
            cmd += [*args, url]
            proc = subprocess.run(cmd, input=config.encode(), capture_output=True)
            status = proc.stdout.decode().strip()
            if proc.returncode != 0:
                raise FactsError(f"curl failed for {url}: {proc.stderr.decode().strip()}")
            data = out.read_bytes() if out.exists() else b""
            return int(status or 0), data

    def get(self, key, public=False):
        """The object's bytes, or None when it does not exist."""
        url = f"{self.public_base if public else self.write_base}/{key}"
        status, data = self._run([], url, signed=not public)
        if status == 404:
            return None
        _require(status == 200, f"GET {url}: HTTP {status}")
        return data

    def put(self, key, data, content_type, cache_control):
        url = f"{self.write_base}/{key}"
        status, _ = self._run(["--header", f"Content-Type: {content_type}",
                               "--header", f"Cache-Control: {cache_control}"],
                              url, signed=True, body=data)
        _require(200 <= status < 300, f"PUT {url}: HTTP {status}")


def _verify_public(store, key, digest, attempts, sleep, log):
    for attempt in range(1, attempts + 1):
        data = store.get(key, public=True)
        if data is not None and sha256(data) == digest:
            return
        log(f"{key}: not yet readable with the expected hash (attempt {attempt}/{attempts})")
        if attempt < attempts:
            sleep(10)
    raise FactsError(f"{key}: the public object does not have SHA-256 {digest}")


def publish(gen_dir, expected_commit, store, attempts=6, sleep=time.sleep, log=print):
    """Publish one generation; return the pointer bytes now current.

    Order is what makes this safe to interrupt anywhere: the facts, then the manifest that names
    them, then a public read-back of both, and only then the single pointer PUT. Until that PUT,
    the previous pointer still names a complete generation, and a retry finds the objects already
    in place and continues.
    """
    manifest_bytes, packed = read_generation(gen_dir)
    manifest = validate(manifest_bytes, packed)
    _require(manifest["source_commit"] == expected_commit,
             f"the generation documents {manifest['source_commit']}, but the deployed docs are "
             f"from {expected_commit}; refusing to publish facts for documentation that is not live")
    generation = manifest["generation"]
    facts_key = f"{generation}/{FACTS_NAME}"
    manifest_key = f"{generation}/{MANIFEST_NAME}"

    existing = store.get(facts_key)
    if existing is None:
        store.put(facts_key, packed, "application/gzip", IMMUTABLE_CACHE_CONTROL)
        log(f"uploaded {facts_key} ({len(packed)} bytes)")
    else:
        _require(existing == packed, f"{facts_key} already exists with different bytes", ConflictError)
        log(f"{facts_key} already published")
    existing = store.get(manifest_key)
    if existing is None:
        store.put(manifest_key, manifest_bytes, "application/json", IMMUTABLE_CACHE_CONTROL)
        log(f"uploaded {manifest_key}")
    else:
        _require(existing == manifest_bytes, f"{manifest_key} already exists with different bytes",
                 ConflictError)
        log(f"{manifest_key} already published")

    _verify_public(store, facts_key, manifest["facts_sha256"], attempts, sleep, log)
    _verify_public(store, manifest_key, sha256(manifest_bytes), attempts, sleep, log)

    pointer = pointer_for(manifest_bytes)
    if store.get(POINTER_KEY) == pointer:
        log(f"{POINTER_KEY} already names {generation}")
        return pointer
    store.put(POINTER_KEY, pointer, "application/json", POINTER_CACHE_CONTROL)
    _require(store.get(POINTER_KEY) == pointer, f"{POINTER_KEY} did not read back as written")
    log(f"{POINTER_KEY} now names {generation}")
    return pointer


# ----- command line --------------------------------------------------------------------------


def _doc_gen_provenance(manifest_path):
    try:
        manifest = json.loads(pathlib.Path(manifest_path).read_text())
    except (OSError, ValueError) as exc:
        raise FactsError(f"{manifest_path}: unreadable Lake manifest: {exc}") from exc
    for package in manifest.get("packages", []):
        if package.get("name", "").strip("«»") == "doc-gen4":
            return f"{package.get('url')}@{package.get('rev')}"
    raise FactsError(f"{manifest_path}: no doc-gen4 package")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    exp = sub.add_parser("export", help="write a generation from a doc-gen4 tree")
    exp.add_argument("--doc-dir", required=True)
    exp.add_argument("--db", required=True)
    exp.add_argument("--repo", required=True)
    exp.add_argument("--root", default="TauCeti")
    exp.add_argument("--docs-base", required=True)
    exp.add_argument("--toolchain-file", required=True)
    exp.add_argument("--docs-manifest", required=True, help="the docs project's lake-manifest.json")
    exp.add_argument("--out", help=f"default: <doc-dir>/{FACTS_DIR}")
    chk = sub.add_parser("check", help="validate a generation directory")
    chk.add_argument("generation")
    chk.add_argument("--source-commit")
    pub = sub.add_parser("publish", help="upload a generation and advance the pointer")
    pub.add_argument("generation")
    pub.add_argument("--source-commit", required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "export":
            doc_dir = pathlib.Path(args.doc_dir)
            marker = doc_dir / "SOURCE_SHA"
            _require(marker.is_file() and not marker.is_symlink(), f"{marker}: no provenance marker")
            commit = marker.read_text()
            _require(_SHA40.fullmatch(commit.rstrip("\n")) is not None and commit.count("\n") == 1
                     and commit.endswith("\n"), f"{marker}: malformed")
            facts = collect(doc_dir, args.db, args.repo, args.root, commit.rstrip("\n"), args.docs_base)
            provenance = {
                "toolchain": pathlib.Path(args.toolchain_file).read_text().strip(),
                "doc_gen": _doc_gen_provenance(args.docs_manifest),
                "docs_base": args.docs_base.rstrip("/"),
            }
            manifest_bytes, packed = build_generation(facts, provenance)
            validate(manifest_bytes, packed)
            write_generation(args.out or doc_dir / FACTS_DIR, manifest_bytes, packed)
            manifest = json.loads(manifest_bytes)
            declarations = sum(len(d) for d in facts["modules"].values())
            print(f"exported {manifest['generation']}: {len(manifest['modules'])} modules, "
                  f"{declarations} declarations, {len(packed)} bytes compressed")
        elif args.command == "check":
            manifest = validate(*read_generation(args.generation))
            _require(args.source_commit in (None, manifest["source_commit"]),
                     f"generation documents {manifest['source_commit']}, not {args.source_commit}")
            print(f"valid generation {manifest['generation']}")
        else:
            key = os.environ.get("DOCS_FACTS_KEY", "").strip()
            write_base = os.environ.get("DOCS_FACTS_ENDPOINT", "")
            public_base = os.environ.get("DOCS_FACTS_BASE_PUBLIC", "")
            _require(key and write_base and public_base,
                     "DOCS_FACTS_KEY, DOCS_FACTS_ENDPOINT and DOCS_FACTS_BASE_PUBLIC are required")
            publish(args.generation, args.source_commit, CurlStore(write_base, public_base, key))
    except FactsError as exc:
        print(f"::error title=Documentation facts::{exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
