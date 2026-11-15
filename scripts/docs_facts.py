#!/usr/bin/env python3
"""Export the documentation facts file served at /docs/facts.json.gz.

Progress reporting needs declaration facts that describe exactly one documented commit. Reading
them from the HTML site cannot guarantee that: the declaration index and thousands of module
pages are separate URLs, and a deploy can land between any two reads. One file, deployed with the
pages it summarizes, is read in one request and so always describes one build. See
`docs-facts.md` beside this file for the format.

`export` runs in api-docs.yml straight after doc-gen4, while its SQLite database is still on
disk, and writes `facts.json.gz` into the doc tree beside `SOURCE_SHA`. The file then travels
with that tree through the actions cache into every Pages deploy of it. `check` validates a file.

Nothing here parses Lean. Every fact comes from doc-gen4's own output: the rendered module pages
(declaration names, kinds and source links, the same markup the legacy reader used), the
declaration index (every declaration's canonical page), and the analysis database (raw docstring
text, ranges, and each module's source URL). The three are cross-checked against one another and
against git, and any disagreement refuses the export rather than writing an incomplete file.
"""

from __future__ import annotations

import argparse
import gzip
import html
import io
import json
import os
import pathlib
import re
import sqlite3
import subprocess
import sys
import tempfile
import urllib.parse

SCHEMA_VERSION = 1
FACTS_NAME = "facts.json.gz"

_SHA40 = re.compile(r"[0-9a-f]{40}")

# doc-gen4's own markup, as in TauCetiProgress's legacy HTML reader. `export` refuses a page whose
# markup stops matching rather than reading it as a page with no declarations.
_DECL_RE = re.compile(r'<div class="decl(?: [^"]*)?" id="([^"]+)">')
_KIND_RE = re.compile(r'<span class="decl_kind">([^<]+)</span>')
_GH_LINK_RE = re.compile(r'<div class="gh_link"><a href="([^"]*)">')
_NAV_LINK_RE = re.compile(r'<p class="gh_nav_link"><a href="([^"]*)">')
_SOURCE_URL_RE = re.compile(r"https://github\.com/[^/]+/[^/]+/blob/([0-9a-f]{40})/([^#?]+)")
_RANGE_RE = re.compile(r"L(\d+)-L(\d+)")


class FactsError(RuntimeError):
    """The documentation output or a facts file is unusable; nothing may be written from it."""


def _require(condition, message):
    if not condition:
        raise FactsError(message)


def encode(value) -> bytes:
    """Canonical JSON bytes: sorted keys, no insignificant whitespace, one trailing newline."""
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


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
    """Module source URLs, docstrings, ranges and rendered declarations from doc-gen4's database.

    `rendered` is `{module: {name}}` for the declarations a module page shows as declarations:
    those doc-gen4 marks for rendering, less constructors, which it renders inside their type.
    """
    _require(pathlib.Path(db_path).is_file(), f"{db_path}: doc-gen4 database not found")
    db = sqlite3.connect(f"file:{pathlib.Path(db_path).resolve()}?mode=ro", uri=True)
    try:
        sources = dict(db.execute("SELECT name, source_url FROM modules"))
        docs: dict[str, dict[str, str | None]] = {}
        ranges: dict[tuple[str, str], tuple[int, int]] = {}
        rendered: dict[str, set[str]] = {}
        rows = db.execute(
            "SELECT n.module_name, n.name, n.kind, n.render, d.text, r.start_line, r.end_line"
            " FROM name_info n"
            " LEFT JOIN declaration_markdown_docstrings d USING (module_name, position)"
            " LEFT JOIN declaration_ranges r USING (module_name, position)")
        for module, name, kind, render, text, start, end in rows:
            docs.setdefault(module, {})[name] = text
            if start is not None:
                ranges[(module, name)] = (start, end)
            if render and kind != "constructor":
                rendered.setdefault(module, set()).add(name)
    except sqlite3.Error as exc:
        raise FactsError(f"{db_path}: unreadable doc-gen4 database: {exc}") from exc
    finally:
        db.close()
    return sources, docs, ranges, rendered


def collect(doc_dir, db_path, repo, root, source_commit, docs_base):
    """The facts payload for one doc-gen4 tree, cross-checked against its index, database and git.

    Raises FactsError on any inconsistency: a file that is not provably complete and
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

    sources, db_docs, db_ranges, db_rendered = _db_rows(db_path)

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
        # A page that lost declarations would otherwise read as a module that has fewer.
        on_page = {name for name, _, _ in decls}
        wanted = db_rendered.get(module, set())
        _require(on_page == wanted,
                 f"{page}: declarations differ from the database: missing {sorted(wanted - on_page)[:5]} "
                 f"({len(wanted - on_page)}), unexpected {sorted(on_page - wanted)[:5]} "
                 f"({len(on_page - wanted)})")
        declarations = {}
        for name, kind, href in decls:
            _require(name and name not in seen_names, f"{page}: empty or duplicate declaration {name!r}")
            seen_names.add(name)
            base, _, fragment = href.partition("#")
            _require(base == source_url, f"{page}: {name} links to {base}, not the module source {source_url}")
            start = end = None
            _require(bool(fragment) == ((module, name) in db_ranges),
                     f"{page}: {name} source range presence differs from the database")
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


def pack(facts: dict) -> bytes:
    """The gzipped canonical bytes of a facts payload, identical wherever they are produced."""
    # GzipFile, not gzip.compress: from Python 3.12 the latter's header names the host OS.
    buffer = io.BytesIO()
    with gzip.GzipFile(filename="", fileobj=buffer, mode="wb", compresslevel=9, mtime=0) as stream:
        stream.write(encode(facts))
    return buffer.getvalue()


def validate(packed: bytes) -> dict:
    """Check a facts file's structure; return the payload."""
    try:
        raw = gzip.decompress(packed)
    except (OSError, EOFError) as exc:
        raise FactsError(f"facts: invalid gzip: {exc}") from exc
    data = _strict_json(raw, "facts")
    _require(data.get("schema_version") == SCHEMA_VERSION and type(data["schema_version"]) is int,
             "facts: unsupported schema_version")
    _require(isinstance(data.get("source_commit"), str)
             and _SHA40.fullmatch(data["source_commit"]) is not None, "facts: invalid source commit")
    provenance = data.get("provenance")
    _require(isinstance(provenance, dict) and all(
        isinstance(provenance.get(k), str) and provenance[k] for k in ("toolchain", "doc_gen")),
        "facts: missing toolchain/doc-gen provenance")
    modules = data.get("modules")
    _require(isinstance(modules, dict) and modules and all(_source_path(p) for p in modules),
             "facts: invalid module coverage")
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
    return data


def write_once(path, data: bytes):
    """Create `path` holding `data` in one rename, refusing to replace anything already there."""
    path = pathlib.Path(path)
    _require(not path.exists() and not path.is_symlink(), f"{path} already exists; refusing to overwrite it")
    fd, tmp = tempfile.mkstemp(prefix=".facts-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(data)
            # mkstemp creates 0600, and the mode survives the cache into the Pages artifact, where a
            # file not readable by others fails the whole deployment.
            os.fchmod(out.fileno(), 0o644)
        os.rename(tmp, path)
    finally:
        pathlib.Path(tmp).unlink(missing_ok=True)


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
    exp = sub.add_parser("export", help="write facts.json.gz from a doc-gen4 tree")
    exp.add_argument("--doc-dir", required=True)
    exp.add_argument("--db", required=True)
    exp.add_argument("--repo", required=True)
    exp.add_argument("--root", default="TauCeti")
    exp.add_argument("--docs-base", required=True)
    exp.add_argument("--toolchain-file", required=True)
    exp.add_argument("--docs-manifest", required=True, help="the docs project's lake-manifest.json")
    exp.add_argument("--out", help=f"default: <doc-dir>/{FACTS_NAME}")
    chk = sub.add_parser("check", help="validate a facts file")
    chk.add_argument("file")
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
            facts["provenance"] = {
                "toolchain": pathlib.Path(args.toolchain_file).read_text().strip(),
                "doc_gen": _doc_gen_provenance(args.docs_manifest),
            }
            packed = pack(facts)
            validate(packed)
            write_once(args.out or doc_dir / FACTS_NAME, packed)
            declarations = sum(len(d) for d in facts["modules"].values())
            print(f"exported facts for {facts['source_commit']}: {len(facts['modules'])} modules, "
                  f"{declarations} declarations, {len(packed)} bytes compressed")
        else:
            data = validate(pathlib.Path(args.file).read_bytes())
            print(f"valid facts for {data['source_commit']}")
    except FactsError as exc:
        print(f"::error title=Documentation facts::{exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
