#!/usr/bin/env python3
"""Tests for scripts/docs_facts.py, the immutable documentation facts producer.

Run with: python3 scripts/test_docs_facts.py
Regenerate the published fixture with: python3 scripts/test_docs_facts.py --regenerate

`docs_facts_fixture/doc/` and `api-docs.sql` are real doc-gen4 output (the pinned revision in
docbuild/lakefile.toml) for the three small modules in `sources.json`; see the fixture README. The
tests rebuild that source history in a temporary git repository with fixed dates, so its commits
are reproducible, and substitute the commit into the recorded source links.
`docs_facts_fixture/contract/` is TauCetiProgress's consumer fixture, byte for byte.
"""

import contextlib
import gzip
import hashlib
import io
import json
import os
import pathlib
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import threading
import unittest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import docs_facts as facts  # noqa: E402

FIXTURE = pathlib.Path(__file__).resolve().parent / "docs_facts_fixture"
RECORDED_COMMIT = "937b7d87c3dec2f992a6791337a04a2cafd0d243"
DOCS_BASE = "https://taucetiproject.org/docs"
PROVENANCE = {"toolchain": "leanprover/lean4:v4.36.0-rc1",
              "doc_gen": "https://github.com/kim-em/doc-gen4@d25c28427ff9693ea711584a7037da22cdeee1c8",
              "docs_base": DOCS_BASE}
REGENERATE = "--regenerate" in sys.argv
if REGENERATE:
    sys.argv.remove("--regenerate")

GIT_ENV = {"GIT_AUTHOR_NAME": "Fixture", "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
           "GIT_COMMITTER_NAME": "Fixture", "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
           "GIT_AUTHOR_DATE": "2026-10-20T00:00:00Z", "GIT_COMMITTER_DATE": "2026-10-20T00:00:00Z",
           "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}


class Workspace:
    """A git repository holding the fixture sources, and a doc tree whose links name a commit."""

    def __init__(self, root: pathlib.Path):
        self.root = root
        self.repo = root / "repo"
        self.repo.mkdir()
        self.git("init", "-q", "-b", "main")
        for path, text in json.loads((FIXTURE / "sources.json").read_text()).items():
            self.write(path, text)
        self.analyzed = self.commit("sources")

    def git(self, *args):
        env = {**os.environ, **GIT_ENV}
        return subprocess.run(["git", "-C", str(self.repo), *args], check=True, env=env,
                              capture_output=True, text=True).stdout.strip()

    def write(self, path, text):
        target = self.repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def commit(self, message):
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def docs(self, source_commit=None):
        """A doc tree and database as doc-gen4 left them after analyzing `self.analyzed`."""
        doc = self.root / "doc"
        if doc.exists():
            shutil.rmtree(doc)
        shutil.copytree(FIXTURE / "doc", doc)
        for page in doc.rglob("*.html"):
            page.write_text(page.read_text().replace(RECORDED_COMMIT, self.analyzed))
        (doc / "SOURCE_SHA").write_text((source_commit or self.analyzed) + "\n")
        db = self.root / "api-docs.db"
        db.unlink(missing_ok=True)
        conn = sqlite3.connect(db)
        conn.executescript((FIXTURE / "api-docs.sql").read_text().replace(RECORDED_COMMIT, self.analyzed))
        conn.commit()
        conn.close()
        return doc, db

    def collect(self, source_commit=None):
        doc, db = self.docs(source_commit)
        return facts.collect(doc, db, self.repo, "Demo", source_commit or self.analyzed, DOCS_BASE)


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.ws = Workspace(pathlib.Path(self.tmp.name))

    def tearDown(self):
        self.tmp.cleanup()

    def test_facts_agree_with_the_index_and_module_pages(self):
        data = self.ws.collect()
        doc, _ = self.ws.docs()
        index = json.loads((doc / "declarations" / "declaration-data.bmp").read_text())
        modules = data["modules"]
        self.assertEqual(sorted(modules), ["Demo/A.lean", "Demo/Empty.lean", "Demo/Sub/B.lean"])
        for path, declarations in modules.items():
            page = path[:-5] + ".html"
            html = (doc / page).read_text()
            for name, info in declarations.items():
                self.assertIn(f'<div class="decl" id="{name}">', html)
                self.assertEqual(index["declarations"][name]["docLink"], f"./{page}#{name}")
                self.assertEqual(info["url"], f"{DOCS_BASE}/{page}#{name}")
                self.assertEqual(info["file"], path)
                self.assertIn(f'blob/{self.ws.analyzed}/{path}#L{info["start"]}-L{info["end"]}', html)
            self.assertEqual(html.count('<div class="decl" id="'), len(declarations))

    def test_generated_declarations_kinds_and_docstrings(self):
        a = self.ws.collect()["modules"]["Demo/A.lean"]
        # `deriving` output is compiler-generated and still carries the deriving clause's line.
        self.assertEqual(a["Demo.instReprPoint"]["kind"], "instance")
        self.assertEqual((a["Demo.instReprPoint"]["start"], a["Demo.instReprPoint"]["end"]), (23, 23))
        self.assertEqual(a["Demo.instReprPoint.repr"]["kind"], "def")
        # The rendered kind, as the legacy reader saw it, not the database's coarser one.
        self.assertEqual(a["Demo.Short"]["kind"], "abbrev")
        # Raw source documentation, not rendered HTML.
        self.assertEqual(a["Demo.alpha"]["doc"],
                         "**Alpha's theorem.** It states `True`.\n\nA second paragraph.")
        self.assertEqual(a["Demo.undocumented"]["doc"], "")
        # Constructors and structure fields are rendered inside their parent, not as declarations.
        for name in ("Demo.Point.mk", "Demo.Point.x", "Demo.Colour.red"):
            self.assertNotIn(name, a)

    def test_empty_module_is_covered(self):
        self.assertEqual(self.ws.collect()["modules"]["Demo/Empty.lean"], {})

    def test_source_link_without_range_gives_null_range(self):
        doc, db = self.ws.docs()
        page = doc / "Demo" / "Sub" / "B.html"
        page.write_text(page.read_text().replace("B.lean#L9-L10", "B.lean"))
        with self.assertRaisesRegex(facts.FactsError, "range presence"):
            facts.collect(doc, db, self.ws.repo, "Demo", self.ws.analyzed, DOCS_BASE)
        conn = sqlite3.connect(db)
        conn.execute("DELETE FROM declaration_ranges WHERE module_name = 'Demo.Sub.B' AND position = 0")
        conn.commit()
        conn.close()
        data = facts.collect(doc, db, self.ws.repo, "Demo", self.ws.analyzed, DOCS_BASE)
        beta = data["modules"]["Demo/Sub/B.lean"]["Demo.Sub.beta"]
        self.assertEqual((beta["start"], beta["end"]), (None, None))
        facts.validate(*facts.build_generation(data, PROVENANCE))

    def test_reused_analysis_documents_a_later_unchanged_commit(self):
        self.ws.write("README.md", "unrelated\n")
        later = self.ws.commit("unrelated")
        data = self.ws.collect(later)
        self.assertEqual(data["source_commit"], later)
        self.assertEqual(data["modules"], self.ws.collect()["modules"])

    def test_stale_analysis_of_a_changed_module_is_refused(self):
        self.ws.write("Demo/Sub/B.lean", "module\n")
        later = self.ws.commit("edit")
        with self.assertRaisesRegex(facts.FactsError, "Demo/Sub/B.lean was analyzed at"):
            self.ws.collect(later)

    def test_deleted_module_still_documented_is_refused(self):
        (self.ws.repo / "Demo" / "Empty.lean").unlink()
        later = self.ws.commit("delete")
        with self.assertRaisesRegex(facts.FactsError, "deleted but documented.*Demo/Empty.lean"):
            self.ws.collect(later)

    def test_undocumented_module_is_refused(self):
        self.ws.write("Demo/New.lean", "module\n")
        later = self.ws.commit("add")
        with self.assertRaisesRegex(facts.FactsError, "missing.*Demo/New.lean"):
            self.ws.collect(later)

    def test_page_missing_declarations_is_refused(self):
        doc, db = self.ws.docs()
        page = doc / "Demo" / "A.html"
        text = page.read_text()
        start = text.index('<div class="decl" id="Demo.Short">')
        end = text.index('<div class="decl" id="Demo.secret">')
        page.write_text(text[:start] + text[end:])
        with self.assertRaisesRegex(facts.FactsError, r"missing \['Demo.Short'\]"):
            facts.collect(doc, db, self.ws.repo, "Demo", self.ws.analyzed, DOCS_BASE)
        main_start = text.index("<main>")
        page.write_text(text[:main_start] + "<main></main>" + text[text.index("</main>") + 7:])
        with self.assertRaisesRegex(facts.FactsError, r"declarations differ.*\(14\)"):
            facts.collect(doc, db, self.ws.repo, "Demo", self.ws.analyzed, DOCS_BASE)

    def test_missing_module_page_is_refused(self):
        doc, db = self.ws.docs()
        (doc / "Demo" / "Empty.html").unlink()
        with self.assertRaisesRegex(facts.FactsError, "module page missing"):
            facts.collect(doc, db, self.ws.repo, "Demo", self.ws.analyzed, DOCS_BASE)

    def test_inconsistent_outputs_are_refused(self):
        cases = [
            ("Demo/A.html", "#L13-L16", "#L13-L17", "differs from the database"),
            ("Demo/A.html", '<span class="decl_kind">theorem</span>', "", "no kind or source link"),
            ("Demo/Empty.html", '<p class="gh_nav_link">', "<p>", "no source link in the navigation"),
            ("declarations/declaration-data.bmp", "./Demo/Sub/B.html#Demo.Sub.beta",
             "./Demo/A.html#Demo.Sub.beta", "does not link to"),
        ]
        for rel, old, new, message in cases:
            with self.subTest(rel=rel, message=message):
                doc, db = self.ws.docs()
                target = doc / rel
                text = target.read_text()
                self.assertIn(old, text)
                target.write_text(text.replace(old, new, 1))
                with self.assertRaisesRegex(facts.FactsError, message):
                    facts.collect(doc, db, self.ws.repo, "Demo", self.ws.analyzed, DOCS_BASE)

    def test_database_disagreeing_with_navigation_is_refused(self):
        doc, db = self.ws.docs()
        conn = sqlite3.connect(db)
        conn.execute("UPDATE modules SET source_url = replace(source_url, 'A.lean', 'B.lean') "
                     "WHERE name = 'Demo.A'")
        conn.commit()
        conn.close()
        with self.assertRaisesRegex(facts.FactsError, "does not match page|differs from the database"):
            facts.collect(doc, db, self.ws.repo, "Demo", self.ws.analyzed, DOCS_BASE)

    def test_cli_writes_the_generation_into_the_tree_once(self):
        doc, db = self.ws.docs()
        toolchain = self.ws.root / "lean-toolchain"
        toolchain.write_text(PROVENANCE["toolchain"] + "\n")
        manifest = self.ws.root / "lake-manifest.json"
        manifest.write_text(json.dumps({"packages": [
            {"name": "«doc-gen4»", "url": "https://github.com/kim-em/doc-gen4",
             "rev": "d25c28427ff9693ea711584a7037da22cdeee1c8"}]}))
        argv = ["export", "--doc-dir", str(doc), "--db", str(db), "--repo", str(self.ws.repo),
                "--root", "Demo", "--docs-base", DOCS_BASE, "--toolchain-file", str(toolchain),
                "--docs-manifest", str(manifest)]
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(facts.main(argv), 0)
        manifest_bytes, packed = facts.read_generation(doc / facts.FACTS_DIR)
        with contextlib.redirect_stderr(io.StringIO()) as err:
            self.assertEqual(facts.main(argv), 1)
        self.assertIn("already exists", err.getvalue())
        self.assertEqual(facts.read_generation(doc / facts.FACTS_DIR), (manifest_bytes, packed))
        self.assertEqual(json.loads(manifest_bytes)["provenance"], PROVENANCE)
        self.assertEqual(facts.build_generation(self.ws.collect(), PROVENANCE), (manifest_bytes, packed))

    def test_published_fixture_is_current(self):
        """`docs_facts_fixture/published/` is exactly what this producer emits for the fixture."""
        manifest_bytes, packed = facts.build_generation(self.ws.collect(), PROVENANCE)
        manifest = json.loads(manifest_bytes)
        published = FIXTURE / "published"
        files = {
            "facts.json": gzip.decompress(packed),
            facts.POINTER_KEY: facts.pointer_for(manifest_bytes),
            f"{manifest['generation']}/{facts.MANIFEST_NAME}": manifest_bytes,
            f"{manifest['generation']}/{facts.FACTS_NAME}": packed,
        }
        if REGENERATE:
            if published.exists():
                shutil.rmtree(published)
            for rel, data in files.items():
                (published / rel).parent.mkdir(parents=True, exist_ok=True)
                (published / rel).write_bytes(data)
        on_disk = {str(p.relative_to(published)): p.read_bytes()
                   for p in published.rglob("*") if p.is_file()}
        self.assertEqual(on_disk, files, "run with --regenerate after an intended format change")


class ContractTests(unittest.TestCase):
    """TauCetiProgress's v1 fixture: this producer writes those exact bytes for that payload."""

    def test_consumer_fixture_bytes(self):
        contract = FIXTURE / "contract"
        payload = json.loads((contract / "facts.json").read_bytes())
        self.assertEqual(facts.encode(payload), (contract / "facts.json").read_bytes())
        [gen] = (contract / "v1" / "generations").glob("*/*")
        manifest_bytes = (gen / facts.MANIFEST_NAME).read_bytes()
        packed = (gen / facts.FACTS_NAME).read_bytes()
        manifest = facts.validate(manifest_bytes, packed)
        rebuilt_manifest, rebuilt_packed = facts.build_generation(payload, manifest["provenance"])
        self.assertEqual(rebuilt_packed, packed)
        self.assertEqual(rebuilt_manifest, manifest_bytes)
        self.assertEqual(facts.pointer_for(manifest_bytes), (contract / "v1" / "current.json").read_bytes())

    def test_validation_rejects_what_the_consumer_rejects(self):
        payload = json.loads((FIXTURE / "contract" / "facts.json").read_bytes())
        good = facts.build_generation(payload, PROVENANCE)
        facts.validate(*good)
        broken = [
            (lambda p: p["modules"]["TauCeti/A.lean"]["TauCeti.alpha"].update(start=3), "source range"),
            (lambda p: p["modules"]["TauCeti/A.lean"]["TauCeti.alpha"].update(
                url="https://x.org/docs/TauCeti/B.html#TauCeti.alpha"), "canonical URL"),
            (lambda p: p["modules"]["TauCeti/A.lean"]["TauCeti.alpha"].update(file="TauCeti/B.lean"),
             "source file"),
            (lambda p: p["modules"]["TauCeti/Empty.lean"].update(
                {"TauCeti.alpha": p["modules"]["TauCeti/A.lean"]["TauCeti.alpha"]}), "duplicate"),
        ]
        for mutate, message in broken:
            with self.subTest(message=message):
                bad = json.loads(json.dumps(payload))
                mutate(bad)
                with self.assertRaisesRegex(facts.FactsError, message):
                    facts.validate(*facts.build_generation(bad, PROVENANCE))
        manifest_bytes, packed = good
        with self.assertRaisesRegex(facts.FactsError, "SHA-256"):
            facts.validate(manifest_bytes, packed[:20] + bytes([packed[20] ^ 1]) + packed[21:])
        with self.assertRaisesRegex(facts.FactsError, "provenance"):
            facts.validate(*facts.build_generation(payload, {"toolchain": "x"}))


class MemoryStore:
    """Object storage in a dict, with a log of every operation and optional injected faults."""

    def __init__(self):
        self.objects = {}
        self.log = []
        self.fail_put = set()
        self.public_lag = {}
        self.race = {}

    def get(self, key, public=False):
        self.log.append(("GET", key, public))
        if public and self.public_lag.get(key, 0) > 0:
            self.public_lag[key] -= 1
            return None
        return self.objects.get(key, (None,))[0]

    def put(self, key, data, content_type, cache_control, create_only=False):
        self.log.append(("PUT", key))
        if key in self.fail_put:
            raise facts.FactsError(f"PUT {key}: injected failure")
        if key in self.race:
            self.objects[key] = (self.race.pop(key), "", "")
        if create_only and key in self.objects:
            return False
        self.objects[key] = (data, content_type, cache_control)
        return True

    def puts(self):
        return [entry[1] for entry in self.log if entry[0] == "PUT"]


def generation_dir(root, payload, name="gen"):
    out = pathlib.Path(root) / name
    facts.write_generation(out, *facts.build_generation(payload, PROVENANCE))
    return out


class PublishTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.payload = json.loads((FIXTURE / "contract" / "facts.json").read_bytes())
        self.commit = self.payload["source_commit"]
        self.gen = generation_dir(self.tmp.name, self.payload)
        manifest_bytes, _ = facts.read_generation(self.gen)
        self.manifest = json.loads(manifest_bytes)
        self.pointer = facts.pointer_for(manifest_bytes)
        self.store = MemoryStore()
        self.sleeps = []

    def tearDown(self):
        self.tmp.cleanup()

    def publish(self, gen=None, commit=None):
        return facts.publish(gen or self.gen, commit or self.commit, self.store,
                             sleep=self.sleeps.append, log=lambda *_: None)

    def current(self):
        return self.store.objects.get(facts.POINTER_KEY, (None,))[0]

    def test_pointer_is_written_last_after_public_read_back(self):
        self.assertEqual(self.publish(), self.pointer)
        g = self.manifest["generation"]
        self.assertEqual(self.store.puts(), [f"{g}/facts.json.gz", f"{g}/manifest.json", facts.POINTER_KEY])
        pointer_put = self.store.log.index(("PUT", facts.POINTER_KEY))
        public_reads = [i for i, e in enumerate(self.store.log) if e[0] == "GET" and e[2]]
        self.assertEqual(len(public_reads), 2)
        self.assertTrue(all(i < pointer_put for i in public_reads))
        self.assertEqual(self.current(), self.pointer)
        self.assertEqual(self.store.objects[facts.POINTER_KEY][2], facts.POINTER_CACHE_CONTROL)
        self.assertEqual(self.store.objects[f"{g}/manifest.json"][2], facts.IMMUTABLE_CACHE_CONTROL)

    def test_republishing_the_same_generation_writes_nothing(self):
        self.publish()
        self.store.log.clear()
        self.publish()
        self.assertEqual(self.store.puts(), [])

    def test_interrupted_upload_keeps_the_old_pointer_and_an_ordinary_retry_completes(self):
        older = json.loads(json.dumps(self.payload))
        older["source_commit"] = "b" * 40
        self.publish(generation_dir(self.tmp.name, older, "older"), "b" * 40)
        last_good = self.current()
        for failing in (f"{self.manifest['generation']}/manifest.json", facts.POINTER_KEY):
            with self.subTest(failing=failing):
                self.store.fail_put = {failing}
                with self.assertRaisesRegex(facts.FactsError, "injected"):
                    self.publish()
                self.assertEqual(self.current(), last_good)
        self.store.fail_put = set()
        self.assertEqual(self.publish(), self.pointer)
        self.assertEqual(self.current(), self.pointer)

    def test_failed_validation_uploads_nothing(self):
        bad = pathlib.Path(self.tmp.name) / "bad"
        shutil.copytree(self.gen, bad)
        (bad / facts.FACTS_NAME).write_bytes(b"not gzip")
        with self.assertRaisesRegex(facts.FactsError, "SHA-256"):
            self.publish(bad)
        self.assertEqual(self.store.puts(), [])
        (bad / facts.FACTS_NAME).unlink()
        with self.assertRaisesRegex(facts.FactsError, "unexpected contents"):
            self.publish(bad)

    def test_conflicting_immutable_key_is_an_error(self):
        g = self.manifest["generation"]
        for key in (f"{g}/facts.json.gz", f"{g}/manifest.json"):
            with self.subTest(key=key):
                self.store = MemoryStore()
                self.store.objects[key] = (b"different", "", "")
                with self.assertRaises(facts.ConflictError):
                    self.publish()
                self.assertIsNone(self.current())
                self.assertEqual(self.store.objects[key][0], b"different")

    def test_a_concurrent_writer_is_never_overwritten(self):
        g = self.manifest["generation"]
        self.store.race[f"{g}/manifest.json"] = b"written by another publisher"
        with self.assertRaises(facts.ConflictError):
            self.publish()
        self.assertEqual(self.store.objects[f"{g}/manifest.json"][0], b"written by another publisher")
        self.assertIsNone(self.current())
        same = MemoryStore()
        same.race[f"{g}/facts.json.gz"] = facts.read_generation(self.gen)[1]
        self.store = same
        self.assertEqual(self.publish(), self.pointer)

    def test_cached_docs_publish_their_own_commit(self):
        """A Pages run at a newer checkout publishes the commit the reused tree documents."""
        with self.assertRaisesRegex(facts.FactsError, "not live"):
            self.publish(commit="c" * 40)
        self.assertEqual(self.store.puts(), [])
        self.publish(commit=self.commit)
        self.assertEqual(json.loads(self.current())["source_commit"], self.commit)

    def test_old_generation_remains_readable_after_a_new_publish(self):
        self.publish()
        old_pointer = json.loads(self.current())
        newer = json.loads(json.dumps(self.payload))
        newer["source_commit"] = "d" * 40
        del newer["modules"]["TauCeti/Empty.lean"]
        self.publish(generation_dir(self.tmp.name, newer, "newer"), "d" * 40)
        self.assertEqual(json.loads(self.current())["source_commit"], "d" * 40)
        manifest_bytes = self.store.objects[old_pointer["manifest_path"]][0]
        self.assertEqual(hashlib.sha256(manifest_bytes).hexdigest(), old_pointer["manifest_sha256"])
        manifest = json.loads(manifest_bytes)
        packed = self.store.objects[f"{manifest['generation']}/facts.json.gz"][0]
        self.assertEqual(facts.validate(manifest_bytes, packed)["source_commit"], self.commit)

    def test_public_read_back_waits_for_visibility(self):
        self.store.public_lag[f"{self.manifest['generation']}/facts.json.gz"] = 2
        self.publish()
        self.assertEqual(self.sleeps, [10, 10])
        self.store = MemoryStore()
        self.store.public_lag[f"{self.manifest['generation']}/manifest.json"] = 99
        with self.assertRaisesRegex(facts.FactsError, "public object"):
            self.publish()
        self.assertIsNone(self.current())


class ObjectServer(BaseHTTPRequestHandler):
    """A tiny path-style object store: PUT stores, GET returns or 404s."""

    objects: dict = {}
    requests: list = []
    fail: set = set()

    def log_message(self, *_):
        pass

    def do_PUT(self):
        body = self.rfile.read(int(self.headers.get("Content-Length", 0)))
        self.requests.append(("PUT", self.path, dict(self.headers)))
        if self.path in self.fail:
            self.send_response(500)
        elif self.headers.get("If-None-Match") == "*" and self.path in self.objects:
            self.send_response(412)
        else:
            self.objects[self.path] = body
            self.send_response(200)
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        self.requests.append(("GET", self.path, dict(self.headers)))
        body = self.objects.get(self.path.replace("/public/", "/write/", 1))
        self.send_response(404 if body is None else 200)
        self.send_header("Content-Length", str(len(body or b"")))
        self.end_headers()
        self.wfile.write(body or b"")


@unittest.skipUnless(shutil.which("curl"), "curl is required")
class CurlStoreTests(unittest.TestCase):
    """The real transport against a local server: signing, headers, 404s and a failed PUT."""

    def setUp(self):
        ObjectServer.objects, ObjectServer.requests, ObjectServer.fail = {}, [], set()
        self.server = ThreadingHTTPServer(("127.0.0.1", 0), ObjectServer)
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        base = f"http://127.0.0.1:{self.server.server_address[1]}"
        self.store = facts.CurlStore(f"{base}/write", f"{base}/public", "AKID:secret-value")
        self.tmp = tempfile.TemporaryDirectory()
        payload = json.loads((FIXTURE / "contract" / "facts.json").read_bytes())
        self.gen = generation_dir(self.tmp.name, payload)
        self.commit = payload["source_commit"]

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()
        self.tmp.cleanup()

    def test_publish_over_curl_and_retry_after_a_server_error(self):
        ObjectServer.fail = {"/write/v1/current.json"}
        with self.assertRaisesRegex(facts.FactsError, "HTTP 500"):
            facts.publish(self.gen, self.commit, self.store, log=lambda *_: None)
        self.assertNotIn("/write/v1/current.json", ObjectServer.objects)
        ObjectServer.fail = set()
        pointer = facts.publish(self.gen, self.commit, self.store, log=lambda *_: None)
        self.assertEqual(ObjectServer.objects["/write/v1/current.json"], pointer)
        puts = [r for r in ObjectServer.requests if r[0] == "PUT"]
        for _, path, headers in puts:
            self.assertIn("AWS4-HMAC-SHA256", headers.get("Authorization", ""))
            self.assertNotIn("secret-value", headers.get("Authorization", ""))
        cache = {path: headers.get("Cache-Control") for _, path, headers in puts}
        self.assertEqual(cache["/write/v1/current.json"], facts.POINTER_CACHE_CONTROL)
        public = [r for r in ObjectServer.requests if r[0] == "GET" and r[1].startswith("/public/")]
        self.assertTrue(public)
        self.assertTrue(all("Authorization" not in headers for _, _, headers in public))
        self.assertIsNone(self.store.get("v1/absent.json"))
        immutable = [h for _, path, h in puts if "/generations/" in path]
        self.assertTrue(immutable and all(h.get("If-None-Match") == "*" for h in immutable))
        self.assertFalse(self.store.put("v1/current.json", b"x", "application/json", "no-cache",
                                        create_only=True))


if __name__ == "__main__":
    unittest.main()
