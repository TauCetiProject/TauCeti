#!/usr/bin/env python3
"""Tests for scripts/docs_facts.py, the immutable documentation facts producer.

Run with: python3 scripts/test_docs_facts.py
Regenerate the published fixture with: python3 scripts/test_docs_facts.py --regenerate

`docs_facts_fixture/doc/` and `api-docs.sql` are real doc-gen4 output (the pinned revision in
docbuild/lakefile.toml) for the three small modules in `sources.json`; see the fixture README. The
tests rebuild that source history in a temporary git repository with fixed dates, so its commits
are reproducible, and substitute the commit into the recorded source links.
"""

import contextlib
import gzip
import io
import json
import os
import pathlib
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import docs_facts as facts  # noqa: E402

FIXTURE = pathlib.Path(__file__).resolve().parent / "docs_facts_fixture"
RECORDED_COMMIT = "937b7d87c3dec2f992a6791337a04a2cafd0d243"
DOCS_BASE = "https://taucetiproject.org/docs"
PROVENANCE = {"toolchain": "leanprover/lean4:v4.36.0-rc1",
              "doc_gen": "https://github.com/kim-em/doc-gen4@d25c28427ff9693ea711584a7037da22cdeee1c8"}
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
        facts.validate(facts.pack({**data, "provenance": PROVENANCE}))

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

    def test_cli_writes_the_file_into_the_tree_once(self):
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
        packed = (doc / facts.FACTS_NAME).read_bytes()
        self.assertEqual((doc / facts.FACTS_NAME).stat().st_mode & 0o777, 0o644)
        with contextlib.redirect_stderr(io.StringIO()) as err:
            self.assertEqual(facts.main(argv), 1)
        self.assertIn("already exists", err.getvalue())
        self.assertEqual((doc / facts.FACTS_NAME).read_bytes(), packed)
        self.assertEqual(sorted(p.name for p in doc.iterdir() if p.name.startswith(".")), [])
        data = facts.validate(packed)
        self.assertEqual(data["provenance"], PROVENANCE)
        self.assertEqual(packed, facts.pack({**self.ws.collect(), "provenance": PROVENANCE}))

    def test_published_fixture_is_current(self):
        """`docs_facts_fixture/facts.json` is exactly what this exporter emits for the fixture."""
        raw = gzip.decompress(facts.pack({**self.ws.collect(), "provenance": PROVENANCE}))
        expected = FIXTURE / "facts.json"
        if REGENERATE:
            expected.write_bytes(raw)
        self.assertEqual(expected.read_bytes(), raw, "run with --regenerate after an intended format change")


class ValidationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.payload = {**Workspace(pathlib.Path(self.tmp.name)).collect(), "provenance": PROVENANCE}

    def tearDown(self):
        self.tmp.cleanup()

    def test_validation_rejects_malformed_facts(self):
        facts.validate(facts.pack(self.payload))
        alpha = lambda p: p["modules"]["Demo/A.lean"]["Demo.alpha"]
        broken = [
            (lambda p: alpha(p).update(start=99), "source range"),
            (lambda p: alpha(p).update(url=f"{DOCS_BASE}/Demo/Empty.html#Demo.alpha"), "canonical URL"),
            (lambda p: alpha(p).update(file="Demo/Empty.lean"), "source file"),
            (lambda p: p["modules"]["Demo/Empty.lean"].update({"Demo.alpha": alpha(p)}), "duplicate"),
            (lambda p: p.update(provenance={"toolchain": "x"}), "provenance"),
            (lambda p: p.update(source_commit="HEAD"), "source commit"),
        ]
        for mutate, message in broken:
            with self.subTest(message=message):
                bad = json.loads(json.dumps(self.payload))
                mutate(bad)
                with self.assertRaisesRegex(facts.FactsError, message):
                    facts.validate(facts.pack(bad))
        with self.assertRaisesRegex(facts.FactsError, "gzip"):
            facts.validate(facts.pack(self.payload)[:-8])


if __name__ == "__main__":
    unittest.main()
