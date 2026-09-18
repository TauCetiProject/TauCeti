#!/usr/bin/env python3
"""Unit tests for the Progress page generator.

Run with: PYTHONPATH=scripts python3 scripts/test_roadmap_progress.py
"""

import datetime as dt
import json
import pathlib
import tempfile
import unittest

import roadmap_progress as rp


README = """# Roadmap: widgets

## What Mathlib already has

## The build, in layers

### Layer 0: the widget (Bourbaki I.2)
text
### Layer 1: gadgets
### Layer 2.5: gizmos — and more
## Worked examples
"""

STATUS = """<!--tauceti-status:v1 {"roadmap":"Widgets","to_sha":"0123456789abcdef0123456789abcdef01234567","ts":"2026-09-01T00:00:00Z"}-->
# Status: Widgets

## Where this roadmap stands

**At a glance.** Layer 0 is done; the rest is untouched.

## The frontier

- **Gadgets.** Build them.
- **Gizmos.** Later.
"""

MARKER = ('<!--tauceti-coverage:v1 {"roadmap":"Widgets","to_sha":"0123456789abcdef0123456789abcdef01234567",'
          '"layers":[{"id":"Layer 0","state":"done"},{"id":"Layer 1","state":"untouched"},'
          '{"id":"Layer 2.5","state":"partial"}]}-->\n')


class Headings(unittest.TestCase):
    def test_headings_drop_parentheticals_and_keep_order(self):
        self.assertEqual(rp.layer_headings(README),
                         ["Layer 0: the widget", "Layer 1: gadgets", "Layer 2.5: gizmos — and more"])

    def test_ids_stop_at_the_first_separator(self):
        self.assertEqual([rp.layer_id(t) for t in rp.layer_headings(README)],
                         ["Layer 0", "Layer 1", "Layer 2.5"])
        self.assertEqual(rp.layer_id("Layer A, line bundles and divisors"), "Layer A")
        self.assertEqual(rp.layer_id("Lane G: grid homology"), "Lane G")
        self.assertEqual(rp.layer_id("L0A — sheaves of modules"), "L0A")
        self.assertEqual(rp.layer_id("S1: the twenty-six sporadic presentations"), "S1")

    def test_short_labels_need_a_separator(self):
        # `K3 surfaces` is a heading about a subject, not a layer label.
        self.assertEqual(rp.layer_headings("### K3 surfaces\n### L0: sheaves\n"), ["L0: sheaves"])

    def test_worded_headings_hide_short_sub_labels(self):
        text = "## Part A — Hermite\n### A1: orthogonality\n### A2: the basis\n## Part B — Chebyshev\n### B1: x\n"
        self.assertEqual(rp.layer_headings(text), ["Part A — Hermite", "Part B — Chebyshev"])

    def test_bold_bullets_are_the_fallback(self):
        text = "## Layers\n- **L0 — the engine** (consumes X). Stuff.\n- **L1 — Montel.** More.\n"
        self.assertEqual(rp.layer_headings(text), ["L0 — the engine", "L1 — Montel"])


class Status(unittest.TestCase):
    def test_parse_status(self):
        st = rp.parse_status(STATUS)
        self.assertEqual(st["to_sha"][:7], "0123456")
        self.assertEqual(st["glance"], "Layer 0 is done; the rest is untouched.")
        self.assertEqual(st["frontier"], ["Gadgets.", "Gizmos."])
        self.assertIsNone(st["coverage"])

    def test_missing_header_is_no_status(self):
        self.assertIsNone(rp.parse_status("# Status\n\nprose only\n"))

    def test_marker_applies_when_it_names_every_layer_once(self):
        st = rp.parse_status(MARKER + STATUS)
        layers = rp.layer_headings(README)
        self.assertEqual(rp.states_from_marker(st["coverage"], layers, st["to_sha"]),
                         ["done", "untouched", "partial"])

    def test_marker_is_ignored_whole_when_it_does_not_fit(self):
        st = rp.parse_status(MARKER + STATUS)
        layers = rp.layer_headings(README)
        self.assertIsNone(rp.states_from_marker(st["coverage"], layers, "another sha"))
        self.assertIsNone(rp.states_from_marker(st["coverage"], layers[:2], st["to_sha"]))
        bad = dict(st["coverage"], layers=st["coverage"]["layers"][:2] + [{"id": "Layer 2.5", "state": "soon"}])
        self.assertIsNone(rp.states_from_marker(bad, layers, st["to_sha"]))

    def test_hand_reading_is_keyed_to_the_snapshot(self):
        layers = rp.layer_headings(README)
        sha = "0123456789abcdef0123456789abcdef01234567"
        self.assertEqual(rp.states_from_transitional({"to_sha": "0123456", "states": "dup"}, layers, sha),
                         ["done", "untouched", "partial"])
        self.assertIsNone(rp.states_from_transitional({"to_sha": "fffffff", "states": "dup"}, layers, sha))
        self.assertIsNone(rp.states_from_transitional({"to_sha": "0123456", "states": "du"}, layers, sha))
        self.assertIsNone(rp.states_from_transitional({"to_sha": "0123456", "states": "dux"}, layers, sha))
        self.assertIsNone(rp.states_from_transitional({"to_sha": "012", "states": "dup"}, layers, sha))


class Tree(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = pathlib.Path(self.tmp.name)
        w = root / rp.AREAS_DIR / "Widgets"
        w.mkdir(parents=True)
        (w / "README.md").write_text(README)
        (w / "STATUS.md").write_text(STATUS)
        (w / "Suggested.lean").write_text("theorem t : True := by sorry\n")
        (w / "references").mkdir()
        (w / "references" / "README.md").write_text("# refs\n### Layer 9: not a roadmap\n")
        sub = w / "Sub"
        sub.mkdir()
        (sub / "README.md").write_text("# Roadmap: sub\n### Layer 0: a\n### Layer 1: b\n")
        (sub / "Suggested.lean").write_text("")
        c = root / rp.COMPLETED_DIR / "Done"
        c.mkdir(parents=True)
        (c / "README.md").write_text("# Done\n### Part A — x\n### Part B — y\n")
        self.root = root

    def tearDown(self):
        self.tmp.cleanup()

    def test_rows_children_and_completed(self):
        rows = rp.read_roadmaps(self.root, {"Sub": {"to_sha": "0123456", "states": "dp"}})
        names = [(r["name"], r["parent"]) for r in rows]
        self.assertEqual(names, [("Widgets", None), ("Sub", "Widgets"), ("Done", None)])
        widgets, sub, done = rows
        self.assertEqual(widgets["title"], "widgets")
        self.assertEqual(widgets["states"], ["unassessed"] * 3)
        self.assertIsNone(widgets["states_source"])
        # The sub-roadmap inherits the umbrella snapshot and its hand reading is keyed to it.
        self.assertTrue(sub["status_inherited"])
        self.assertEqual(sub["states"], ["done", "partial"])
        self.assertEqual(sub["states_source"], "hand-read")
        self.assertTrue(done["completed"])
        self.assertEqual(done["states"], ["done", "done"])
        self.assertEqual(done["states_source"], "completed")


class Activity(unittest.TestCase):
    def test_weekly_bins_and_attribution(self):
        today = dt.date(2026, 9, 17)  # a Thursday; the current week starts Monday 14th
        prs = [
            {"number": 1, "merged_at": "2026-09-15T10:00:00Z", "labels": ["roadmap/PDE"]},
            {"number": 2, "merged_at": "2026-09-08T10:00:00Z", "labels": ["roadmap/PDE", "roadmap/HopfRinow"]},
            {"number": 3, "merged_at": "2026-09-08T10:00:00Z", "labels": ["roadmap/none"]},
            {"number": 4, "merged_at": "2026-01-01T10:00:00Z", "labels": ["roadmap/PDE"]},
        ]
        weeks, allweekly, per = rp.activity(prs, today, weeks=4)
        self.assertEqual(weeks, ["2026-08-24", "2026-08-31", "2026-09-07", "2026-09-14"])
        self.assertEqual(allweekly, [0, 0, 2, 1])
        self.assertEqual(set(per), {"PDE"})
        self.assertEqual(per["PDE"]["weekly"], [0, 0, 0, 1])
        self.assertEqual(per["PDE"]["total"], 2)
        self.assertEqual(per["PDE"]["last30"], 1)
        self.assertEqual(per["PDE"]["last"], "2026-09-15")

    def test_load_prs_accepts_the_statistics_snapshot_and_gh_output(self):
        with tempfile.TemporaryDirectory() as d:
            p = pathlib.Path(d) / "a.json"
            p.write_text(json.dumps({"schema_version": 2, "prs": [
                {"number": 1, "merged_at": "2026-09-01T00:00:00Z", "labels": ["roadmap/PDE"]},
                {"number": 2, "merged_at": None, "labels": []}]}))
            self.assertEqual(rp.load_prs(p), [{"number": 1, "merged_at": "2026-09-01T00:00:00Z", "labels": ["roadmap/PDE"]}])
            p.write_text(json.dumps([{"number": 3, "mergedAt": "2026-09-02T00:00:00Z", "labels": [{"name": "roadmap/PDE"}]}]))
            self.assertEqual(rp.load_prs(p)[0]["labels"], ["roadmap/PDE"])

    def test_build_counts_prs_since_the_snapshot(self):
        rows = [{"name": "Widgets", "parent": None, "completed": False, "layers": ["Layer 0"], "layer_ids": ["Layer 0"],
                 "states": ["done"], "states_source": "hand-read",
                 "status": {"to_sha": "x", "ts": "2026-09-01T00:00:00Z", "glance": "", "frontier": []}}]
        prs = [{"number": 1, "merged_at": "2026-09-02T00:00:00Z", "labels": ["roadmap/Widgets"]},
               {"number": 2, "merged_at": "2026-08-30T00:00:00Z", "labels": ["roadmap/Widgets"]}]
        data = rp.build(rows, prs, {"order": ["T"], "map": {"Widgets": "T"}}, dt.date(2026, 9, 17), "abc1234", "test")
        self.assertEqual(data["rows"][0]["activity"]["since_snapshot"], 1)
        self.assertEqual(data["rows"][0]["topic"], "T")
        self.assertEqual(data["first_merge"], "2026-08-30")


if __name__ == "__main__":
    unittest.main()
