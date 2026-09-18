#!/usr/bin/env python3
"""Unit tests for the Progress page generator.

Run with: PYTHONPATH=scripts python3 scripts/test_roadmap_progress.py
"""

import datetime as dt
import hashlib
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

SHA = "0123456789abcdef0123456789abcdef01234567"

STATUS = f"""<!--tauceti-status:v1 {{"roadmap":"Widgets","to_sha":"{SHA}","ts":"2026-09-01T00:00:00Z"}}-->
# Status: Widgets

## Where this roadmap stands

**At a glance.** Layer 0 is done, and the gadget
half of Layer 1 is
in place. Nothing else has begun.

### Named results

- **The widget theorem** — it holds.

## The frontier

- **Gadgets.** Build the other
  half.
- **Gizmos.** Later.
"""

MARKER = (f'<!--tauceti-coverage:v1 {{"roadmap":"Widgets","to_sha":"{SHA}",'
          '"layers":[{"id":"Layer 0","state":"done"},{"id":"Layer 1","state":"partial"},'
          '{"id":"Layer 2.5","state":"untouched"}]}-->\n')


def report_sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


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
    def test_glance_is_the_whole_wrapped_paragraph(self):
        st = rp.parse_status(STATUS)
        self.assertEqual(st["glance"],
                         "Layer 0 is done, and the gadget half of Layer 1 is in place. Nothing else has begun.")
        one_line = STATUS.replace("Layer 0 is done, and the gadget\nhalf of Layer 1 is\nin place.",
                                  "Layer 0 is done, and the gadget half of Layer 1 is in place.")
        self.assertEqual(rp.parse_status(one_line)["glance"], st["glance"])
        own_line = STATUS.replace("**At a glance.** Layer 0", "**At a glance.**\nLayer 0")
        self.assertEqual(rp.parse_status(own_line)["glance"], st["glance"])

    def test_glance_stops_at_a_block_boundary(self):
        text = STATUS.replace("Nothing else has begun.\n\n### Named", "Nothing else has begun.\n### Named")
        self.assertEqual(rp.parse_status(text)["glance"].endswith("has begun."), True)
        self.assertNotIn("widget theorem", rp.parse_status(text)["glance"])
        self.assertEqual(rp.parse_status(STATUS.replace("**At a glance.**", "**Summary.**"))["glance"], "")

    def test_frontier_keeps_names_and_joined_text(self):
        st = rp.parse_status(STATUS)
        self.assertEqual(st["frontier"], [{"name": "Gadgets.", "text": "Build the other half."},
                                          {"name": "Gizmos.", "text": "Later."}])
        self.assertEqual(st["to_sha"], SHA)
        self.assertEqual(st["report_sha"], report_sha(STATUS))
        self.assertIsNone(st["coverage"])

    def test_missing_or_malformed_header_is_no_status(self):
        self.assertIsNone(rp.parse_status("# Status\n\nprose only\n"))
        self.assertIsNone(rp.parse_status('<!--tauceti-status:v1 {"roadmap":"W","to_sha":7}-->\n'))
        self.assertIsNone(rp.parse_status('<!--tauceti-status:v1 {"roadmap":"W"}-->\n'))

    def test_marker_applies_when_it_names_the_roadmap_and_every_layer_once(self):
        st = rp.parse_status(MARKER + STATUS)
        layers = rp.layer_headings(README)
        self.assertEqual(rp.states_from_marker(st["coverage"], "Widgets", layers, SHA),
                         (["done", "partial", "untouched"], None))

    def test_marker_is_refused_whole_with_a_reason(self):
        st = rp.parse_status(MARKER + STATUS)
        layers = rp.layer_headings(README)
        m = st["coverage"]

        def refused(marker, name="Widgets", lay=layers, sha=SHA):
            states, why = rp.states_from_marker(marker, name, lay, sha)
            self.assertIsNone(states)
            return why

        self.assertIn("names roadmap", refused(m, name="Gadgets"))
        self.assertIn("different library commit", refused(m, sha="another"))
        self.assertIn("differ from the README", refused(m, lay=layers[:2]))
        self.assertIn("illegal state", refused(dict(m, layers=m["layers"][:2] + [{"id": "Layer 2.5", "state": "soon"}])))
        self.assertIn("duplicate", refused(dict(m, layers=m["layers"] + [m["layers"][0]])))
        self.assertIn("objects", refused(dict(m, layers=["Layer 0"])))
        self.assertIn("no layer list", refused(dict(m, layers="Layer 0")))
        self.assertIn("not an object", refused(["Layer 0"]))

    def test_hand_transcription_is_bound_to_the_report_and_the_layer_ids(self):
        layers = rp.layer_headings(README)
        rs = report_sha(STATUS)
        good = {"to_sha": SHA[:7], "report_sha": rs[:12], "layers": {"Layer 0": "d", "Layer 1": "p", "Layer 2.5": "u"}}
        self.assertEqual(rp.states_from_transitional(good, layers, SHA, rs), (["done", "partial", "untouched"], None))
        retired = "transcription-retired"
        self.assertEqual(rp.states_from_transitional(dict(good, to_sha="fffffff"), layers, SHA, rs)[1], retired)
        self.assertEqual(rp.states_from_transitional(dict(good, report_sha="ffffffffffff"), layers, SHA, rs)[1], retired)
        self.assertEqual(rp.states_from_transitional(dict(good, to_sha="012"), layers, SHA, rs)[1], retired)
        # Same number of layers, different ids: never realigned positionally.
        renamed = dict(good, layers={"Layer 0": "d", "Layer 1": "p", "Layer 3": "u"})
        self.assertEqual(rp.states_from_transitional(renamed, layers, SHA, rs)[1], retired)
        self.assertEqual(rp.states_from_transitional(dict(good, layers={"Layer 0": "x", "Layer 1": "p", "Layer 2.5": "u"}), layers, SHA, rs)[1], retired)
        self.assertEqual(rp.states_from_transitional(dict(good, layers="dpu"), layers, SHA, rs)[1], retired)
        self.assertEqual(rp.states_from_transitional(None, layers, SHA, rs)[1], "not-transcribed")


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
        (c / "STATUS.md").write_text(STATUS.replace("Widgets", "Done"))
        self.root = root
        self.rs = report_sha(STATUS)

    def tearDown(self):
        self.tmp.cleanup()

    def test_rows_children_completed_and_reasons(self):
        hand = {
            "Sub": {"to_sha": SHA[:7], "report_sha": self.rs[:12], "layers": {"Layer 0": "d", "Layer 1": "p"}},
            "Done": {"to_sha": SHA[:7], "report_sha": "ffffffffffff", "layers": {"Part A": "d", "Part B": "p"}},
        }
        rows = rp.read_roadmaps(self.root, hand)
        self.assertEqual([(r["id"], r["parent"]) for r in rows],
                         [("TauCetiRoadmap/Widgets", None), ("TauCetiRoadmap/Widgets/Sub", "Widgets"),
                          ("Completed/Done", None)])
        widgets, sub, done = rows
        self.assertEqual(widgets["title"], "widgets")
        self.assertEqual(widgets["states"], ["unassessed"] * 3)
        self.assertEqual(widgets["assessment"]["reason"], "not-transcribed")
        self.assertFalse(widgets["status"]["inherited"])
        # The sub-roadmap inherits the umbrella report, links to it, and its transcription is
        # bound to that report.
        self.assertTrue(sub["status"]["inherited"])
        self.assertEqual(sub["status"]["path"], "TauCetiRoadmap/Widgets/STATUS.md")
        self.assertEqual(sub["readme"], "TauCetiRoadmap/Widgets/Sub/README.md")
        self.assertEqual(sub["states"], ["done", "partial"])
        self.assertEqual(sub["assessment"]["source"], "hand-read")
        # A completed roadmap is a maintainer decision; its layers are not painted done for it.
        self.assertTrue(done["completed"])
        self.assertEqual(done["states"], ["unassessed", "unassessed"])
        self.assertEqual(done["assessment"]["reason"], "transcription-retired")
        self.assertEqual(done["retired"], {"to_sha": SHA[:7], "states": ["done", "partial"]})

    def test_marker_beats_transcription_and_invalid_marker_is_reported(self):
        (self.root / rp.AREAS_DIR / "Widgets" / "STATUS.md").write_text(MARKER + STATUS)
        rows = rp.read_roadmaps(self.root, {})
        self.assertEqual(rows[0]["states"], ["done", "partial", "untouched"])
        self.assertEqual(rows[0]["assessment"]["source"], "marker")
        bad = MARKER.replace('"roadmap":"Widgets"', '"roadmap":"Gadgets"')
        (self.root / rp.AREAS_DIR / "Widgets" / "STATUS.md").write_text(bad + STATUS)
        rows = rp.read_roadmaps(self.root, {})
        self.assertEqual(rows[0]["assessment"]["reason"], "invalid-marker")
        self.assertIn("Gadgets", rows[0]["assessment"]["detail"])
        self.assertEqual(rows[0]["states"], ["unassessed"] * 3)

    def test_no_layers_and_no_report_are_distinct_reasons(self):
        (self.root / rp.AREAS_DIR / "Widgets" / "README.md").write_text("# Roadmap: widgets\n\nprose\n")
        (self.root / rp.AREAS_DIR / "Widgets" / "STATUS.md").unlink()
        rows = rp.read_roadmaps(self.root, {})
        self.assertEqual(rows[0]["assessment"]["reason"], "no-layers")
        self.assertEqual(rows[1]["assessment"]["reason"], "no-report")


class Activity(unittest.TestCase):
    def test_weekly_bins_and_attribution(self):
        today = dt.date(2026, 9, 17)  # a Thursday; the current week starts Monday 14th
        prs = [
            {"number": 1, "merged_at": "2026-09-15T10:00:00Z", "labels": ["roadmap/PDE"]},
            {"number": 2, "merged_at": "2026-09-08T10:00:00Z", "labels": ["roadmap/PDE", "roadmap/HopfRinow"]},
            {"number": 3, "merged_at": "2026-09-08T10:00:00Z", "labels": ["roadmap/none"]},
            {"number": 4, "merged_at": "2026-01-01T10:00:00Z", "labels": ["roadmap/PDE"]},
            {"number": 5, "merged_at": "2026-09-09T10:00:00Z", "labels": ["roadmap/Gone"]},
        ]
        weeks, glob, per = rp.activity(prs, today, weeks=4, known={"PDE"})
        self.assertEqual(weeks, ["2026-08-24", "2026-08-31", "2026-09-07", "2026-09-14"])
        # Every merged PR counts once globally, whatever its labels.
        self.assertEqual(glob["weekly"], [0, 0, 3, 1])
        self.assertEqual(glob["total"], 5)
        self.assertEqual(glob["last30"], 4)
        self.assertEqual(glob["unattributed"], {"no_label": 1, "several_labels": 1, "unknown_area": 1})
        self.assertEqual(set(per), {"PDE"})
        self.assertEqual(per["PDE"]["weekly"], [0, 0, 0, 1])
        self.assertEqual(per["PDE"]["total"], 2)
        self.assertEqual(per["PDE"]["last30"], 1)
        self.assertEqual(per["PDE"]["last"], "2026-09-15")

    def test_load_prs_accepts_the_statistics_snapshot_and_gh_output_and_deduplicates(self):
        with tempfile.TemporaryDirectory() as d:
            p = pathlib.Path(d) / "a.json"
            p.write_text(json.dumps({"schema_version": 2, "prs": [
                {"number": 1, "merged_at": "2026-09-01T00:00:00Z", "labels": ["roadmap/PDE"]},
                {"number": 1, "merged_at": "2026-09-01T00:00:00Z", "labels": ["roadmap/PDE"]},
                {"number": 2, "merged_at": None, "labels": []}]}))
            self.assertEqual(rp.load_prs(p), [{"number": 1, "merged_at": "2026-09-01T00:00:00Z", "labels": ["roadmap/PDE"]}])
            p.write_text(json.dumps([{"number": 3, "mergedAt": "2026-09-02T00:00:00Z", "labels": [{"name": "roadmap/PDE"}]}]))
            self.assertEqual(rp.load_prs(p)[0]["labels"], ["roadmap/PDE"])

    def test_build_counts_prs_since_the_report_and_stamps_the_generation_time(self):
        rows = [{"id": "TauCetiRoadmap/Widgets", "name": "Widgets", "parent": None, "completed": False,
                 "layers": ["Layer 0"], "layer_ids": ["Layer 0"], "states": ["done"],
                 "assessment": {"source": "hand-read", "reason": "ok", "detail": None, "notes": {}},
                 "status": {"to_sha": "x", "ts": "2026-09-01T00:00:00Z", "glance": "", "frontier": []}}]
        prs = [{"number": 1, "merged_at": "2026-09-02T00:00:00Z", "labels": ["roadmap/Widgets"]},
               {"number": 2, "merged_at": "2026-08-30T00:00:00Z", "labels": ["roadmap/Widgets"]},
               {"number": 3, "merged_at": "2026-09-03T00:00:00Z", "labels": []}]
        now = dt.datetime(2026, 9, 17, 12, 30, tzinfo=dt.timezone.utc)
        data = rp.build(rows, prs, {"order": ["T"], "map": {"Widgets": "T"}}, now, "abc1234", "test")
        self.assertEqual(data["rows"][0]["activity"]["since_report"], 1)
        self.assertEqual(data["rows"][0]["topic"], "T")
        self.assertEqual(data["generated_at"], "2026-09-17T12:30:00Z")
        self.assertEqual(data["global"]["first_merge"], "2026-08-30")
        self.assertEqual(data["global"]["total"], 3)
        self.assertEqual(data["global"]["unattributed"]["no_label"], 1)

    def test_build_with_no_rows_or_prs_is_well_formed(self):
        data = rp.build([], [], {}, dt.datetime(2026, 9, 17, tzinfo=dt.timezone.utc), None, "test")
        self.assertIsNone(data["global"]["first_merge"])
        self.assertEqual(data["global"]["total"], 0)


if __name__ == "__main__":
    unittest.main()
