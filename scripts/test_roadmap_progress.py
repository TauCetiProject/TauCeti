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

UTC = dt.timezone.utc


def entry(**over):
    e = {"to_sha": SHA[:7], "report_sha": rp.sha256(STATUS)[:12], "readme_sha": rp.sha256(README)[:12],
         "layers": {"Layer 0": "d", "Layer 1": "p", "Layer 2.5": "u"}}
    e.update(over)
    return e


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

    def test_headings_carry_their_line_numbers(self):
        self.assertEqual(rp.layer_headings_with_lines(README),
                         [("Layer 0: the widget", 7), ("Layer 1: gadgets", 9), ("Layer 2.5: gizmos — and more", 10)])
        bullets = "## Layers\n\n- **L0 — the engine** (x). Stuff.\n- **L1 — Montel.** More.\n"
        self.assertEqual([l for _, l in rp.layer_headings_with_lines(bullets)], [3, 4])

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
        self.assertTrue(rp.parse_status(text)["glance"].endswith("has begun."))
        self.assertNotIn("widget theorem", rp.parse_status(text)["glance"])
        self.assertEqual(rp.parse_status(STATUS.replace("**At a glance.**", "**Summary.**"))["glance"], "")

    def test_frontier_keeps_names_and_joined_text(self):
        st = rp.parse_status(STATUS)
        self.assertEqual(st["frontier"], [{"name": "Gadgets.", "text": "Build the other half."},
                                          {"name": "Gizmos.", "text": "Later."}])
        self.assertEqual(st["to_sha"], SHA)
        self.assertEqual(st["ts"], "2026-09-01T00:00:00Z")
        self.assertEqual(st["report_sha"], rp.sha256(STATUS))
        self.assertIsNone(st["coverage"])

    def test_missing_or_malformed_header_is_no_status_and_bad_dates_are_dropped(self):
        self.assertIsNone(rp.parse_status("# Status\n\nprose only\n"))
        self.assertIsNone(rp.parse_status('<!--tauceti-status:v1 {"roadmap":"W","to_sha":7}-->\n'))
        self.assertIsNone(rp.parse_status('<!--tauceti-status:v1 {"roadmap":"W"}-->\n'))
        self.assertIsNone(rp.parse_status('<!--tauceti-status:v1 {"roadmap":"W" "to_sha":"x"}-->\n'))
        bad_ts = rp.parse_status(STATUS.replace("2026-09-01T00:00:00Z", "yesterday"))
        self.assertIsNone(bad_ts["ts"])
        offset = rp.parse_status(STATUS.replace("2026-09-01T00:00:00Z", "2026-09-07T11:04:50+10:00"))
        self.assertEqual(offset["ts"], "2026-09-07T01:04:50Z")

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

    def test_remaining_notes_come_from_marker_entries_or_a_transcription_map(self):
        ids = ["Layer 0", "Layer 1"]
        entries = [{"id": "Layer 0", "state": "partial", "remaining": " the converse "}, {"id": "Layer 1", "state": "done", "remaining": 7},
                   {"id": "Layer 9", "state": "done", "remaining": "not a layer"}, "junk"]
        self.assertEqual(rp.remaining_notes(entries, ids), {"Layer 0": "the converse"})
        self.assertEqual(rp.remaining_notes({"Layer 1": "duality", "Layer 5": "x", "Layer 0": ""}, ids), {"Layer 1": "duality"})
        self.assertEqual(rp.remaining_notes("duality", ids), {})

    def test_present_but_broken_marker_is_not_the_same_as_none(self):
        broken = '<!--tauceti-coverage:v1 {"roadmap":"Widgets", "layers": [}-->\n' + STATUS
        st = rp.parse_status(broken)
        self.assertEqual(st["coverage"], rp.MALFORMED)
        self.assertEqual(rp.states_from_marker(st["coverage"], "Widgets", rp.layer_headings(README), SHA)[1],
                         "marker JSON does not parse")

    def test_hand_transcription_is_bound_to_report_readme_and_layer_ids(self):
        layers = rp.layer_headings(README)
        rs, ms = rp.sha256(STATUS), rp.sha256(README)

        def result(e):
            return rp.states_from_transitional(e, layers, SHA, rs, ms)

        self.assertEqual(result(entry()), (["done", "partial", "untouched"], None))
        self.assertEqual(result(entry(to_sha="fffffff"))[1], "transcription-retired")
        self.assertEqual(result(entry(report_sha="ffffffffffff"))[1], "transcription-retired")
        self.assertEqual(result(entry(to_sha="012"))[1], "transcription-retired")
        # Same ids, changed requirements: the README hash retires it with its own reason.
        self.assertEqual(result(entry(readme_sha="ffffffffffff"))[1], "specification-changed")
        self.assertEqual(result(entry(readme_sha=None))[1], "specification-changed")
        # Same number of layers, different ids: never realigned positionally.
        self.assertEqual(result(entry(layers={"Layer 0": "d", "Layer 1": "p", "Layer 3": "u"}))[1], "specification-changed")
        self.assertEqual(result(entry(layers={"Layer 0": "x", "Layer 1": "p", "Layer 2.5": "u"}))[1], "specification-changed")
        self.assertEqual(result(entry(layers="dpu"))[1], "specification-changed")
        self.assertEqual(result(entry(layers={"Layer 0": ["d"], "Layer 1": "p", "Layer 2.5": "u"}))[1], "specification-changed")
        self.assertEqual(result(None)[1], "not-transcribed")

    def test_edited_requirements_under_unchanged_headings_retire_the_transcription(self):
        layers = rp.layer_headings(README)
        edited = README.replace("text\n", "completely different requirements\n")
        self.assertEqual(rp.layer_headings(edited), layers)
        self.assertEqual(rp.states_from_transitional(entry(), layers, SHA, rp.sha256(STATUS), rp.sha256(edited))[1],
                         "specification-changed")


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
        for sub in ("Sub", "Twin"):
            (w / sub).mkdir()
            (w / sub / "README.md").write_text("# Roadmap: sub\n### Layer 0: a\n### Layer 1: b\n")
            (w / sub / "Suggested.lean").write_text("")
        # A second umbrella with a child of the same display name as Widgets' child.
        g = root / rp.AREAS_DIR / "Gadgets"
        (g / "Twin").mkdir(parents=True)
        (g / "README.md").write_text("# Roadmap: gadgets\n### Layer 0: x\n")
        (g / "STATUS.md").write_text(STATUS.replace("Widgets", "Gadgets"))
        (g / "Twin" / "README.md").write_text("# Roadmap: other twin\n### Layer 0: y\n")
        (g / "Twin" / "Suggested.lean").write_text("")
        c = root / rp.COMPLETED_DIR / "Done"
        c.mkdir(parents=True)
        (c / "README.md").write_text("# Done\n### Part A — x\n### Part B — y\n")
        (c / "STATUS.md").write_text(STATUS.replace("Widgets", "Done"))
        self.root = root
        self.sub_readme = rp.sha256("# Roadmap: sub\n### Layer 0: a\n### Layer 1: b\n")[:12]

    def tearDown(self):
        self.tmp.cleanup()

    def test_rows_children_completed_and_reasons(self):
        hand = {
            "TauCetiRoadmap/Widgets/Sub": {"to_sha": SHA[:7], "report_sha": rp.sha256(STATUS)[:12],
                                           "readme_sha": self.sub_readme, "layers": {"Layer 0": "d", "Layer 1": "p"}},
            "Completed/Done": {"to_sha": SHA[:7], "report_sha": "ffffffffffff", "readme_sha": "ffffffffffff",
                               "layers": {"Part A": "d", "Part B": "p"}},
        }
        rows = rp.read_roadmaps(self.root, hand)
        self.assertEqual([r["id"] for r in rows],
                         ["TauCetiRoadmap/Gadgets", "TauCetiRoadmap/Gadgets/Twin", "TauCetiRoadmap/Widgets",
                          "TauCetiRoadmap/Widgets/Sub", "TauCetiRoadmap/Widgets/Twin", "Completed/Done"])
        gadgets, gtwin, widgets, sub, wtwin, done = rows
        self.assertEqual(widgets["title"], "widgets")
        self.assertEqual(widgets["states"], ["unassessed"] * 3)
        self.assertEqual(widgets["assessment"]["reason"], "not-transcribed")
        self.assertFalse(widgets["status"]["inherited"])
        self.assertEqual(len(widgets["readme_sha"]), 64)
        # The sub-roadmap inherits the umbrella report, links to it, and its transcription is
        # bound to that report and keyed by its full path.
        self.assertTrue(sub["status"]["inherited"])
        self.assertEqual(sub["parent_id"], "TauCetiRoadmap/Widgets")
        self.assertEqual(sub["status"]["path"], "TauCetiRoadmap/Widgets/STATUS.md")
        self.assertEqual(sub["readme"], "TauCetiRoadmap/Widgets/Sub/README.md")
        self.assertEqual(sub["states"], ["done", "partial"])
        self.assertEqual(sub["assessment"]["source"], "hand-read")
        # Two children called Twin under different parents stay apart.
        self.assertNotEqual(gtwin["id"], wtwin["id"])
        self.assertEqual(gtwin["parent_id"], "TauCetiRoadmap/Gadgets")
        self.assertEqual(wtwin["assessment"]["reason"], "not-transcribed")
        # A completed roadmap is a maintainer decision; its layers are not painted done for it.
        self.assertTrue(done["completed"])
        self.assertEqual(done["states"], ["unassessed", "unassessed"])
        self.assertEqual(done["assessment"]["reason"], "transcription-retired")
        self.assertEqual(done["retired"], {"to_sha": SHA[:7], "states": ["done", "partial"]})

    def test_lines_links_and_remaining_reach_the_row(self):
        hand = {"TauCetiRoadmap/Widgets": dict(entry(), remaining={"Layer 1": "the other half", "Layer 7": "x"})}
        links = {"TauCetiRoadmap/Widgets": [{"label": "route map", "url": "https://example.org/map"},
                                            {"label": "bad", "url": "javascript:alert(1)"}, "junk"]}
        widgets = rp.read_roadmaps(self.root, hand, links)[2]
        self.assertEqual(widgets["layer_lines"], [7, 9, 10])
        self.assertEqual(widgets["links"], [{"label": "route map", "url": "https://example.org/map"}])
        self.assertEqual(widgets["assessment"]["remaining"], {"Layer 1": "the other half"})
        marker = MARKER.replace('"state":"partial"', '"state":"partial","remaining":"the other half"')
        (self.root / rp.AREAS_DIR / "Widgets" / "STATUS.md").write_text(marker + STATUS)
        widgets = rp.read_roadmaps(self.root, {}, links)[2]
        self.assertEqual(widgets["assessment"]["source"], "marker")
        self.assertEqual(widgets["assessment"]["remaining"], {"Layer 1": "the other half"})

    def test_a_malformed_old_transcription_is_dropped_not_fatal(self):
        hand = {"Completed/Done": {"to_sha": SHA[:7], "report_sha": "ffffffffffff", "readme_sha": "ffffffffffff",
                                   "layers": {"Part A": ["d"], "Part B": "p"}}}
        done = rp.read_roadmaps(self.root, hand)[-1]
        self.assertEqual(done["assessment"]["reason"], "transcription-retired")
        self.assertIsNone(done["retired"])
        self.assertIn("malformed", done["assessment"]["detail"])

    def test_marker_beats_transcription_and_invalid_marker_is_reported(self):
        status = self.root / rp.AREAS_DIR / "Widgets" / "STATUS.md"
        status.write_text(MARKER + STATUS)
        widgets = rp.read_roadmaps(self.root, {})[2]
        self.assertEqual(widgets["states"], ["done", "partial", "untouched"])
        self.assertEqual(widgets["assessment"]["source"], "marker")
        status.write_text(MARKER.replace('"roadmap":"Widgets"', '"roadmap":"Gadgets"') + STATUS)
        widgets = rp.read_roadmaps(self.root, {})[2]
        self.assertEqual(widgets["assessment"]["reason"], "invalid-marker")
        self.assertIn("Gadgets", widgets["assessment"]["detail"])
        self.assertEqual(widgets["states"], ["unassessed"] * 3)
        status.write_text('<!--tauceti-coverage:v1 {"roadmap":"Widgets",}-->\n' + STATUS)
        widgets = rp.read_roadmaps(self.root, {})[2]
        self.assertEqual(widgets["assessment"]["reason"], "invalid-marker")
        self.assertIn("does not parse", widgets["assessment"]["detail"])

    def test_no_layers_and_no_report_are_distinct_reasons(self):
        (self.root / rp.AREAS_DIR / "Widgets" / "README.md").write_text("# Roadmap: widgets\n\nprose\n")
        (self.root / rp.AREAS_DIR / "Widgets" / "STATUS.md").unlink()
        rows = rp.read_roadmaps(self.root, {})
        self.assertEqual(rows[2]["assessment"]["reason"], "no-layers")
        self.assertEqual(rows[3]["assessment"]["reason"], "no-report")


class Activity(unittest.TestCase):
    def test_weekly_bins_attribution_and_cutoff(self):
        cutoff = dt.datetime(2026, 9, 17, 12, 0, tzinfo=UTC)  # a Thursday; the week starts Monday 14th
        prs = [
            {"number": 1, "merged_at": "2026-09-15T10:00:00Z", "labels": ["roadmap/PDE"]},
            {"number": 2, "merged_at": "2026-09-08T10:00:00Z", "labels": ["roadmap/PDE", "roadmap/HopfRinow"]},
            {"number": 3, "merged_at": "2026-09-08T10:00:00Z", "labels": ["roadmap/none"]},
            {"number": 4, "merged_at": "2026-01-01T10:00:00Z", "labels": ["roadmap/PDE"]},
            {"number": 5, "merged_at": "2026-09-09T10:00:00Z", "labels": ["roadmap/Gone"]},
            {"number": 6, "merged_at": "2026-09-17T12:00:01Z", "labels": ["roadmap/PDE"]},  # after the cutoff
            {"number": 7, "merged_at": "2026-08-18T12:00:00Z", "labels": ["roadmap/PDE"]},  # exactly 30 days before
            {"number": 8, "merged_at": "2026-08-18T12:00:01Z", "labels": ["roadmap/PDE"]},  # just inside
            {"number": 9, "merged_at": None, "open": True, "labels": ["roadmap/PDE"]},
            {"number": 10, "merged_at": None, "open": True, "labels": ["roadmap/PDE", "roadmap/Gone"]},
            {"number": 11, "merged_at": None, "open": True, "labels": []},
        ]
        weeks, glob, per = rp.activity(prs, cutoff, weeks=4, known={"PDE"})
        self.assertEqual(glob["open"], 3)
        self.assertEqual(per["PDE"]["open"], 1)
        self.assertEqual(weeks, ["2026-08-24", "2026-08-31", "2026-09-07", "2026-09-14"])
        # Every merged PR up to the cutoff counts once globally, whatever its labels.
        self.assertEqual(glob["total"], 7)
        self.assertEqual(glob["weekly"], [0, 0, 3, 1])
        self.assertEqual(glob["recent"], 5)
        self.assertEqual(glob["unattributed"], {"no_label": 1, "several_labels": 1, "unknown_area": 1})
        self.assertEqual(set(per), {"PDE"})
        self.assertEqual(per["PDE"]["weekly"], [0, 0, 0, 1])
        self.assertEqual(per["PDE"]["total"], 4)
        self.assertEqual(per["PDE"]["recent"], 2)
        self.assertEqual(per["PDE"]["last"], "2026-09-15T10:00:00Z")

    def test_load_prs_accepts_every_shape_deduplicates_and_keeps_the_collection_time(self):
        with tempfile.TemporaryDirectory() as d:
            p = pathlib.Path(d) / "a.json"
            p.write_text(json.dumps({"schema_version": 2, "fetched_at": "2026-09-17T03:00:00Z", "prs": [
                {"number": 1, "merged_at": "2026-09-01T00:00:00Z", "labels": ["roadmap/PDE"]},
                {"number": 1, "merged_at": "2026-09-01T00:00:00Z", "labels": ["roadmap/PDE"]},
                {"number": 2, "merged_at": None, "closed_at": "2026-09-02T00:00:00Z", "state": "CLOSED", "labels": []},
                {"number": 5, "merged_at": None, "closed_at": None, "state": "OPEN", "labels": ["roadmap/PDE"]},
                {"number": 9, "merged_at": "not a date", "state": "CLOSED", "labels": []}]}))
            prs, collected = rp.load_prs(p)
            self.assertEqual(prs, [{"number": 1, "merged_at": "2026-09-01T00:00:00Z", "open": False, "labels": ["roadmap/PDE"]},
                                   {"number": 5, "merged_at": None, "open": True, "labels": ["roadmap/PDE"]}])
            self.assertEqual(collected, "2026-09-17T03:00:00Z")
            p.write_text(json.dumps([{"number": 3, "mergedAt": "2026-09-02T00:00:00Z", "labels": [{"name": "roadmap/PDE"}]},
                                     {"number": 4, "mergedAt": None, "state": "OPEN", "labels": []}]))
            prs, collected = rp.load_prs(p)
            self.assertEqual([(q["number"], q["open"]) for q in prs], [(3, False), (4, True)])
            self.assertIsNone(collected)

    def test_build_stamps_three_times_and_counts_prs_since_the_report(self):
        rows = [{"id": "TauCetiRoadmap/Widgets", "name": "Widgets", "parent": None, "completed": False,
                 "layers": ["Layer 0"], "layer_ids": ["Layer 0"], "states": ["done"],
                 "assessment": {"source": "hand-read", "reason": "ok", "detail": None, "notes": {}},
                 "status": {"to_sha": "x", "ts": "2026-09-01T00:00:00Z", "glance": "", "frontier": []}}]
        prs = [{"number": 1, "merged_at": "2026-09-02T00:00:00Z", "labels": ["roadmap/Widgets"]},
               {"number": 2, "merged_at": "2026-08-30T00:00:00Z", "labels": ["roadmap/Widgets"]},
               {"number": 3, "merged_at": "2026-09-03T00:00:00Z", "labels": []},
               {"number": 4, "merged_at": "2026-09-20T00:00:00Z", "labels": ["roadmap/Widgets"]},
               {"number": 5, "merged_at": None, "open": True, "labels": ["roadmap/Widgets"]}]
        exported = dt.datetime(2026, 9, 18, 12, 30, tzinfo=UTC)
        cutoff = dt.datetime(2026, 9, 17, 3, 0, tzinfo=UTC)
        data = rp.build(rows, prs, {"order": ["T"], "map": {"Widgets": "T"}}, exported, cutoff,
                        "2026-09-17T03:00:00Z", "abc1234", "test")
        self.assertEqual(data["exported_at"], "2026-09-18T12:30:00Z")
        self.assertEqual(data["collected_at"], "2026-09-17T03:00:00Z")
        self.assertEqual(data["cutoff"], "2026-09-17T03:00:00Z")
        self.assertEqual(data["rows"][0]["activity"]["since_report"], 1)  # #4 is after the cutoff
        self.assertEqual(data["rows"][0]["activity"]["total"], 2)
        self.assertEqual(data["rows"][0]["activity"]["open"], 1)
        self.assertEqual(data["global"]["open"], 1)
        self.assertEqual(data["rows"][0]["topic"], "T")
        self.assertEqual(data["global"]["first_merge"], "2026-08-30T00:00:00Z")
        self.assertEqual(data["global"]["total"], 3)
        self.assertEqual(data["global"]["unattributed"]["no_label"], 1)

    def test_build_with_no_rows_or_prs_is_well_formed_and_unknown_collection_stays_unknown(self):
        now = dt.datetime(2026, 9, 17, tzinfo=UTC)
        data = rp.build([], [], {}, now, now, None, None, "test")
        self.assertIsNone(data["global"]["first_merge"])
        self.assertIsNone(data["collected_at"])
        self.assertEqual(data["global"]["total"], 0)


if __name__ == "__main__":
    unittest.main()
