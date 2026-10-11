#!/usr/bin/env python3
"""Historical completion and forecast regressions, including real throwaway git histories."""

import datetime as dt
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest
import xml.etree.ElementTree as ET

import roadmap_completion as completion
import roadmap_progress as progress


README = "# Widgets\n\n### Layer 1: foundations\n\n### Lane B: theorem\n"
SHA = "a" * 40


def report(name="Widgets", states=("done", "partial"), readme=README):
    coverage = dict(roadmap=name, to_sha=SHA, readme_sha=progress.sha256(readme),
                    layers=[dict(id=label, state=state)
                            for label, state in zip(["Layer 1", "Lane B"], states)])
    return (f'<!--tauceti-status:v1 {json.dumps(dict(roadmap=name, to_sha=SHA))}-->\n'
            f'<!--tauceti-coverage:v1 {json.dumps(coverage)}-->\n')


class Snapshots(unittest.TestCase):
    def tree(self):
        return {"TauCetiRoadmap/Widgets/README.md": README,
                "TauCetiRoadmap/Widgets/Suggested.lean": "example : True := by trivial\n",
                "TauCetiRoadmap/Widgets/STATUS.md": report(),
                "Completed/Archive/README.md": README,
                "Completed/Archive/Suggested.lean": "example : True := by trivial\n"}

    def test_completed_size_stays_in_total_and_reports_are_excluded(self):
        tree = self.tree()
        tree["TauCetiRoadmap/Widgets/PROGRESS.md"] = "Generated summary.\n" * 100
        size = len(README.splitlines()) + 1
        row = completion.summarize(completion.snapshot(tree))
        self.assertEqual(row["spec_lines"], 2 * size)
        self.assertEqual(row["completed_spec_lines"], size)
        self.assertEqual((row["layers"], row["completed_layers"]), (4, 3))
        self.assertEqual(row["unassessed_layers"], 0)

    def test_active_and_archived_roadmaps_with_same_name_both_count(self):
        tree = self.tree()
        tree["Completed/Widgets/README.md"] = tree.pop("Completed/Archive/README.md")
        row = completion.summarize(completion.snapshot(tree))
        self.assertEqual(row["roadmaps"], 2)
        self.assertEqual(row["layers"], 4)
        self.assertEqual(row["completed_roadmaps"], 1)

    def test_missing_assessment_is_visible_and_earns_zero_credit(self):
        tree = self.tree()
        del tree["TauCetiRoadmap/Widgets/STATUS.md"]
        row = completion.summarize(completion.snapshot(tree))
        self.assertEqual(row["unassessed_layers"], 2)
        self.assertEqual(row["completed_layers"], 2)  # only human-archived layers

    def test_relayered_readme_cannot_reuse_old_verdicts(self):
        tree = self.tree()
        tree["TauCetiRoadmap/Widgets/README.md"] = README.replace("Lane B", "Lane C")
        row = completion.summarize(completion.snapshot(tree))
        self.assertEqual(row["unassessed_layers"], 2)
        self.assertEqual(row["stale_assessments"], 0)

    def test_edited_readme_preserves_same_ids_with_stale_flag(self):
        tree = self.tree()
        tree["TauCetiRoadmap/Widgets/README.md"] += "New requirements.\n"
        row = completion.summarize(completion.snapshot(tree))
        self.assertEqual(row["completed_layers"], 3)
        self.assertEqual(row["stale_assessments"], 1)

    def test_invalid_marker_cannot_claim_completion(self):
        tree = self.tree()
        tree["TauCetiRoadmap/Widgets/STATUS.md"] = report().replace('"state": "done"', '"state": "invalid"')
        row = completion.summarize(completion.snapshot(tree))
        self.assertEqual(row["unassessed_layers"], 2)

    def test_umbrella_uses_child_marker_and_ignores_reference_readmes(self):
        tree = self.tree()
        tree["TauCetiRoadmap/Widgets/STATUS.md"] += report("Widgets/Child", ("done", "done")).splitlines()[1]
        tree["TauCetiRoadmap/Widgets/Child/README.md"] = README
        tree["TauCetiRoadmap/Widgets/Child/Suggested.lean"] = "\n"
        tree["TauCetiRoadmap/Widgets/references/README.md"] = "### Lane Z: reference\n"
        row = completion.summarize(completion.snapshot(tree))
        self.assertEqual(row["roadmaps"], 2)
        self.assertEqual((row["layers"], row["completed_layers"]), (6, 5))


class Forecasts(unittest.TestCase):
    def data(self):
        rows = [dict(date="2026-07-01", spec_lines=100, completed_spec_lines=0, layers=10,
                     completed_layers=0, completion_credit=dict(spec_lines=0, layers=0)),
                dict(date="2026-07-08", spec_lines=120, completed_spec_lines=40, layers=12,
                     completed_layers=4, completion_credit=dict(spec_lines=40, layers=4))]
        code = [("2026-06-30", 0), ("2026-07-01", 100), ("2026-07-08", 800)]
        return rows, code

    def test_work_calibration_and_both_authoring_scenarios(self):
        rows, code = self.data()
        result = completion.forecasts(rows, [], code)
        self.assertEqual(result["library_growth_lines_per_day"], 100)
        forecast = result["estimates"]["spec_lines"]
        self.assertEqual(forecast["completion_units_per_library_line"], 40 / 800)
        self.assertAlmostEqual(forecast["stop_authoring"]["days"], 16)
        self.assertAlmostEqual(forecast["continue_authoring"]["days"], 80 / (5 - 20 / 7))

    def test_authoring_faster_than_completion_has_no_finite_exhaustion(self):
        rows, code = self.data()
        rows[-1]["spec_lines"] = 200
        forecast = completion.forecasts(rows, [], code)["estimates"]["spec_lines"]
        self.assertEqual(forecast["continue_authoring"], dict(days=None, state="not-catching-up"))
        self.assertGreater(forecast["stop_authoring"]["days"], 0)

    def test_zero_or_negative_growth_and_no_completions_are_unknown(self):
        rows, code = self.data()
        for growth in (0, -10):
            code[-1] = ("2026-07-08", 100 + growth)
            result = completion.forecasts(rows, [], code)
            self.assertIsNone(result["estimates"]["layers"]["stop_authoring"]["days"])
        rows[-1]["completion_credit"]["layers"] = 0
        self.assertEqual(completion.forecasts(rows, [], self.data()[1])["estimates"]["layers"]
                         ["stop_authoring"]["state"], "insufficient-history")

    def test_an_incomplete_seven_day_window_does_not_invent_recent_pace(self):
        rows, code = self.data()
        rows[0]["date"] = "2026-07-05"
        forecast = completion.forecasts(rows, [], code)["estimates"]["layers"]
        self.assertIsNone(forecast["stop_authoring"]["days"])

    def test_completed_events_export_then_current_library_loc(self):
        rows, code = self.data()
        events = [dict(date="2026-07-02", basis="layers", units=1)]
        completion.forecasts(rows, events, code)
        self.assertEqual(events[0]["library_lines"], 100)


class GitHistory(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.env = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_SYSTEM=os.devnull,
                        GIT_CONFIG_NOSYSTEM="1", GIT_AUTHOR_NAME="Test", GIT_AUTHOR_EMAIL="t@e",
                        GIT_COMMITTER_NAME="Test", GIT_COMMITTER_EMAIL="t@e")
        self.git("init", "-q", "-b", "main")
        self.area = self.repo / "TauCetiRoadmap/Widgets"
        self.area.mkdir(parents=True)
        (self.area / "README.md").write_text(README)
        (self.area / "Suggested.lean").write_text("example : True := by trivial\n")
        (self.repo / "TauCeti").mkdir()
        (self.repo / "TauCeti/A.lean").write_text("example : True := by trivial\n")

    def tearDown(self):
        self.temp.cleanup()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args], env=self.env, text=True)

    def commit(self, day, message="change"):
        self.env.update(GIT_AUTHOR_DATE=f"2026-07-{day:02d}T12:00:00Z",
                        GIT_COMMITTER_DATE=f"2026-07-{day:02d}T12:00:00Z")
        self.git("add", "-A")
        self.git("commit", "-qm", message)

    def test_archive_and_reopen_preserve_total_and_withdraw_completion_credit(self):
        self.commit(1)
        before = len(README.splitlines()) + 1
        destination = self.repo / "Completed/Widgets"
        destination.parent.mkdir()
        shutil.move(self.area, destination)
        self.commit(3)
        (destination / "README.md").write_text(README + "Edited after archival.\n")
        self.commit(4)
        shutil.move(destination, self.area)
        self.commit(5)
        rows, events = completion.history(self.repo, "HEAD", dt.date(2026, 7, 7))
        self.assertEqual([r["date"] for r in rows], [f"2026-07-{n:02d}" for n in range(1, 7)])
        self.assertEqual(rows[1]["spec_lines"], rows[2]["spec_lines"])
        self.assertEqual(rows[2]["completed_spec_lines"], before)
        self.assertEqual(rows[3]["completion_credit"]["spec_lines"], before)
        self.assertEqual(rows[4]["completion_credit"], dict(spec_lines=0, layers=0))
        self.assertEqual(sum(e["units"] for e in events if e["basis"] == "spec_lines"), 0)

    def test_current_day_and_side_branch_reports_do_not_enter_history(self):
        self.commit(1)
        self.git("checkout", "-qb", "feature")
        (self.area / "STATUS.md").write_text(report(states=("done", "done")))
        self.commit(2)
        self.git("checkout", "-q", "main")
        self.env.update(GIT_AUTHOR_DATE="2026-07-03T12:00:00Z",
                        GIT_COMMITTER_DATE="2026-07-03T12:00:00Z")
        self.git("merge", "--no-ff", "-qm", "merge report", "feature")
        # The feature report is absent on day 2 and lands on day 3. Today's edit is excluded.
        (self.area / "STATUS.md").write_text(report(states=("partial", "partial")))
        self.commit(5)
        rows, _ = completion.history(self.repo, "HEAD", dt.date(2026, 7, 5))
        self.assertEqual(rows[0]["completed_layers"], 0)
        self.assertEqual(rows[1]["completed_layers"], 0)
        self.assertEqual(rows[-1]["date"], "2026-07-04")
        self.assertEqual(rows[-1]["completed_layers"], 2)

    def test_generated_assets_are_valid_xml_and_machine_readable(self):
        self.commit(1)
        (self.area / "STATUS.md").write_text(report())
        self.commit(8)
        out = self.root / "output"
        payload = completion.generate(self.repo, "HEAD", self.repo, "HEAD", out,
                                      dt.date(2026, 7, 9),
                                      [(f"2026-07-{n:02d}", n * 100) for n in range(1, 9)])
        for path in out.glob("*.svg"):
            ET.parse(path)
        saved = json.loads((out / "roadmap-completion.json").read_text())
        self.assertEqual(saved, payload)
        self.assertEqual(saved["history"][-1]["completed_layers"], 1)
        self.assertEqual(len(list(out.glob("*.svg"))), 3)
        self.assertEqual({path.name for path in out.iterdir()}, set(completion.ASSET_NAMES))

    def test_cached_loc_data_fixes_the_cutoff_across_midnight(self):
        self.commit(1)
        (self.area / "STATUS.md").write_text(report())
        self.commit(8)
        payload = completion.generate(self.repo, "HEAD", self.repo, "HEAD", self.root / "output",
                                      code_data=[("2026-07-01", 100), ("2026-07-07", 700)])
        self.assertEqual(payload["last_full_day"], "2026-07-07")
        self.assertEqual(payload["history"][-1]["completed_layers"], 0)


if __name__ == "__main__":
    unittest.main()
