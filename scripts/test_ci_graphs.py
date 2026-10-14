#!/usr/bin/env python3
"""Regression tests for merge-engine classification and PR arrival dates."""
import datetime as dt
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch
import xml.etree.ElementTree as ET

import ci_daily_graphs as daily
import ci_stats_graphs as fleet


class MergeQueueChartsTest(unittest.TestCase):
    def setUp(self):
        self.db = sqlite3.connect(":memory:")
        self.addCleanup(self.db.close)
        self.db.executescript("""
            CREATE TABLE runs (repo TEXT, run_id INTEGER, workflow TEXT, trigger TEXT,
                               created_at TEXT);
            CREATE TABLE jobs (repo TEXT, run_id INTEGER, job_id INTEGER, name TEXT,
                               created_at TEXT, started_at TEXT, conclusion TEXT,
                               runner_kind TEXT, wait_s REAL, run_s REAL, failure_class TEXT);
            CREATE TABLE steps (job_id INTEGER, name TEXT, run_s REAL);
            CREATE TABLE main_commits (sha TEXT, committed_at TEXT, pr INTEGER);
            CREATE TABLE main_landings (repo TEXT, head_sha TEXT, landed_at TEXT);
        """)

    def build(self, number, trigger, conclusion="success", *, repo="TauCeti",
              workflow=daily.PR_BUILD, kind="namespace", day="2026-10-06"):
        stamp = day + "T10:00:00Z"
        self.db.execute("INSERT INTO runs VALUES (?,?,?,?,?)",
                        (repo, number, workflow, trigger, stamp))
        self.db.execute("INSERT INTO jobs VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                        (repo, number, number * 10, daily.BUILD, stamp, stamp,
                         conclusion, kind, 120, 600, None))

    def arrival(self, sha, pr, created, landed=None, repo="TauCeti"):
        self.db.execute("INSERT INTO main_commits VALUES (?,?,?)", (sha, created, pr))
        if landed:
            self.db.execute("INSERT INTO main_landings VALUES (?,?,?)", (repo, sha, landed))

    def metrics(self):
        return daily.metrics(self.db, "2026-10-05", "2026-10-07")

    def test_both_engines_include_failed_cancelled_and_retried_builds(self):
        self.build(1, "merge_queue")
        self.build(2, "bors_staging")  # One batch may contain several PRs.
        self.build(3, "bors_staging", "failure")
        self.build(4, "bors_staging", "cancelled")
        # A rerun is another job for the same run, not another PR arrival.
        self.db.execute("INSERT INTO jobs SELECT repo,run_id,job_id+1,name,created_at,"
                        "started_at,conclusion,runner_kind,wait_s,run_s,failure_class "
                        "FROM jobs WHERE run_id=2")
        m = self.metrics()
        self.assertEqual(dict(m["mq"]["2026-10-06"]),
                         {"success": 3, "failure": 1, "cancelled": 1})
        self.assertEqual(len(m["dur"][("2026-10-06", "merge validation")]), 3)
        self.assertEqual(len(m["wait"][("2026-10-06", "merge validation")]), 5)

    def test_pilots_unknown_dispatches_and_other_repositories_are_excluded(self):
        for number, trigger in enumerate(("bors_pilot", "bors_unknown", "repository_dispatch",
                                          "workflow_dispatch"), 1):
            self.build(number, trigger)
        self.build(5, "bors_staging", repo="TauCetiReview")
        self.build(6, "bors_staging", workflow=".github/workflows/other.yml")
        self.assertFalse(self.metrics()["mq"])

    def test_pr_failure_and_runner_picker_totals_do_not_include_bors(self):
        self.build(1, "bors_staging", "failure")
        self.build(2, "pr", "failure", kind="github")
        m = self.metrics()
        self.assertEqual(m["pr_total"]["2026-10-06"], 1)
        self.assertEqual(m["picker"]["2026-10-06"], [1, 0])
        self.assertEqual(sum(m["fails"]["2026-10-06"].values()), 1)

    def test_landing_time_is_main_arrival_not_staging_creation(self):
        self.arrival("a", 42, "2026-10-05T10:00:00Z", "2026-10-06T01:00:00Z")
        self.arrival("b", 43, "2026-10-05T11:00:00Z", "2026-10-06T01:00:00Z")
        m = self.metrics()
        self.assertEqual(dict(m["landed"]), {"2026-10-06": 2})

    def test_duplicate_prs_across_commits_and_days_count_once_at_first_arrival(self):
        self.arrival("a", 42, "2026-10-05T10:00:00Z", "2026-10-06T01:00:00Z")
        self.arrival("b", 42, "2026-10-06T10:00:00Z", "2026-10-07T01:00:00Z")
        self.assertEqual(dict(self.metrics()["landed"]), {"2026-10-06": 1})

    def test_missing_arrival_and_other_repository_evidence_do_not_invent_dates(self):
        self.arrival("a", 42, "2026-10-05T10:00:00Z")
        self.arrival("b", 43, "2026-10-05T10:00:00Z", "2026-10-06T01:00:00Z",
                     repo="TauCetiReview")
        self.assertFalse(self.metrics()["landed"])

    def test_duplicate_pr_first_arriving_before_window_stays_out(self):
        self.arrival("a", 42, "2026-10-03T10:00:00Z", "2026-10-04T01:00:00Z")
        self.arrival("b", 42, "2026-10-06T10:00:00Z", "2026-10-07T01:00:00Z")
        self.assertFalse(self.metrics()["landed"])

    def test_charts_render_both_engines_and_explain_arrival_line(self):
        self.build(1, "bors_staging")
        self.arrival("a", 42, "2026-10-05T10:00:00Z", "2026-10-06T01:00:00Z")
        until = dt.datetime(2026, 10, 8, tzinfo=dt.timezone.utc).timestamp()
        charts = daily.charts(self.db, until)
        for svg in charts.values():
            ET.fromstring(svg)
        self.assertIn("GitHub queue + bors", charts["ci-merge-queue.svg"])
        self.assertIn("PR arrivals on main", charts["ci-merge-queue.svg"])

    def test_fleet_legend_has_clearance_above_running_panel(self):
        data = {"since": 0, "until": 3600, "step": 3600,
                "running": {key: [1.0] for key, _, _ in fleet.SERIES},
                "picked_namespace": [], "queued": {"github": [0], "namespace": [0]},
                "wait_min": {"build": [0], "other": [0]}}
        root = ET.fromstring(fleet.render(data, "Fleet", "Fixture", []))
        texts = list(root.iter("{http://www.w3.org/2000/svg}text"))
        labels = {label for _, label, _ in fleet.SERIES}
        bottom = max(float(node.attrib["y"]) for node in texts if node.text in labels)
        grids = [node for node in root.iter("{http://www.w3.org/2000/svg}line")
                 if node.attrib.get("class") == "grid"]
        top = min(float(node.attrib["y1"]) for node in grids)
        self.assertGreaterEqual(top - bottom, 16)

    def test_fleet_classifies_bors_with_merge_queue_on_both_runner_kinds(self):
        for trigger in daily.MERGE_TRIGGERS:
            self.assertEqual(fleet.classify(daily.BUILD, "namespace", trigger),
                             ("ns-mq", "build"))
            self.assertEqual(fleet.classify(daily.BUILD, "github", trigger),
                             ("gh-build-other", "build"))
        self.assertEqual(fleet.classify(daily.BUILD, "namespace", "bors_pilot"),
                         ("ns-other", "build"))
        self.assertEqual(fleet.classify(daily.BUILD, "github", "pr"),
                         ("gh-build-pr", "build"))


class HistoricalRefreshTest(unittest.TestCase):
    def test_stale_coverage_refreshes_daily_charts_and_still_reports_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            db_path = root / "ci.sqlite"
            db = sqlite3.connect(db_path)
            db.execute("CREATE TABLE coverage (complete_to TEXT)")
            db.execute("INSERT INTO coverage VALUES ('2000-01-02T12:00:00Z')")
            db.commit()
            db.close()
            fallbacks = {name: "previous " + name for name in (
                "ci-fleet-72h.svg", "ci-fleet-30d.svg", "ci-stats.json")}
            for name, contents in fallbacks.items():
                (root / name).write_text(contents)
            charts = {"ci-failures.svg": '<svg xmlns="http://www.w3.org/2000/svg"/>'}
            with patch.object(daily, "charts", return_value=charts) as render_daily, \
                    patch.object(fleet, "load_jobs") as load_jobs, \
                    self.assertRaisesRegex(SystemExit, "rebuilt historical daily charts only"):
                fleet.main(["--db", str(db_path), "--out-dir", str(root)])
            render_daily.assert_called_once()
            self.assertEqual(render_daily.call_args.args[1], fleet.ts("2000-01-02T12:00:00Z"))
            self.assertEqual((root / "ci-failures.svg").read_text(), charts["ci-failures.svg"])
            for name, contents in fallbacks.items():
                self.assertEqual((root / name).read_text(), contents)
            load_jobs.assert_not_called()

    def test_invalid_svg_preserves_every_fallback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "ci-failures.svg").write_text("previous")
            with self.assertRaises(ET.ParseError):
                fleet.write_charts(root, {"ci-failures.svg": "<svg/>", "other.svg": "<broken"})
            self.assertEqual((root / "ci-failures.svg").read_text(), "previous")
            self.assertFalse((root / "other.svg").exists())


if __name__ == "__main__":
    unittest.main()
