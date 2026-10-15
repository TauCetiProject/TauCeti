#!/usr/bin/env python3
"""Regression tests for merge-engine classification, arrival dates and merge timelines."""
import datetime as dt
import json
import sqlite3
import tempfile
import unittest
import xml.etree.ElementTree as ET
from pathlib import Path

import ci_daily_graphs as daily
import ci_stats_graphs as fleet
import generated_assets


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

    def test_other_job_waits_stop_at_their_complete_day(self):
        self.build(1, 'pr', day='2026-10-06')
        self.db.execute("INSERT INTO jobs VALUES ('TauCeti',1,999,'label','2026-10-06T12:00:00Z',NULL,'success','github',600,2,NULL)")
        m = daily.metrics(self.db, '2026-10-05', '2026-10-07', daily.ts('2026-10-06T12:00:00Z'))
        self.assertNotIn(('2026-10-06', 'other GitHub jobs'), m['wait'])
        self.assertIn(('2026-10-06', 'PR, Namespace'), m['wait'])

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


class MergeTimelinesTest(unittest.TestCase):
    def setUp(self):
        self.db = sqlite3.connect(":memory:")
        self.addCleanup(self.db.close)
        self.db.executescript("""
            CREATE TABLE merge_observations (observed_at TEXT, eligible_json TEXT);
            CREATE TABLE runs (repo TEXT, run_id INTEGER, run_attempt INTEGER, workflow TEXT,
                               trigger TEXT, conclusion TEXT, created_at TEXT);
            CREATE TABLE merge_builds (repo TEXT, run_id INTEGER, engine TEXT,
                                       batch_id INTEGER, members_json TEXT);
        """)
        self.since = daily.ts("2026-10-06T00:00:00Z")
        self.until = daily.ts("2026-10-08T12:00:00Z")

    def sample(self, stamp, prs):
        self.db.execute("INSERT INTO merge_observations VALUES (?,?)",
                        (stamp, json.dumps([{"pr": p, "queued": p == 42} for p in prs])))

    def staging(self, number, prs, conclusion="success", *, repo="TauCeti", attempt=1,
                trigger="bors_staging", engine="bors", workflow=daily.PR_BUILD,
                stamp="2026-10-07T10:00:00Z"):
        self.db.execute("INSERT INTO runs VALUES (?,?,?,?,?,?,?)",
                        (repo, number, attempt, workflow, trigger, conclusion, stamp))
        self.db.execute("INSERT INTO merge_builds VALUES (?,?,?,?,?)",
                        (repo, number, engine, number+100, json.dumps([{"pr": p} for p in prs])))

    def history(self):
        return daily.merge_history(self.db, self.since, self.until)

    def svg(self, name):
        return ET.fromstring(daily.merge_charts(self.db, self.until)[name])

    def test_backlog_counts_distinct_ready_prs_including_those_queued(self):
        self.sample("2026-10-07T10:00:00Z", [42, 43, 42])
        self.sample("2026-10-07T10:01:00Z", [])  # Observed zero is a real value.
        self.assertEqual(self.history()["queue"],
                         [(daily.ts("2026-10-07T10:00:00Z"), 2),
                          (daily.ts("2026-10-07T10:01:00Z"), 0)])

    def test_fractional_timestamps_and_partial_day_respect_window(self):
        for stamp in ("2026-10-05T23:59:59.999999Z", "2026-10-06T00:00:00Z",
                      "2026-10-08T11:59:59.999000Z", "2026-10-08T12:00:00Z"):
            self.sample(stamp, [42])
            self.staging(len(self.db.execute("SELECT * FROM runs").fetchall()), [42], stamp=stamp)
        m = self.history()
        self.assertEqual(len(m["queue"]), 2)
        self.assertEqual(len(m["runs"]), 2)
        self.assertGreater(m["queue"][-1][0], daily.ts("2026-10-08T00:00:00Z"))

    def test_production_runs_use_batch_membership_and_latest_overall_result(self):
        self.staging(1, [42, 43, 42], "failure", attempt=2)
        self.staging(2, [42, 43], stamp="2026-10-07T11:00:00Z")  # Same PRs, separate run.
        self.staging(3, [99], trigger="bors_pilot")
        self.staging(4, [99], trigger="bors_unknown")
        self.staging(5, [99], engine="queue", trigger="merge_queue")
        self.staging(6, [99], repo="TauCetiReview")
        self.staging(7, [99], workflow=".github/workflows/other.yml")
        self.staging(8, [])
        m = self.history()
        self.assertEqual([(r["run_id"], r["prs"], r["conclusion"], r["attempt"]) for r in m["runs"]],
                         [(1, 2, "failure", 2), (2, 2, "success", 1)])
        self.assertEqual(m["missing_members"], 1)
        self.assertIn("1 runs omitted", daily.merge_charts(self.db, self.until)["ci-bors-staging.svg"])

    def test_staging_dots_use_elapsed_time_batch_size_and_outcome(self):
        self.staging(1, [41], stamp="2026-10-07T01:00:00Z")
        self.staging(2, [41, 42, 43], "failure", stamp="2026-10-07T03:00:00Z")
        self.staging(3, [41], "cancelled", stamp="2026-10-07T09:00:00Z")
        dots = list(self.svg("ci-bors-staging.svg").iter("{http://www.w3.org/2000/svg}circle"))
        self.assertEqual([p.attrib["fill"] for p in dots], [daily.PALETTE[5], daily.PALETTE[3], daily.MUTED])
        xs = [float(p.attrib["cx"]) for p in dots]
        self.assertAlmostEqual((xs[2]-xs[1])/(xs[1]-xs[0]), 3, delta=0.02)
        self.assertLess(float(dots[1].attrib["cy"]), float(dots[0].attrib["cy"]))
        self.assertIn("3 PRs, failure", dots[1][0].text)

    def test_queue_gaps_are_not_zeroes_or_connected_and_last_sample_is_not_extended(self):
        for stamp, prs in [("2026-10-07T10:00:00Z", [42]), ("2026-10-07T10:01:00Z", []),
                           ("2026-10-07T11:00:00Z", [42]), ("2026-10-07T11:01:00Z", [42])]:
            self.sample(stamp, prs)
        root = self.svg("ci-queue-size.svg")
        lines = list(root.iter("{http://www.w3.org/2000/svg}polyline"))
        self.assertEqual(len(lines), 2)
        self.assertIn(f",{daily.BOTTOM:.1f}", lines[0].attrib["points"])
        end_x = float(lines[-1].attrib["points"].split()[-1].split(",")[0])
        self.assertLess(end_x, daily.W-daily.R)

    def test_non_failure_terminal_outcomes_are_grey(self):
        for number, conclusion in enumerate(("stale", "action_required", "neutral"), 1):
            self.staging(number, [42], conclusion)
        dots = list(self.svg("ci-bors-staging.svg").iter("{http://www.w3.org/2000/svg}circle"))
        self.assertEqual([p.attrib["fill"] for p in dots], [daily.MUTED] * 3)

    def test_eleven_pr_maximum_has_whole_pr_ticks_on_both_graphs(self):
        self.sample("2026-10-07T10:00:00Z", list(range(1, 12)))
        self.staging(1, list(range(1, 12)))
        for name in ("ci-queue-size.svg", "ci-bors-staging.svg"):
            ticks = [node.text for node in self.svg(name).iter("{http://www.w3.org/2000/svg}text")
                     if node.attrib.get("text-anchor") == "end"]
            self.assertTrue(all(float(t).is_integer() for t in ticks), ticks)
            self.assertGreaterEqual(float(ticks[-1]), 11)

    def test_short_multiday_window_has_distinct_time_tick_labels(self):
        self.staging(1, [42], stamp="2026-10-06T10:00:00Z")
        labels = [node.text for node in self.svg("ci-bors-staging.svg").iter("{http://www.w3.org/2000/svg}text")
                  if node.attrib.get("y") == str(daily.BOTTOM+18)]
        self.assertGreater(len(labels), 1)
        self.assertEqual(len(labels), len(set(labels)))
        self.assertTrue(all(":" in label for label in labels))

    def test_empty_history_has_explicit_messages_and_whole_pr_ticks(self):
        charts = daily.merge_charts(self.db, self.until)
        self.assertIn("No queue observations", charts["ci-queue-size.svg"])
        self.assertIn("No staging runs", charts["ci-bors-staging.svg"])
        for name, svg in charts.items():
            root = ET.fromstring(svg)
            self.assertIn(name, generated_assets.GENERATED_ASSETS)
            ticks = [node.text for node in root.iter("{http://www.w3.org/2000/svg}text")
                     if node.attrib.get("text-anchor") == "end"]
            self.assertTrue(all(float(t).is_integer() for t in ticks))


    def test_incomplete_initial_candidate_scan_is_a_gap_and_completed_snapshot_can_be_reused(self):
        self.db.execute("CREATE TABLE queue_observation_metadata (observed_at TEXT, eligible_count INTEGER, candidate_scan_complete INTEGER, candidate_snapshot_at TEXT)")
        for minute, complete, snapshot, count in [(0, 1, '2026-10-07T10:00:00Z', 17),
                                                  (1, 0, None, 2),
                                                  (2, 0, '2026-10-07T10:00:00Z', 17)]:
            stamp = f'2026-10-07T10:0{minute}:00Z'
            self.sample(stamp, [42])
            self.db.execute('INSERT INTO queue_observation_metadata VALUES (?,?,?,?)',
                            (stamp, count, complete, snapshot))
        self.assertEqual([n for _, n in self.history()['queue']], [17, None, 17])
        lines = list(self.svg('ci-queue-size.svg').iter('{http://www.w3.org/2000/svg}polyline'))
        self.assertEqual(len(lines), 2)

    def test_active_staging_runs_have_no_result_dots(self):
        self.staging(1, [42], None)
        self.assertFalse(self.history()['runs'])

    def test_inventory_gap_union_clips_intervals_and_shades_partial_results(self):
        self.db.execute('CREATE TABLE stream_coverage (repo TEXT, stream TEXT, since TEXT, complete_to TEXT)')
        for lo, hi in [('2026-10-05', '2026-10-06T06:00:00Z'),
                       ('2026-10-06T05:00:00Z', '2026-10-06T12:00:00Z'),
                       ('2026-10-07', '2026-10-10'), ('2026-10-11', '2026-10-12')]:
            self.db.execute('INSERT INTO stream_coverage VALUES (?,?,?,?)', ('TauCeti', 'inventory', lo, hi))
        self.assertEqual(daily.inventory_gaps(self.db, self.since, self.until),
                         [(daily.ts('2026-10-06T12:00:00Z'), daily.ts('2026-10-07'))])
        self.staging(1, [42], stamp='2026-10-06T18:00:00Z')
        svg = self.svg('ci-bors-staging.svg')
        self.assertTrue(any(n.attrib.get('class') == 'coverage-gap' for n in svg))
        self.assertEqual(len(list(svg.iter('{http://www.w3.org/2000/svg}circle'))), 1)

    def test_fresh_timelines_survive_stale_fleet_without_replacing_its_fallbacks(self):
        self.db.executescript("""
            CREATE TABLE coverage (repo TEXT, complete_to TEXT);
            INSERT INTO coverage VALUES ('TauCeti', '2026-10-02T00:00:00Z');
            CREATE TABLE stream_coverage (repo TEXT, stream TEXT, since TEXT, complete_to TEXT);
            INSERT INTO stream_coverage VALUES ('TauCeti','inventory','2026-10-06','2026-10-08T12:00:00Z');
        """)
        self.sample('2026-10-08T11:00:00Z', [42])
        self.staging(1, [42])
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            (out/'ci-fleet-72h.svg').write_text('preserved fleet')
            (out/'ci-duration.svg').write_text('preserved daily')
            errors = fleet.generate(self.db, out, self.until)
            self.assertEqual(len(errors), 2)
            self.assertEqual((out/'ci-fleet-72h.svg').read_text(), 'preserved fleet')
            self.assertEqual((out/'ci-duration.svg').read_text(), 'preserved daily')
            ET.parse(out/'ci-queue-size.svg'); ET.parse(out/'ci-bors-staging.svg')
            status = json.loads((out/'ci-freshness.json').read_text())['groups']
            self.assertEqual({g: s['status'] for g, s in status.items()},
                             {'fleet': 'stale', 'daily': 'stale', 'queue': 'updated', 'staging': 'updated'})
            self.assertIn('ci-freshness.json', generated_assets.GENERATED_ASSETS)

    def test_missing_staging_schema_does_not_block_queue(self):
        self.db.execute('DROP TABLE merge_builds')
        self.sample('2026-10-08T11:00:00Z', [42])
        self.assertEqual(list(daily.merge_charts(self.db, self.until, include_staging=False)),
                         ['ci-queue-size.svg'])

    def test_builds_use_their_own_coverage_and_queue_includes_last_sample(self):
        self.db.executescript("""
            CREATE TABLE coverage (repo TEXT, complete_to TEXT);
            INSERT INTO coverage VALUES ('TauCeti','2026-10-02'),('Other','2026-10-01');
            CREATE TABLE stream_coverage (repo TEXT, stream TEXT, since TEXT, complete_to TEXT);
            INSERT INTO stream_coverage VALUES ('TauCeti','build-jobs','2026-10-01','2026-10-08');
        """)
        self.sample('2026-10-08T11:00:00Z', [42])
        ends = fleet.chart_cutoffs(self.db, self.until)
        self.assertEqual(ends['fleet'], daily.ts('2026-10-01'))
        self.assertEqual(ends['daily'], daily.ts('2026-10-08'))
        history = daily.merge_history(self.db, self.since, ends['queue'], include_staging=False)
        self.assertEqual(len(history['queue']), 1)

    def test_generator_writes_new_assets_with_the_existing_charts(self):
        # Exercise the public entry point and generated-asset list together.
        schema = MergeQueueChartsTest()
        schema.setUp()
        self.addCleanup(schema.doCleanups)
        schema.db.executescript("""
            ALTER TABLE runs ADD COLUMN run_attempt INTEGER;
            ALTER TABLE runs ADD COLUMN conclusion TEXT;
            ALTER TABLE runs ADD COLUMN jobs_fetched INTEGER;
            ALTER TABLE runs ADD COLUMN updated_at TEXT;
            ALTER TABLE jobs ADD COLUMN completed_at TEXT;
            CREATE TABLE merge_observations (observed_at TEXT, eligible_json TEXT);
            CREATE TABLE merge_builds (repo TEXT, run_id INTEGER, engine TEXT,
                                       batch_id INTEGER, members_json TEXT);
            CREATE TABLE coverage (repo TEXT, complete_to TEXT);
            INSERT INTO coverage VALUES ('TauCeti','2026-10-08T12:00:00Z');
        """)
        schema.db.execute("INSERT INTO runs (repo,run_id,workflow,trigger,created_at) VALUES (?,?,?,?,?)",
                          ("TauCeti", 1, daily.PR_BUILD, "pr", "2026-10-06T10:00:00Z"))
        schema.db.commit()
        with tempfile.TemporaryDirectory() as directory:
            dbpath = Path(directory) / "ci.sqlite"
            with sqlite3.connect(dbpath) as disk:
                schema.db.backup(disk)
            fleet.main(["--db", str(dbpath), "--until", "2026-10-08T12:00:00Z", "--out-dir", directory])
            for name in daily.ASSET_NAMES:
                ET.parse(Path(directory) / name)


if __name__ == "__main__":
    unittest.main()
