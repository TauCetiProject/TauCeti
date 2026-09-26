#!/usr/bin/env python3
"""Regression tests for the lines-of-code graph.

Run with:

    python3 scripts/test_loc_graph.py
"""

import datetime as dt
import os
import pathlib
import subprocess
import tempfile
import unittest

import loc_graph


def git(repo: pathlib.Path, *args: str, env=None) -> None:
    subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True,
        env=env,
        stdout=subprocess.DEVNULL,
    )


class SeriesTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = pathlib.Path(self.tmp.name)
        self.env = os.environ.copy()
        self.env.update({
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_CONFIG_SYSTEM": os.devnull,
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_TERMINAL_PROMPT": "0",
        })
        git(self.repo, "init", "--quiet", "--initial-branch=main", env=self.env)
        git(self.repo, "config", "user.name", "Test", env=self.env)
        git(self.repo, "config", "user.email", "test@example.com", env=self.env)

    def tearDown(self):
        self.tmp.cleanup()

    def commit(self, author_time: str, committer_time: str, lines: int) -> None:
        source = self.repo / "Tracked.lean"
        source.write_text("example : True := by trivial\n" * lines)
        git(self.repo, "add", "Tracked.lean", env=self.env)
        env = self.env.copy()
        env["GIT_AUTHOR_DATE"] = author_time
        env["GIT_COMMITTER_DATE"] = committer_time
        git(self.repo, "commit", "--quiet", "--no-verify",
            "-m", f"{lines} lines", env=env)

    def test_uses_committer_dates(self):
        self.commit("2026-06-02T12:00:00+0000",
                    "2026-06-03T12:00:00+0000", 1)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD",
                                today=dt.date(2026, 6, 4))

        self.assertEqual(data, [("2026-06-03", 1)])

    def test_normalizes_committer_dates_to_utc(self):
        # These commits have decreasing local calendar dates but increasing UTC
        # timestamps, reproducing the timezone form of the graph reversal.
        self.commit("2026-07-20T00:15:00+1000",
                    "2026-07-20T00:15:00+1000", 1)
        self.commit("2026-07-19T15:00:00+0000",
                    "2026-07-19T15:00:00+0000", 2)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD",
                                today=dt.date(2026, 7, 20))

        self.assertEqual(data, [("2026-07-19", 2)])

    def test_last_commit_of_the_day_wins(self):
        self.commit("2026-06-02T10:00:00+0000",
                    "2026-06-02T10:00:00+0000", 1)
        self.commit("2026-06-03T10:00:00+0000",
                    "2026-06-03T10:00:00+0000", 5)
        self.commit("2026-06-03T11:00:00+0000",
                    "2026-06-03T11:00:00+0000", 3)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD",
                                today=dt.date(2026, 6, 4))

        self.assertEqual(data, [("2026-06-02", 1), ("2026-06-03", 3)])

    def test_days_without_commits_carry_the_previous_count(self):
        self.commit("2026-07-11T10:00:00+0000",
                    "2026-07-11T10:00:00+0000", 4)
        self.commit("2026-07-15T10:00:00+0000",
                    "2026-07-15T10:00:00+0000", 9)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD",
                                today=dt.date(2026, 7, 16))

        self.assertEqual(data, [
            ("2026-07-11", 4),
            ("2026-07-12", 4),
            ("2026-07-13", 4),
            ("2026-07-14", 4),
            ("2026-07-15", 9),
        ])


    def test_yesterday_is_in_and_today_is_out(self):
        self.commit("2026-07-10T10:00:00+0000",
                    "2026-07-10T10:00:00+0000", 4)
        self.commit("2026-07-11T23:59:59+0000",
                    "2026-07-11T23:59:59+0000", 6)
        self.commit("2026-07-12T00:00:00+0000",
                    "2026-07-12T00:00:00+0000", 9)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD",
                                today=dt.date(2026, 7, 12))

        # The commit one second before midnight counts; the one at midnight does not.
        self.assertEqual(data, [("2026-07-10", 4), ("2026-07-11", 6)])

    def test_a_quiet_stretch_reaches_the_last_completed_day(self):
        self.commit("2026-07-10T10:00:00+0000",
                    "2026-07-10T10:00:00+0000", 4)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD",
                                today=dt.date(2026, 7, 14))

        # Nothing landed after the 10th, so the count is unchanged through the 13th. Without
        # this the chart would end on the 10th and appear to have stopped being regenerated.
        self.assertEqual(data, [("2026-07-10", 4), ("2026-07-11", 4),
                                ("2026-07-12", 4), ("2026-07-13", 4)])

    def test_a_repository_whose_only_commit_is_today_is_empty_not_broken(self):
        self.commit("2026-07-12T08:00:00+0000",
                    "2026-07-12T08:00:00+0000", 4)

        data = loc_graph.series(str(self.repo), ["Tracked.lean"], "HEAD",
                                today=dt.date(2026, 7, 12))

        self.assertEqual(data, [])


class CarryToTest(unittest.TestCase):
    def test_it_does_not_reach_backwards(self):
        points = [("2026-07-10", 4), ("2026-07-14", 9)]

        self.assertEqual(loc_graph.carry_to(points, dt.date(2026, 7, 12)), points)

    def test_an_empty_series_stays_empty(self):
        self.assertEqual(loc_graph.carry_to([], dt.date(2026, 7, 12)), [])


class CarryQuietDaysTest(unittest.TestCase):
    def test_leaves_a_contiguous_series_alone(self):
        points = [("2026-06-02", 1), ("2026-06-03", 2)]

        self.assertEqual(loc_graph.carry_quiet_days(points), points)

    def test_does_not_extend_past_either_end(self):
        # Nothing to carry forward from before the first commit, and carrying
        # past the last one would invent a measurement for a day not yet over.
        points = [("2026-06-02", 1), ("2026-06-05", 7)]

        filled = loc_graph.carry_quiet_days(points)

        self.assertEqual(filled[0], ("2026-06-02", 1))
        self.assertEqual(filled[-1], ("2026-06-05", 7))

    def test_handles_an_empty_series(self):
        self.assertEqual(loc_graph.carry_quiet_days([]), [])


if __name__ == "__main__":
    unittest.main()
