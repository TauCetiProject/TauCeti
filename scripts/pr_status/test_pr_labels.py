#!/usr/bin/env python3
"""Unit tests for the PR-status derivation (core) and the label collapse (labels).

Pure logic only: the GitHub-reading helpers in core are monkeypatched, so these
run with no network and no `gh`. Run with:  python3 -m unittest test_pr_labels
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core  # noqa: E402
import labels  # noqa: E402


class ReviewState(unittest.TestCase):
    HEAD = "abc123"

    def test_no_scoreboard_is_none(self):
        self.assertEqual(core.review_state({}, self.HEAD), "none")

    def test_behind_head_is_running(self):
        meta = {"head_sha": "old", "runs": [{"verdict": "approve"}]}
        self.assertEqual(core.review_state(meta, self.HEAD), "running")

    def test_at_head_all_approve_is_approved(self):
        meta = {"head_sha": self.HEAD,
                "runs": [{"verdict": "approve"}, {"verdict": "approve"}]}
        self.assertEqual(core.review_state(meta, self.HEAD), "approved")

    def test_at_head_error_counts_as_approve_for_greenness(self):
        # An "error" verdict is not blocking (mirrors round.sh): all-approve-or-
        # error still reads approved only if every non-error rubric approved.
        meta = {"head_sha": self.HEAD,
                "runs": [{"verdict": "approve"}, {"verdict": "error"}]}
        # Not all are "approve", and none is blocking -> running, green so far.
        self.assertEqual(core.review_state(meta, self.HEAD), "running")

    def test_at_head_blocking_is_changes(self):
        meta = {"head_sha": self.HEAD,
                "runs": [{"verdict": "approve"}, {"verdict": "request_changes"}]}
        self.assertEqual(core.review_state(meta, self.HEAD), "changes")

    def test_at_head_no_runs_is_running(self):
        meta = {"head_sha": self.HEAD, "runs": []}
        self.assertEqual(core.review_state(meta, self.HEAD), "running")


class DerivedLabel(unittest.TestCase):
    def label(self, lifecycle="open", ci=None, review="none"):
        return labels.derived_label(
            {"lifecycle": lifecycle, "ci": ci, "review": review,
             "head": "h", "title": "t"})

    def test_merged_and_closed_have_no_label(self):
        self.assertIsNone(self.label(lifecycle="merged"))
        self.assertIsNone(self.label(lifecycle="closed"))

    def test_ci_not_reported_is_awaiting_ci(self):
        self.assertEqual(self.label(ci=None), "awaiting-CI")

    def test_ci_running_is_awaiting_ci(self):
        self.assertEqual(self.label(ci="running"), "awaiting-CI")

    def test_ci_failure_is_awaiting_author(self):
        self.assertEqual(self.label(ci="failure", review="none"), "awaiting-author")

    def test_ci_green_no_verdict_is_awaiting_review(self):
        self.assertEqual(self.label(ci="success", review="none"), "awaiting-review")
        self.assertEqual(self.label(ci="success", review="running"), "awaiting-review")

    def test_ci_green_changes_is_awaiting_author(self):
        self.assertEqual(self.label(ci="success", review="changes"), "awaiting-author")

    def test_ci_green_approved_is_ready_to_merge(self):
        self.assertEqual(self.label(ci="success", review="approved"), "ready-to-merge")

    def test_ci_failure_dominates_stale_approval(self):
        # A red build on a new commit outranks a stale green review.
        self.assertEqual(self.label(ci="failure", review="approved"), "awaiting-author")


class Derive(unittest.TestCase):
    """core.derive glues pr_state/ci_status/scoreboard_meta together; stub them."""

    def setUp(self):
        self._saved = (core.pr_state, core.ci_status, core.scoreboard_meta)

    def tearDown(self):
        core.pr_state, core.ci_status, core.scoreboard_meta = self._saved

    def stub(self, state="open", merged=False, ci="success", meta=None):
        core.pr_state = lambda pr: {
            "state": state, "merged": merged, "head": "H", "title": "T"}
        core.ci_status = lambda head: ci
        core.scoreboard_meta = lambda pr: (meta or {})

    def test_open_clears_nothing(self):
        self.stub(ci="running")
        d = core.derive("1")
        self.assertEqual(d["lifecycle"], "open")
        self.assertEqual(d["ci"], "running")
        self.assertEqual(d["review"], "none")

    def test_merged_clears_ci_and_review(self):
        self.stub(state="closed", merged=True, ci="success")
        d = core.derive("1")
        self.assertEqual(d["lifecycle"], "merged")
        self.assertIsNone(d["ci"])
        self.assertIsNone(d["review"])

    def test_closed_unmerged_clears_ci_and_review(self):
        self.stub(state="closed", merged=False)
        d = core.derive("1")
        self.assertEqual(d["lifecycle"], "closed")
        self.assertIsNone(d["ci"])

    def test_ci_override_none_maps_to_none(self):
        self.stub(ci="success")
        # Even though the build status is success, an explicit "none" override wins.
        self.assertIsNone(core.derive("1", ci_override="none")["ci"])

    def test_ci_override_running_wins(self):
        self.stub(ci="success")
        self.assertEqual(core.derive("1", ci_override="running")["ci"], "running")

    def test_ci_override_not_read_when_terminal(self):
        self.stub(state="closed", merged=True)
        self.assertIsNone(core.derive("1", ci_override="running")["ci"])


if __name__ == "__main__":
    unittest.main()
