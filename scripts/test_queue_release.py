"""Run with python3 scripts/test_queue_release.py."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import queue_release as release


def state(queued=False, base="main", status="OPEN"):
    return {"data": {"repository": {"pullRequest": {
        "isInMergeQueue": queued, "baseRefName": base, "state": status}}}}


PIN_FILES = [[{"filename": "lean-toolchain"}]]


class QueueRelease(unittest.TestCase):
    @patch.object(release, "gh_json")
    def test_pin_on_later_page(self, gh):
        gh.side_effect = [[[{'filename': 'TauCeti/X.lean'}],
                           [{'filename': 'lake-manifest.json'}]], state(status="MERGED")]
        self.assertTrue(release.should_sweep("o/r", 1, "closed"))
        self.assertIn("--paginate", gh.call_args_list[0].args)
        self.assertIn("--slurp", gh.call_args_list[0].args)

    @patch.object(release, "gh_json")
    def test_toolchain_eviction_releases(self, gh):
        gh.side_effect = [PIN_FILES, state()]
        self.assertTrue(release.should_sweep("o/r", 1, "dequeued"))

    @patch.object(release, "gh_json")
    def test_stale_event_does_not_retry_requeued_bump(self, gh):
        gh.side_effect = [PIN_FILES, state(queued=True)]
        self.assertFalse(release.should_sweep("o/r", 1, "dequeued"))

    @patch.object(release, "gh_json")
    def test_non_main_release_does_nothing(self, gh):
        gh.side_effect = [PIN_FILES, state(base="stack-parent")]
        self.assertFalse(release.should_sweep("o/r", 1, "manual"))

    @patch.object(release, "gh_json")
    def test_ordinary_removal_does_not_sweep(self, gh):
        gh.return_value = [[{"filename": "TauCeti/X.lean"}]]
        self.assertFalse(release.should_sweep("o/r", 1, "dequeued"))
        gh.assert_called_once()

    @patch.object(release, "gh_json")
    def test_late_duplicate_dequeue_after_merge_does_not_sweep(self, gh):
        gh.side_effect = [PIN_FILES, state(status="MERGED")]
        self.assertFalse(release.should_sweep("o/r", 1, "dequeued"))

    @patch.object(release, "gh_json")
    def test_unmerged_close_needs_a_dequeue_event(self, gh):
        gh.side_effect = [PIN_FILES, state(status="CLOSED")]
        self.assertFalse(release.should_sweep("o/r", 1, "closed"))
        gh.side_effect = [PIN_FILES, state(status="CLOSED")]
        self.assertTrue(release.should_sweep("o/r", 1, "dequeued"))

    @patch.object(release, "gh_json")
    def test_manual_recovery_of_merged_bump(self, gh):
        gh.side_effect = [PIN_FILES, state(status="MERGED")]
        self.assertTrue(release.should_sweep("o/r", 1, "manual"))

    @patch.object(release, "gh_json")
    def test_api_failure_does_not_mean_unreserved(self, gh):
        gh.side_effect = subprocess.CalledProcessError(1, ["gh"])
        with self.assertRaises(subprocess.CalledProcessError):
            release.should_sweep("o/r", 1, "closed")
        gh.side_effect = [PIN_FILES, dict(state(), errors=[{"message": "partial response"}])]
        with self.assertRaises(RuntimeError):
            release.should_sweep("o/r", 1, "closed")

    def test_unexpected_action_fails_closed(self):
        with self.assertRaises(ValueError):
            release.should_sweep("o/r", 1, "edited")

    @patch.object(release, "should_sweep")
    def test_output_drives_workflow_condition(self, check):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "output"
            for eligible in (False, True):
                check.return_value = eligible
                output.write_text("")
                with patch.dict(os.environ, REPO="o/r", RELEASED_PR="12",
                                RELEASE_ACTION="manual", GITHUB_OUTPUT=str(output)):
                    release.main()
                self.assertEqual(output.read_text(), f"sweep={str(eligible).lower()}\n")
                check.assert_called_with("o/r", 12, "manual")


if __name__ == "__main__":
    unittest.main()
