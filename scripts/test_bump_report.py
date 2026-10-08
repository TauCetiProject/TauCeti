#!/usr/bin/env python3
"""Regression cases for stale downstream boundary reports; no network calls."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import bump_report as br


FKB, PIN, TESTED, GREEN = (c * 40 for c in "abcd")
REPORTED = "2026-10-07T05:36:24Z"


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.report = dict(first_known_bad_commit=FKB, downstream_commit=TESTED,
                           reported_at=REPORTED)
        self.run = dict(head_sha=GREEN, status="completed", conclusion="success",
                        updated_at="2026-10-07T12:00:00Z")
        self.parents = {(TESTED, GREEN), (GREEN, "HEAD")}

    def decide(self, fkb=FKB, current_pin=PIN, relation="ahead", runs=None, green_pin=PIN):
        return br.decision(fkb, current_pin, self.report,
                           lambda: [self.run] if runs is None else runs,
                           compare=lambda *_: relation,
                           ancestor=lambda base, head: (base, head) in self.parents,
                           pin_at=lambda _: green_pin)

    def test_closed_boundary_on_green_main_waits(self):
        waiting, reason = self.decide()
        self.assertTrue(waiting)
        self.assertIn(GREEN, reason)
        self.assertIn(REPORTED, reason)

    def test_current_pin_equal_to_boundary_waits(self):
        self.assertTrue(self.decide(current_pin=FKB, green_pin=FKB)[0])

    def test_reported_boundary_ahead_of_pin_remains_actionable(self):
        self.assertFalse(self.decide(relation="behind")[0])

    def test_diverged_pin_does_not_disprove_failure(self):
        self.assertFalse(self.decide(relation="diverged")[0])

    def test_no_active_boundary_needs_no_ci_reads(self):
        waiting, _ = br.decision("", PIN, {}, lambda: self.fail("unexpected CI query"),
                                  compare=None, ancestor=None, pin_at=None)
        self.assertFalse(waiting)

    def test_no_green_evidence_keeps_report_actionable(self):
        self.assertFalse(self.decide(runs=[])[0])
        self.assertFalse(self.decide(green_pin=FKB)[0])
        for status, conclusion in [("in_progress", ""), ("completed", "failure")]:
            with self.subTest(status=status, conclusion=conclusion):
                self.run.update(status=status, conclusion=conclusion)
                self.assertFalse(self.decide()[0])

    def test_green_source_must_follow_tested_source_and_belong_to_main(self):
        for parents in [set(), {(GREEN, "HEAD")}, {(TESTED, GREEN)}]:
            with self.subTest(parents=parents):
                self.parents = parents
                self.assertFalse(self.decide()[0])

    def test_success_before_validation_does_not_disprove_report(self):
        self.run["updated_at"] = "2026-10-07T01:00:00Z"
        self.assertFalse(self.decide()[0])

    def test_failure_on_same_source_is_not_dismissed(self):
        self.run["head_sha"] = TESTED
        self.assertFalse(self.decide()[0])

    def test_old_success_cannot_hide_later_main_failure(self):
        failure = dict(self.run, conclusion="failure")
        self.assertFalse(self.decide(runs=[failure, self.run])[0])

    def test_cancelled_run_does_not_hide_green_evidence(self):
        cancelled = dict(self.run, conclusion="cancelled")
        self.assertTrue(self.decide(runs=[cancelled, self.run])[0])

    def test_partial_snapshot_publication_waits(self):
        self.report["first_known_bad_commit"] = PIN
        self.assertTrue(self.decide()[0])

    def test_missing_validation_metadata_waits(self):
        for key in ["reported_at", "downstream_commit"]:
            with self.subTest(key=key):
                saved = self.report.pop(key)
                self.assertTrue(self.decide()[0])
                self.report[key] = saved

    def test_export_time_does_not_make_an_old_validation_fresh(self):
        self.report["exported_at"] = "2026-10-08T00:48:34Z"
        self.assertTrue(self.decide()[0])

    def test_unknown_ancestry_fails_instead_of_claiming_resolution(self):
        with self.assertRaises(ValueError):
            self.decide(relation="unknown")

    def test_malformed_metadata_fails(self):
        self.report["downstream_commit"] = "not-a-sha"
        with self.assertRaises(ValueError):
            self.decide()
        self.report["downstream_commit"] = TESTED
        self.report["reported_at"] = "2026-10-07T05:36:24"
        with self.assertRaises(ValueError):
            self.decide()

    def test_cli_outputs_preserve_boundary_while_waiting(self):
        with tempfile.TemporaryDirectory() as directory:
            output, summary = (Path(directory) / name for name in ["output", "summary"])
            boundary = {"downstreams": {"TauCeti": {
                "repo": "TauCetiProject/TauCeti", "first_known_bad_commit": FKB}}}
            runs = {"downstreams": {"TauCeti": {
                "repo": "TauCetiProject/TauCeti", **self.report}}}
            manifest = json.dumps({"packages": [{"name": "mathlib", "rev": PIN}]})
            with patch.object(br, "fetch_snapshot", side_effect=[boundary, runs]), \
                    patch.object(br.Path, "read_text", return_value=manifest), \
                    patch.object(br, "gh_api", side_effect=[{"status": "ahead"},
                                                            {"workflow_runs": [self.run]}]), \
                    patch.object(br, "git_ancestor", return_value=True), \
                    patch.object(br, "git_pin", return_value=PIN), \
                    patch.dict(br.os.environ, {"GITHUB_OUTPUT": str(output),
                                               "GITHUB_STEP_SUMMARY": str(summary)}), \
                    patch("sys.argv", ["bump_report.py"]):
                br.main()
            self.assertEqual(output.read_text(), f"commit={FKB}\nawaiting_revalidation=true\n")
            self.assertIn("creates no incompatibility issue or fix PR", summary.read_text())


if __name__ == "__main__":
    unittest.main()
