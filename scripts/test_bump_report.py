#!/usr/bin/env python3
"""Regression cases for stale downstream boundary reports; no network calls."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import bump_report as br


FKB, PIN, TESTED, GREEN = (c * 40 for c in "abcd")
OLD_PIN = "e" * 40
REPORTED = "2026-10-07T05:36:24Z"


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.report = dict(first_known_bad_commit=FKB, downstream_commit=TESTED,
                           reported_at=REPORTED)
        self.run = dict(head_sha=GREEN, status="completed", conclusion="success",
                        updated_at="2026-10-07T12:00:00Z")
        self.parents = {(TESTED, GREEN), (GREEN, "HEAD")}

    def decide(self, fkb=FKB, current_pin=PIN, relation="ahead", runs=None,
               green_pin=PIN, tested_pin=OLD_PIN):
        return br.decision(fkb, current_pin, self.report,
                           lambda: [self.run] if runs is None else runs,
                           compare=lambda *_: relation,
                           ancestor=lambda base, head: (base, head) in self.parents,
                           pin_at=lambda commit: tested_pin if commit == TESTED else green_pin)

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

    def test_success_during_a_long_validation_supersedes_older_source(self):
        self.run["updated_at"] = "2026-10-07T01:00:00Z"
        self.assertTrue(self.decide()[0])

    def test_success_on_reported_source_does_not_disprove_failure(self):
        self.run["head_sha"] = TESTED
        self.parents.update({(TESTED, "HEAD"), (TESTED, TESTED)})
        self.assertFalse(self.decide(tested_pin=PIN)[0])

    def test_old_success_cannot_hide_later_main_failure(self):
        failure = dict(self.run, conclusion="failure")
        self.assertFalse(self.decide(runs=[failure, self.run])[0])

    def test_cancelled_run_does_not_hide_green_evidence(self):
        cancelled = dict(self.run, conclusion="cancelled")
        self.assertTrue(self.decide(runs=[cancelled, self.run])[0])

    def test_partial_snapshot_publication_waits(self):
        self.report["first_known_bad_commit"] = PIN
        self.assertTrue(self.decide()[0])

    def test_incomplete_reports_do_not_suppress_a_forward_incompatibility(self):
        for report in [{}, dict(self.report, first_known_bad_commit=PIN),
                       dict(self.report, reported_at=None), dict(self.report, downstream_commit=None)]:
            with self.subTest(report=report):
                self.report = report
                self.assertFalse(self.decide(relation="behind")[0])
                self.assertFalse(self.decide(relation="diverged")[0])

    def test_revalidation_on_current_pin_remains_actionable(self):
        self.assertFalse(self.decide(tested_pin=PIN)[0])

    def test_missing_reported_source_is_not_evidence_of_a_fix(self):
        self.assertFalse(self.decide(tested_pin=None)[0])

    def test_old_pin_ci_does_not_hide_a_later_failure_with_current_pin(self):
        old = "f" * 40
        self.parents.add((old, "HEAD"))
        failure = dict(self.run, conclusion="failure")
        self.assertFalse(br.decision(FKB, PIN, self.report,
                                     lambda: [dict(self.run, head_sha=old), failure, self.run],
                                     compare=lambda *_: "ahead",
                                     ancestor=lambda base, head: (base, head) in self.parents,
                                     pin_at=lambda commit: PIN if commit == GREEN else OLD_PIN)[0])

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
                    patch.object(br, "git_pin", side_effect=lambda commit: OLD_PIN if commit == TESTED else PIN), \
                    patch.dict(br.os.environ, {"GITHUB_OUTPUT": str(output),
                                               "GITHUB_STEP_SUMMARY": str(summary)}), \
                    patch("sys.argv", ["bump_report.py"]):
                br.main()
            self.assertEqual(output.read_text(), f"commit={FKB}\nawaiting_revalidation=true\n")
            self.assertIn("creates no incompatibility issue or fix PR", summary.read_text())

    def test_forward_boundary_does_not_fetch_run_metadata(self):
        boundary = {"downstreams": {"TauCeti": {
            "repo": "TauCetiProject/TauCeti", "first_known_bad_commit": FKB}}}
        manifest = json.dumps({"packages": [{"name": "mathlib", "rev": PIN}]})
        with patch.object(br, "fetch_snapshot", return_value=boundary) as fetch, \
                patch.object(br.Path, "read_text", return_value=manifest), \
                patch.object(br, "gh_api", return_value={"status": "behind"}), \
                patch.dict(br.os.environ, {"GITHUB_OUTPUT": "", "GITHUB_STEP_SUMMARY": ""}), \
                patch("sys.argv", ["bump_report.py"]):
            br.main()
        fetch.assert_called_once_with("lkg")

    def test_absent_runs_entry_waits_without_losing_the_boundary(self):
        boundary = {"downstreams": {"TauCeti": {
            "repo": "TauCetiProject/TauCeti", "first_known_bad_commit": FKB}}}
        manifest = json.dumps({"packages": [{"name": "mathlib", "rev": PIN}]})
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "output"
            with patch.object(br, "fetch_snapshot", side_effect=[boundary, {"downstreams": {}}]), \
                    patch.object(br.Path, "read_text", return_value=manifest), \
                    patch.object(br, "gh_api", return_value={"status": "ahead"}), \
                    patch.dict(br.os.environ, {"GITHUB_OUTPUT": str(output), "GITHUB_STEP_SUMMARY": ""}), \
                    patch("sys.argv", ["bump_report.py"]):
                br.main()
            self.assertEqual(output.read_text(), f"commit={FKB}\nawaiting_revalidation=true\n")


class GitHistoryTests(unittest.TestCase):
    def test_missing_api_commits_are_no_evidence_not_a_crash(self):
        previous = Path.cwd()
        with tempfile.TemporaryDirectory() as directory:
            try:
                os.chdir(directory)
                subprocess.run(["git", "init", "-q"], check=True)
                subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.com",
                                "commit", "--allow-empty", "-qm", "initial"], check=True)
                self.assertFalse(br.git_ancestor(TESTED, "HEAD"))
                self.assertFalse(br.git_ancestor("HEAD", GREEN))
                self.assertIsNone(br.git_pin(TESTED))
                self.assertTrue(br.git_ancestor("HEAD", "HEAD"))
            finally:
                os.chdir(previous)


if __name__ == "__main__":
    unittest.main()
