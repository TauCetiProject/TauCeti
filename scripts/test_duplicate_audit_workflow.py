#!/usr/bin/env python3
"""Keep parallel audit fixtures mandatory before main's cache can be published."""

from pathlib import Path
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[1]
JOBS = yaml.safe_load((ROOT / ".github/workflows/ci.yml").read_text())["jobs"]


class DuplicateAuditWorkflowTest(unittest.TestCase):
    def test_fixtures_run_independently_and_fail_closed(self):
        job = JOBS["duplicate-audit-tests"]
        for key in ("needs", "if", "continue-on-error"):
            self.assertNotIn(key, job)
        for step in job["steps"]:
            self.assertNotIn("if", step)
            self.assertNotIn("continue-on-error", step)
        commands = [step.get("run", "") for step in job["steps"]]
        fixture_command = next(c for c in commands if "test_duplicate_declarations.py" in c)
        self.assertIn('LEAN="$(elan which lean)"', fixture_command)
        self.assertIn('LEAN_SYSROOT="$("$LEAN" --print-prefix)"', fixture_command)
        self.assertIn("export LEAN LEAN_SYSROOT", fixture_command)
        self.assertTrue(any('elan toolchain install "$(cat lean-toolchain)"' in c
                            for c in commands))
        # ElanPin tests separately verify every install's release and checksum.
        checkout = next(step for step in job["steps"] if "uses" in step)
        self.assertIs(checkout["with"]["persist-credentials"], False)

    def test_publication_requires_both_jobs_to_succeed(self):
        publisher = JOBS["publish-lake-cache"]
        self.assertEqual(set(publisher["needs"]), {"build", "duplicate-audit-tests"})
        # Require a conjunction of positive success checks, without an OR or a status
        # override that could publish after a failed, skipped, or cancelled prerequisite.
        expression = publisher["if"].removeprefix("${{").removesuffix("}}")
        self.assertEqual({term.strip() for term in expression.split("&&")}, {
            "needs.build.result == 'success'",
            "needs['duplicate-audit-tests'].result == 'success'",
            "needs.build.outputs.staged == 'true'",
        })
        self.assertNotIn("continue-on-error", publisher)

    def test_real_library_audit_stays_in_the_build(self):
        steps = JOBS["build"]["steps"]
        audit = next(step for step in steps
                     if step.get("run") == "lake env lean --run scripts/DuplicateDeclarations.lean")
        self.assertNotIn("if", audit)
        self.assertNotIn("continue-on-error", audit)
        self.assertFalse(any("test_duplicate_declarations.py" in step.get("run", "")
                             for step in steps))


if __name__ == "__main__":
    unittest.main()
