#!/usr/bin/env python3
"""Audit fixtures are independent of library verification and cache publication."""
from pathlib import Path
import unittest
import yaml

ROOT = Path(__file__).resolve().parents[1]
JOBS = yaml.safe_load((ROOT / ".github/workflows/ci.yml").read_text())["jobs"]
INFRA = yaml.safe_load((ROOT / ".github/workflows/infrastructure-tests.yml").read_text())["jobs"]


class DuplicateAuditWorkflowTest(unittest.TestCase):
    def test_fixtures_run_in_the_infrastructure_workflow(self):
        job = INFRA["lean-fixtures"]
        commands = [step.get("run", "") for step in job["steps"]]
        fixture = next(c for c in commands if "test_duplicate_declarations.py" in c)
        self.assertIn('LEAN="$(elan which lean)"', fixture)
        self.assertIn('LEAN_SYSROOT="$("$LEAN" --print-prefix)"', fixture)
        self.assertIn("export LEAN LEAN_SYSROOT", fixture)
        self.assertNotIn("duplicate-audit-tests", JOBS)

    def test_publication_depends_only_on_the_content_build(self):
        publisher = JOBS["publish-lake-cache"]
        self.assertEqual(publisher["needs"], ["build"])
        expression = publisher["if"].removeprefix("${{").removesuffix("}}")
        self.assertEqual({term.strip() for term in expression.split("&&")}, {
            "needs.build.result == 'success'",
            "needs.build.outputs.staged == 'true'",
        })
        self.assertNotIn("continue-on-error", publisher)

    def test_real_library_audit_stays_in_the_build(self):
        steps = JOBS["build"]["steps"]
        audit = next(step for step in steps
                     if 'lake env "$RUNNER_TEMP/audit-driver/audit-driver"' in step.get("run", ""))
        self.assertNotIn("if", audit)
        self.assertNotIn("continue-on-error", audit)
        flags = next(step for step in steps if step.get("run") == "lake exe module-system")
        self.assertNotIn("if", flags)
        self.assertNotIn("continue-on-error", flags)


if __name__ == "__main__":
    unittest.main()
