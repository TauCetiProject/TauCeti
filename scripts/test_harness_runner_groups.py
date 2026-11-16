"""The TauCetiTools harness pin has one source, and the runner groups follow it.

`.tauceti/ci-source.json` `harness_revision` is the only source of the TauCetiTools revision
that PR CI and source staging run. harness-runner-groups.yml derives the runner-group
allow-lists from it and reports a PR status that is green only once they admit the PR's pin.

Run with: python3 scripts/test_harness_runner_groups.py
"""

import json
import pathlib
import re
import unittest

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOWS = ROOT / ".github/workflows"
WORKFLOW = WORKFLOWS / "harness-runner-groups.yml"
HARNESS = "TauCetiProject/TauCetiTools"
# Workflows whose TauCetiTools literals are bound to the harness pin. Callers of a TauCetiTools
# reusable workflow are bound automatically by the shared check.
BOUND = ("pr-build.yml", "source-candidate.yml")
CONTEXT = "harness-runner-groups"


def source():
    value = json.loads((ROOT / ".tauceti/ci-source.json").read_text())
    return value["harness"]["name"], value["harness_revision"]


def literals(text):
    pinned = re.findall(rf"{re.escape(HARNESS)}/\.github/(?:actions|workflows)/[^@\s]+@([0-9A-Za-z._/-]+)", text)
    refs = re.findall(r"^\s*tools[-_]ref:\s*['\"]?([0-9A-Za-z._/-]+)", text, re.MULTILINE)
    return pinned + refs


def document():
    return yaml.safe_load(WORKFLOW.read_text())


class OneHarnessPin(unittest.TestCase):
    def test_bound_literals_follow_ci_source(self):
        repository, revision = source()
        self.assertEqual(repository, HARNESS)
        self.assertRegex(revision, r"^[0-9a-f]{40}$")
        for name in BOUND:
            with self.subTest(workflow=name):
                found = literals((WORKFLOWS / name).read_text())
                self.assertTrue(found, f"{name} has no harness literal")
                self.assertEqual(set(found), {revision}, f"{name} differs from .tauceti/ci-source.json")

    def test_every_reusable_harness_caller_is_bound(self):
        for path in WORKFLOWS.glob("*.yml"):
            jobs = yaml.safe_load(path.read_text()).get("jobs") or {}
            calls = [j for j in jobs.values() if str(j.get("uses", "")).startswith(HARNESS + "/.github/workflows/")]
            if calls:
                self.assertIn(path.name, BOUND)

    def test_reconciler_binds_the_same_workflows(self):
        runs = [s["run"] for job in document()["jobs"].values() for s in job["steps"] if "harness_pins" in s.get("run", "")]
        self.assertEqual(len(runs), 3)
        for run in runs:
            bound = re.findall(r"--bound-workflow (\S+)", run)
            # Callers (source-candidate.yml) are bound by the tool itself.
            self.assertEqual(set(bound) | {"source-candidate.yml"}, set(BOUND))


class RunnerGroupReconciler(unittest.TestCase):
    def test_status_context(self):
        self.assertEqual(document()["env"]["CONTEXT"], CONTEXT)

    def test_triggers(self):
        on = document().get("on", document().get(True))
        self.assertEqual(on["pull_request_target"]["types"], ["opened", "synchronize", "reopened"])
        self.assertEqual(on["repository_dispatch"]["types"], ["tauceti-bors-pr-approved"])
        self.assertEqual(on["push"]["branches"], ["main"])
        self.assertIn(".tauceti/ci-source.json", on["push"]["paths"])
        self.assertIn(".github/workflows/**", on["push"]["paths"])
        self.assertIn("schedule", on)

    def test_pr_contents_are_never_checked_out_and_only_admission_holds_the_credential(self):
        jobs = document()["jobs"]
        for name, job in jobs.items():
            for step in job["steps"]:
                if str(step.get("uses", "")).startswith("actions/checkout@"):
                    with self.subTest(job=name):
                        self.assertEqual(step["with"]["repository"], HARNESS)
                        self.assertEqual(step["with"]["ref"], "${{ env.TOOLS_REF }}")
                        self.assertIs(step["with"]["persist-credentials"], False)
        self.assertNotIn("secrets.", json.dumps(jobs["pull-request"]))
        self.assertNotIn("environment", jobs["pull-request"])
        self.assertEqual(jobs["admit"]["if"], "needs.pull-request.outputs.changed == 'true'")
        for name in ("admit", "main"):
            self.assertEqual(jobs[name]["environment"], "runner-policy")
        self.assertRegex(document()["env"]["TOOLS_REF"], r"^[0-9a-f]{40}$")

    def test_every_pr_path_reports_a_status(self):
        jobs = document()["jobs"]
        for name in ("pull-request", "admit"):
            report = jobs[name]["steps"][-1]
            self.assertEqual(report["if"], "always()")
            self.assertIn("statuses/$HEAD_SHA", report["run"])
            self.assertIn("'error'", report["env"]["STATE"])


if __name__ == "__main__":
    unittest.main()
