"""Exercise the actual runner-picker shell and batch runner expressions offline.

Run with: python3 scripts/test_pick_runner.py
"""

import json
import os
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[1]
PICKER = yaml.safe_load((ROOT / ".github/workflows/pick-runner.yml").read_text())
BUILD = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())
NS = "nscloud-ubuntu-24.04-amd64-8x16-with-features"

# Use real jq to exercise the workflow's filters, including pagination and errors.
FAKE_GH = r'''#!/usr/bin/env python3
import json, os, subprocess, sys
args = sys.argv[1:]
path = next(a for a in args[1:] if not a.startswith('-'))
token = os.environ['GH_TOKEN']
with open(os.environ['CALLS'], 'a') as f:
    f.write(('repository:' if token == 'repository-token' else '') + path + '\n')
fixture = json.load(open(os.environ['FIXTURE']))
pages = fixture.get(token + ':' + path, fixture.get(path))
if pages is None:
    print('API read failed: ' + path, file=sys.stderr)
    sys.exit(1)
if '--paginate' not in args:
    pages = pages[:1]
query = args[args.index('--jq') + 1]
for page in pages:
    if page is None:
        sys.exit(1)
    result = subprocess.run(['jq', '-r', query], input=json.dumps(page), text=True)
    if result.returncode:
        sys.exit(result.returncode)
'''


def job(provider="github", status="in_progress"):
    labels = [NS] if provider == "namespace" else ["ubuntu-latest"]
    if provider == "self-hosted":
        labels = ["self-hosted", "linux"]
    return dict(status=status, labels=labels)


class PickerTests(unittest.TestCase):
    def fixture(self, busy=2):
        return {
            "orgs/Test/repos?per_page=100": [[dict(name="code", archived=False)]],
            "repos/Test/code/actions/runs?status=in_progress&per_page=100": [
                dict(total_count=1, workflow_runs=[dict(id=1)])],
            "repos/Test/code/actions/runs/1/jobs?per_page=100": [
                dict(total_count=busy, jobs=[job() for _ in range(busy)])],
            "rate_limit": [dict(resources=dict(core=dict(remaining=5000)))],
        }

    def pick(self, fixture, budget="18", app_token="installation-token", fallback_token="repository-token", repository_reserve=None):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            (directory / "gh").write_text(FAKE_GH)
            (directory / "gh").chmod(0o755)
            (directory / "fixture.json").write_text(json.dumps(fixture))
            output, summary, calls = (directory / name for name in ["output", "summary", "calls"])
            step = next(s for s in PICKER["jobs"]["pick"]["steps"] if s.get("id") == "pick")
            variables = SimpleNamespace(PICKER_API_RESERVE="",
                                        PICKER_REPOSITORY_API_RESERVE=repository_reserve or "")
            selected_reserve = expression(step["env"]["API_RESERVE"], "", "", "", app_token,
                                          variables=variables)
            selected_repository_reserve = expression(step["env"]["REPOSITORY_API_RESERVE"],
                                                    "", "", "", app_token, variables=variables)
            env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}",
                   "ORG": "Test", "BUDGET": budget, "GITHUB_OUTPUT": str(output),
                   "GITHUB_STEP_SUMMARY": str(summary), "CALLS": str(calls),
                   "FIXTURE": str(directory / "fixture.json"),
                   "API_RESERVE": selected_reserve, "FALLBACK_TOKEN": fallback_token,
                   "REPOSITORY_API_RESERVE": selected_repository_reserve,
                   "GH_TOKEN": app_token or "repository-token"}
            step = next(s for s in PICKER["jobs"]["pick"]["steps"] if s.get("id") == "pick")
            result = subprocess.run(["bash", "-c", step["run"]], env=env,
                                    text=True, capture_output=True, timeout=20)
            self.assertEqual(result.returncode, 0, result.stderr)
            return (dict(line.split("=", 1) for line in output.read_text().splitlines()),
                    summary.read_text(), calls.read_text().splitlines() if calls.exists() else [])

    def test_namespace_backlog_does_not_spill_idle_github_capacity(self):
        fixture = self.fixture()
        # The picker completed on GitHub; these runs now wait for Namespace.
        fixture["repos/Test/code/actions/runs?status=queued&per_page=100"] = [
            dict(total_count=200, workflow_runs=[dict(id=n) for n in range(2, 202)])]
        fixture["repos/Test/code/actions/runs/1/jobs?per_page=100"][0]["jobs"] += [
            job("namespace") for _ in range(8)] + [job("namespace", "queued") for _ in range(64)]
        output, _, calls = self.pick(fixture)
        self.assertEqual(output, dict(github="true", budget="18", busy="2"))
        self.assertFalse(any("status=queued" in path for path in calls))

    def test_budget_boundary_counts_picker_slot(self):
        for busy, expected in [(17, "true"), (18, "true"), (19, "false"), (20, "false")]:
            with self.subTest(busy=busy):
                output, _, _ = self.pick(self.fixture(busy))
                self.assertEqual(output["github"], expected)
                self.assertEqual(output["busy"], str(busy))

    def test_only_running_hosted_jobs_consume_capacity(self):
        fixture = self.fixture()
        fixture["repos/Test/code/actions/runs/1/jobs?per_page=100"][0]["jobs"] += [
            job(status="queued"), job(status="completed"), job("namespace"), job("self-hosted")]
        output, _, _ = self.pick(fixture)
        self.assertEqual(output["busy"], "2")
        self.assertEqual(output["github"], "true")

    def test_counts_all_repositories_and_pages(self):
        fixture = self.fixture(1)
        fixture["orgs/Test/repos?per_page=100"] += [[dict(name="review", archived=False)]]
        fixture["repos/Test/review/actions/runs?status=in_progress&per_page=100"] = [
            dict(total_count=101, workflow_runs=[dict(id=n) for n in range(2, 102)]),
            dict(total_count=101, workflow_runs=[dict(id=102)])]
        for n in range(2, 103):
            fixture[f"repos/Test/review/actions/runs/{n}/jobs?per_page=100"] = [
                dict(total_count=1, jobs=[job("namespace")])]
        # Second page holds running GitHub jobs, after 100 completed jobs.
        fixture["repos/Test/review/actions/runs/102/jobs?per_page=100"] = [
            dict(total_count=118, jobs=[job(status="completed") for _ in range(100)]),
            dict(total_count=118, jobs=[job() for _ in range(18)])]
        output, _, calls = self.pick(fixture)
        self.assertEqual(output["busy"], "19")
        self.assertEqual(output["github"], "false")
        self.assertIn("repos/Test/review/actions/runs/102/jobs?per_page=100", calls)

    def test_incomplete_reads_fall_back_instead_of_undercounting(self):
        for path in ["orgs/Test/repos?per_page=100",
                     "repos/Test/code/actions/runs?status=in_progress&per_page=100",
                     "repos/Test/code/actions/runs/1/jobs?per_page=100"]:
            with self.subTest(path=path):
                fixture = self.fixture()
                fixture[path].append(None)  # A later page fails after partial output.
                output, summary, _ = self.pick(fixture)
                self.assertEqual(output["github"], "false")
                self.assertIn("Could not", summary)

    def test_low_quota_preserves_budget_without_per_run_reads(self):
        for remaining in [0, 1000, 1500]:
            with self.subTest(remaining=remaining):
                fixture = self.fixture()
                fixture["rate_limit"][0]["resources"]["core"]["remaining"] = remaining
                fixture["repository-token:rate_limit"] = [
                    dict(resources=dict(core=dict(remaining=250)))]
                output, summary, calls = self.pick(fixture)
                self.assertEqual(output["github"], "false")
                self.assertIn("quota reserve", summary)
                self.assertEqual(calls, ["rate_limit", "repository:rate_limit"])

    def test_private_github_token_uses_its_separate_1000_request_budget(self):
        fixture = self.fixture()
        fixture["rate_limit"][0]["resources"]["core"]["remaining"] = 1000
        output, _, _ = self.pick(fixture, app_token="")
        self.assertEqual(output["github"], "true")
        self.assertEqual(output["busy"], "2")

    def test_shared_reserve_uses_repository_budget_and_still_checks_capacity(self):
        for busy, expected in [(2, "true"), (18, "true"), (19, "false")]:
            with self.subTest(busy=busy):
                fixture = self.fixture(busy)
                fixture["rate_limit"][0]["resources"]["core"]["remaining"] = 1500
                fixture["repository-token:rate_limit"] = [
                    dict(resources=dict(core=dict(remaining=1000)))]
                output, summary, calls = self.pick(fixture, fallback_token="repository-token")
                self.assertEqual(output["github"], expected)
                self.assertEqual(output["busy"], str(busy))
                self.assertIn("Shared App quota reserve protected", summary)
                self.assertEqual(calls[0], "rate_limit")
                self.assertTrue(all(path.startswith("repository:") for path in calls[1:]))

    def test_repository_fallback_can_happen_before_parallel_job_reads(self):
        fixture = self.fixture()
        fixture["rate_limit"][0]["resources"]["core"]["remaining"] = 1501
        fixture["repository-token:rate_limit"] = [dict(resources=dict(core=dict(remaining=1000)))]
        output, _, calls = self.pick(fixture, fallback_token="repository-token")
        self.assertEqual(output["github"], "true")
        job_calls = [path for path in calls if "/jobs?" in path]
        self.assertTrue(job_calls)
        self.assertTrue(all(path.startswith("repository:") for path in job_calls))

    def test_exhausted_or_unreadable_repository_budget_falls_back_to_namespace(self):
        for remaining in [0, 250, None]:
            with self.subTest(remaining=remaining):
                fixture = self.fixture()
                fixture["rate_limit"][0]["resources"]["core"]["remaining"] = 1500
                fixture["repository-token:rate_limit"] = [
                    dict(resources=dict(core=dict(remaining=remaining)))]
                output, _, calls = self.pick(fixture, fallback_token="repository-token")
                self.assertEqual(output["github"], "false")
                self.assertEqual(calls, ["rate_limit", "repository:rate_limit"])

    def test_projected_job_reads_preserve_reserve(self):
        fixture = self.fixture()
        fixture["rate_limit"][0]["resources"]["core"]["remaining"] = 1501
        fixture["repository-token:rate_limit"] = [
            dict(resources=dict(core=dict(remaining=251)))]
        output, summary, calls = self.pick(fixture)
        self.assertEqual(output["github"], "false")
        self.assertIn("inspection would consume", summary)
        self.assertFalse(any("/jobs?" in path for path in calls))

    def test_no_app_preserves_repository_budget_without_switching(self):
        for remaining in [0, 250, 251]:
            with self.subTest(remaining=remaining):
                fixture = self.fixture()
                fixture["rate_limit"][0]["resources"]["core"]["remaining"] = remaining
                output, summary, calls = self.pick(fixture, app_token="")
                self.assertEqual(output["github"], "false")
                self.assertNotIn("Shared App quota reserve protected", summary)
                self.assertFalse(any("/jobs?" in path for path in calls))

    def test_repository_reserve_is_configurable_and_identified_in_summary(self):
        fixture = self.fixture()
        fixture["rate_limit"][0]["resources"]["core"]["remaining"] = 1500
        fixture["repository-token:rate_limit"] = [
            dict(resources=dict(core=dict(remaining=500)))]
        output, summary, _ = self.pick(fixture, repository_reserve="400")
        self.assertEqual(output["github"], "true")
        self.assertIn("repository API requests left this hour (reserve 400)", summary)
        output, _, calls = self.pick(fixture, repository_reserve="500")
        self.assertEqual(output["github"], "false")
        self.assertEqual(calls, ["rate_limit", "repository:rate_limit"])

    def test_invalid_repository_reserve_avoids_api_reads(self):
        for value in ["bad", "9223372036854775807"]:
            output, summary, calls = self.pick({}, repository_reserve=value)
            self.assertEqual(output["github"], "false")
            self.assertIn("Invalid repository API reserve", summary)
            self.assertEqual(calls, [])

    def test_no_app_custom_reserve_uses_workflow_expression(self):
        fixture = self.fixture()
        fixture["rate_limit"][0]["resources"]["core"]["remaining"] = 400
        output, _, calls = self.pick(fixture, app_token="", repository_reserve="400")
        self.assertEqual(output["github"], "false")
        self.assertEqual(calls, ["repository:rate_limit"])

    def test_missing_fallback_token_preserves_installation_reserve(self):
        fixture = self.fixture()
        fixture["rate_limit"][0]["resources"]["core"]["remaining"] = 1500
        output, _, calls = self.pick(fixture, fallback_token="")
        self.assertEqual(output["github"], "false")
        self.assertEqual(calls, ["rate_limit"])

    def test_quota_read_failure_falls_back_before_org_scan(self):
        fixture = self.fixture()
        del fixture["rate_limit"]
        output, _, calls = self.pick(fixture)
        self.assertEqual(output["github"], "false")
        self.assertEqual(calls, ["rate_limit"])

    def test_namespace_profile_is_not_hosted_capacity(self):
        fixture = self.fixture()
        fixture["repos/Test/code/actions/runs/1/jobs?per_page=100"][0]["jobs"].append(
            dict(status="in_progress", labels=["namespace-profile-test"]))
        output, _, _ = self.pick(fixture)
        self.assertEqual(output["busy"], "2")

    def test_invalid_budget_falls_back(self):
        output, summary, calls = self.pick({}, budget="bad")
        self.assertEqual(output["github"], "false")
        self.assertIn("not a number", summary)
        self.assertEqual(calls, [])


def expression(value, event, action, picked, app_token="installation-token", variables=None):
    """Evaluate the actual workflow expression's boolean/format/JSON subset."""
    source = value.removeprefix("${{").removesuffix("}}").strip()
    source = source.replace("\n", " ").replace("&&", " and ").replace("||", " or ")
    github = SimpleNamespace(run_attempt=1, event_name=event, event=SimpleNamespace(action=action), run_id=42)
    needs = SimpleNamespace(**{"pick-runner": SimpleNamespace(outputs=SimpleNamespace(github=picked, fleet=""))})
    source = source.replace("needs.pick-runner", "needs.__dict__['pick-runner']")
    steps = SimpleNamespace(**{"app-token": SimpleNamespace(outputs=SimpleNamespace(token=app_token))})
    variables = variables or SimpleNamespace(PICKER_API_RESERVE="", PICKER_REPOSITORY_API_RESERVE="")
    variables.FLEET_CI_ENABLED = getattr(variables, "FLEET_CI_ENABLED", "")
    source = source.replace("steps.app-token", "steps.__dict__['app-token']")
    return eval(source, {"__builtins__": {}, "github": github, "needs": needs,
                         "steps": steps, "vars": variables, "fromJSON": json.loads, "format": lambda s, *args: s.format(*args)})


class BatchPriorityTests(unittest.TestCase):
    def test_bors_stays_on_namespace_and_has_priority_and_unique_assignment(self):
        jobs = BUILD["jobs"]
        for picked in ["true", "false", ""]:
            with self.subTest(picked=picked):
                labels = expression(jobs["sandboxed-build"]["runs-on"],
                                    "repository_dispatch", "tauceti-bors-staging", picked)
                self.assertEqual(labels, [NS + ";job.priority=1",
                    "namespace-features:container.privileged=true;github.run-id=42"])
                self.assertFalse(expression(jobs["pick-runner"]["if"],
                                            "repository_dispatch", "tauceti-bors-staging", picked))

    def test_pr_and_native_queue_routing_keeps_its_existing_policy(self):
        for event, action in [("pull_request_target", "opened"), ("workflow_dispatch", ""),
                              ("repository_dispatch", "tauceti-bors-pr-approved"),
                              ("merge_group", "checks_requested")]:
            for picked in ["true", "false", ""]:
                with self.subTest(event=event, picked=picked):
                    labels = expression(BUILD["jobs"]["sandboxed-build"]["runs-on"], event, action, picked)
                    if picked == "true" and event != "merge_group":
                        self.assertEqual(labels, "ubuntu-24.04")
                    else:
                        self.assertEqual(labels, [NS, "namespace-features:container.privileged=true"])


if __name__ == "__main__":
    unittest.main()
