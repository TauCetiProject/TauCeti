"""Exercise this project's picker consumers and immutable recovery identity.

Kept here because nightly source verification uses dedicated capacity, while its
reference job and PR builds still consume the shared picker.
"""

import json
import os
import unittest
from pathlib import Path
from types import SimpleNamespace

import yaml

ROOT = Path(os.environ.get("TAUCETI_PROJECT_ROOT", Path(__file__).resolve().parents[1]))
PICKER = yaml.safe_load((ROOT / ".github/workflows/pick-runner.yml").read_text())
BUILD = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())
MODERN = any(step.get("run") == "python3 scripts/fleet_runner.py --route"
             for job in PICKER["jobs"].values() for step in job.get("steps", []))


def expression(source, *, attempt=1, picker_attempt="1", target='"ubuntu-24.04"', event="pull_request_target", action="opened", staging=False, maintenance=False, author_type="User", head_repo="TauCetiProject/TauCeti", head_ref="feature", hosted_picker=False):
    """Evaluate the actual YAML expression's boolean/format/JSON subset."""
    source = source.removeprefix("${{").removesuffix("}}").strip()
    source = source.replace("\n", " ").replace("&&", " and ").replace("||", " or ")
    github = SimpleNamespace(repository="TauCetiProject/TauCeti", run_attempt=attempt, run_id=42, event_name=event, event=SimpleNamespace(
        action=action, pull_request=SimpleNamespace(number=7, user=SimpleNamespace(type=author_type),
            head=SimpleNamespace(sha="a" * 40, ref=head_ref, repo=SimpleNamespace(full_name=head_repo))),
        client_payload=SimpleNamespace(pr=7, head_sha="a" * 40, base_sha="b" * 40, base_ref="main", batch_id=12),
        merge_group=SimpleNamespace(head_sha="c" * 40)))
    needs = SimpleNamespace(picker=SimpleNamespace(outputs=SimpleNamespace(attempt=picker_attempt, runner=target)))
    source = source.replace("needs.pick-runner", "needs.picker").replace("inputs.fleet-staging", "inputs.staging")
    return eval(source, {"__builtins__": {}, "github": github, "needs": needs,
                         "inputs": SimpleNamespace(pr="7", staging=staging, maintenance=maintenance), "fromJSON": json.loads,
                         "format": lambda s, *args: s.format(*args), "startsWith": lambda s, p: s.startswith(p),
                         "vars": SimpleNamespace(PICKER_GITHUB_FALLBACK="true" if hosted_picker else "")})


@unittest.skipUnless(MODERN, "project uses the standard GitHub-only picker")
class PickerWorkflow(unittest.TestCase):
    def test_exact_target_is_used_for_this_attempt_only(self):
        source = BUILD["jobs"]["sandboxed-build"]["runs-on"]
        target = dict(group="TauCetiFleet", labels=["self-hosted", "tauceti-fleet-pr", "fleet-" + "a" * 32, "fleet-instance-" + "b" * 16])
        self.assertEqual(expression(source, target=json.dumps(target)), target)
        self.assertEqual(expression(source, attempt=2, picker_attempt="2", target=json.dumps(target)), target)
        self.assertEqual(expression(source, attempt=2, target=json.dumps(target)), "ubuntu-24.04")
        self.assertEqual(expression(source, picker_attempt="", target=""), "ubuntu-24.04")

    def test_namespace_target_and_fallback_obey_the_same_attempt_fence(self):
        target = ["nscloud-ubuntu-24.04-amd64-16x32-with-features;job.priority=1", "namespace-features:container.privileged=true;github.run-id=42"]
        for name, job, picker in [
            ("pr-build.yml", "sandboxed-build", "pick-runner"),
            ("nightly-verify.yml", "reference", "pick-reference-runner"),
        ]:
            workflow = yaml.safe_load((ROOT / ".github/workflows" / name).read_text())
            source = workflow["jobs"][job]["runs-on"].replace("needs." + picker, "needs.pick-runner")
            self.assertEqual(expression(source, target=json.dumps(target)), target)
            self.assertEqual(expression(source, target=json.dumps(target), attempt=2), "ubuntu-24.04")

    def test_maintenance_build_capacity_is_limited_to_explicit_or_same_repo_bot_work(self):
        source = BUILD["jobs"]["sandboxed-build"]["runs-on"]
        priority_build = [
            "nscloud-ubuntu-24.04-amd64-8x16-with-features;job.priority=1",
            "namespace-features:container.privileged=true;github.run-id=42",
        ]
        self.assertEqual(expression(source, maintenance=True), priority_build)
        for branch in ("bump-mathlib/abc", "lint-repair/main"):
            self.assertEqual(expression(source, author_type="Bot", head_ref=branch), priority_build)
            self.assertEqual(expression(source, head_ref=branch), "ubuntu-24.04")
            self.assertEqual(expression(source, author_type="Bot", head_ref=branch,
                                        head_repo="someone/fork"), "ubuntu-24.04")

    def test_pr_title_contains_immutable_head_and_bors_title_is_unchanged(self):
        self.assertEqual(expression(BUILD["run-name"]), "pr-build pr=7 head=" + "a" * 40)
        self.assertEqual(expression(BUILD["run-name"], event="repository_dispatch", action="tauceti-bors-pr-approved"), "pr-build pr=7 head=" + "a" * 40)
        self.assertEqual(expression(BUILD["run-name"], event="repository_dispatch", action="tauceti-bors-staging"), "bors branch=main batch=12 head=" + "a" * 40 + " base=" + "b" * 40)

    def test_maintenance_build_keeps_its_explicit_namespace_runner(self):
        source = BUILD["jobs"]["sandboxed-build"]["runs-on"]
        expected = ["nscloud-ubuntu-24.04-amd64-8x16-with-features;job.priority=1",
                    "namespace-features:container.privileged=true;github.run-id=42"]
        self.assertEqual(expression(source, maintenance=True), expected)
        self.assertEqual(expression(source, maintenance=True, hosted_picker=True, attempt=2), expected)

    def test_picker_is_small_control_job_and_calls_the_existing_selector(self):
        pick = PICKER["jobs"]["pick"]
        priority_control = [
            "nscloud-ubuntu-24.04-amd64-2x4-with-features;job.priority=0",
            "namespace-features:github.run-id=42",
        ]
        self.assertEqual(expression(pick["runs-on"]), priority_control)
        self.assertEqual(expression(pick["runs-on"], hosted_picker=True), "ubuntu-24.04")
        self.assertEqual(expression(pick["runs-on"], staging=True), priority_control)
        self.assertEqual(expression(pick["runs-on"], maintenance=True), priority_control)
        self.assertFalse(any("create-github-app-token" in step.get("uses", "") for step in pick["steps"]))
        self.assertTrue(pick["continue-on-error"])
        step = next(s for s in pick["steps"] if s.get("id") == "pick")
        self.assertEqual(step["run"], "python3 scripts/fleet_runner.py --route")
        self.assertEqual(step["env"]["NAMESPACE_BUILD_CAP"], "${{ vars.NAMESPACE_BUILD_CAP }}")
        self.assertEqual(step["env"]["GH_TOKEN"], "${{ github.token }}")
        self.assertIn("'250'", step["env"]["API_RESERVE"])
        self.assertNotIn("FALLBACK_TOKEN", step["env"])
        self.assertNotIn("REPOSITORY_API_RESERVE", step["env"])


if __name__ == "__main__":
    unittest.main()
