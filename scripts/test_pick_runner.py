"""Exercise this project's picker consumers and immutable recovery identity.

Kept here because nightly source verification uses dedicated capacity, while its
reference job and PR builds still consume the shared picker.
"""

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

import yaml

ROOT = Path(os.environ.get("TAUCETI_PROJECT_ROOT", Path(__file__).resolve().parents[1]))
PICKER = yaml.safe_load((ROOT / ".github/workflows/pick-runner.yml").read_text())
BUILD = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())
MODERN = any(step.get("run") == "python3 scripts/fleet_runner.py --route"
             for job in PICKER["jobs"].values() for step in job.get("steps", []))


def expression(source, *, attempt=1, picker_attempt="1", target='"ubuntu-24.04"', event="pull_request_target", action="opened", staging=False, maintenance=False, author_type="User", head_repo="TauCetiProject/TauCeti", head_ref="feature", hosted_picker=False, labels=(), label="unrelated", hosted_slot="0", staging_target=""):
    """Evaluate the actual YAML expression's boolean/format/JSON subset."""
    source = source.removeprefix("${{").removesuffix("}}").strip()
    source = source.replace("\n", " ").replace("&&", " and ").replace("||", " or ")
    source = source.replace("!contains", "not contains").replace("!(", "not (").replace(".labels.*.name", ".label_names")
    github = SimpleNamespace(repository="TauCetiProject/TauCeti", run_attempt=attempt, run_id=42, event_name=event, event=SimpleNamespace(
        action=action, label=SimpleNamespace(name=label), pull_request=SimpleNamespace(number=7, label_names=labels, user=SimpleNamespace(type=author_type),
            head=SimpleNamespace(sha="a" * 40, ref=head_ref, repo=SimpleNamespace(full_name=head_repo))),
        client_payload=SimpleNamespace(pr=7, head_sha="a" * 40, base_sha="b" * 40, base_ref="main", batch_id=12),
        merge_group=SimpleNamespace(head_sha="c" * 40)))
    needs = SimpleNamespace(picker=SimpleNamespace(outputs=SimpleNamespace(attempt=picker_attempt, runner=target, hosted_slot=hosted_slot)))
    source = source.replace("needs.pick-runner", "needs.picker").replace("inputs.fleet-staging", "inputs.staging").replace("outputs.hosted-slot", "outputs.hosted_slot")
    return eval(source, {"__builtins__": {}, "github": github, "needs": needs,
                         "inputs": SimpleNamespace(pr="7", staging=staging, maintenance=maintenance), "fromJSON": json.loads,
                         "contains": lambda values, value: value in values, "format": lambda s, *args: s.format(*args), "startsWith": lambda s, p: s.startswith(p),
                         "vars": SimpleNamespace(PICKER_GITHUB_FALLBACK="true" if hosted_picker else "", STAGING_RUNS_ON=staging_target)})


@unittest.skipUnless(MODERN, "project uses the standard GitHub-only picker")
class PickerWorkflow(unittest.TestCase):
    def test_hosted_bulk_jobs_share_exactly_nineteen_native_slots(self):
        for name, job, picker in (("pr-build.yml", "sandboxed-build", "pick-runner"),
                                 ("nightly-verify.yml", "reference", "pick-reference-runner")):
            workflow = yaml.safe_load((ROOT / ".github/workflows" / name).read_text())
            concurrency = workflow["jobs"][job]["concurrency"]
            group = concurrency["group"].replace("needs." + picker, "needs.pick-runner")
            self.assertEqual({expression(group, hosted_slot=str(i)) for i in range(19)},
                             {"tauceti-hosted-bulk-" + str(i) for i in range(19)})
            self.assertEqual(expression(group, picker_attempt="", target="", hosted_slot=""), "tauceti-hosted-bulk-0")
            for target in (["nscloud-ubuntu-24.04-amd64-8x16-with-features"],
                           dict(group="TauCetiFleet", labels=["self-hosted", "tauceti-fleet-pr"])):
                self.assertFalse(expression(group, target=json.dumps(target)).startswith("tauceti-hosted-bulk-"))
                # A stale picker falls back to GitHub, so it must regain the cap.
                self.assertEqual(expression(group, target=json.dumps(target), attempt=2), "tauceti-hosted-bulk-0")
            self.assertEqual(concurrency["queue"], "max")
            self.assertFalse(concurrency["cancel-in-progress"])

    def test_priority_overrides_do_not_wait_for_hosted_bulk_slots(self):
        group = BUILD["jobs"]["sandboxed-build"]["concurrency"]["group"]
        self.assertFalse(expression(group, maintenance=True).startswith("tauceti-hosted-bulk-"))
        self.assertFalse(expression(group, author_type="Bot", head_ref="bump-mathlib/abc").startswith("tauceti-hosted-bulk-"))
        self.assertFalse(expression(group, event="repository_dispatch", action="tauceti-bors-staging",
                                    staging_target='["nscloud-ubuntu-24.04-amd64-16x32-with-features"]')
                         .startswith("tauceti-hosted-bulk-"))

    def test_slot_calculation_never_creates_an_extra_group(self):
        step = next(s for s in PICKER["jobs"]["pick"]["steps"] if s.get("id") == "hosted-slot")
        with tempfile.TemporaryDirectory() as root:
            for run_id in [*range(19), 42533533021, 999999999999999]:
                output = Path(root) / "output"
                output.unlink(missing_ok=True)
                subprocess.run(["bash", "-e", "-c", step["run"]], check=True,
                               env=dict(os.environ, HOSTED_RUN_ID=str(run_id), GITHUB_OUTPUT=str(output)))
                self.assertEqual(output.read_text(), "slot=" + str(run_id % 19) + "\n")

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

    def test_label_events_only_route_self_tested_prs(self):
        condition = BUILD["jobs"]["pick-runner"]["if"]
        for action in ("labeled", "unlabeled"):
            self.assertFalse(expression(condition, action=action))
            self.assertTrue(expression(condition, action=action, label="self-tested"))
            self.assertFalse(expression(condition, action=action, labels=("self-tested",)))
            self.assertFalse(expression(condition, action=action, label="full-lint"))
            for label in ("full-lint", "lint-repair"):
                self.assertTrue(expression(condition, action=action, label=label, labels=("self-tested",)))
            self.assertEqual(expression(BUILD["run-name"], action=action), "Ignored label event 42")
        self.assertTrue(expression(condition))

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
        token = next(s for s in pick["steps"] if "create-github-app-token" in s.get("uses", ""))
        self.assertTrue(token["continue-on-error"])
        self.assertIn("inputs.pr-number > 0", token["if"])
        self.assertIn("'self-tested'", token["if"])
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
