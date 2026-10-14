"""Candidate supersession fixtures and the actual trusted workflow expressions."""

import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from types import SimpleNamespace
import unittest

import yaml

from bors_staging_identity import concurrency_group


ROOT = Path(__file__).resolve().parents[1]
ENTRY = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())
BUILD = yaml.safe_load((ROOT / ".github/workflows/pr-build-jobs.yml").read_text())
REPO = "TauCetiProject/TauCeti"


def payload():
    return dict(batch_id=12, base_ref="main", head_sha="a" * 40,
                base_sha="b" * 40)


def expression(value, *, event="repository_dispatch", action="tauceti-bors-staging",
               run=42, pr="", manual="", result="success", group="", caller=None):
    """Evaluate the boolean/format/JSON subset used by the workflow fixtures."""
    github = SimpleNamespace(
        event_name=event, run_id=run, repository=REPO,
        workflow_ref=caller or f"{REPO}/.github/workflows/pr-build.yml@refs/heads/main",
        event=SimpleNamespace(action=action, pull_request=SimpleNamespace(number=pr),
                              client_payload=SimpleNamespace(pr=pr),
                              merge_group=SimpleNamespace(head_sha="c" * 40)))
    needs = SimpleNamespace(identity=SimpleNamespace(
        result=result, outputs=SimpleNamespace(group=group)))
    inputs = SimpleNamespace(pr=manual)

    def evaluate(match):
        source = match[1].strip().replace("&&", " and ").replace("||", " or ")
        source = source.replace("needs.staging-identity", "needs.identity")
        source = re.sub(r"!(?!=)", " not ", source)
        return str(eval(source.strip(), {
            "__builtins__": {}, "github": github, "needs": needs, "inputs": inputs,
            "cancelled": lambda: False, "always": lambda: True,
            "format": lambda s, *args: s.format(*args), "fromJSON": json.loads,
            "startsWith": lambda s, prefix: s.lower().startswith(prefix.lower()),
            "contains": lambda values, value: value.lower() in [s.lower() for s in values],
        }))

    return re.sub(r"\$\{\{(.*?)\}\}", evaluate, value)


class IdentityTests(unittest.TestCase):
    def test_repeated_candidate_supersedes_even_with_changed_nonidentity_metadata(self):
        first = payload()
        second = dict(first, members=[dict(pr=1, head_sha="d" * 40)], extra="ignored")
        self.assertEqual(concurrency_group(REPO, first), concurrency_group(REPO, second))

    def test_different_candidates_and_bases_have_different_groups(self):
        first = payload()
        group = concurrency_group(REPO, first)
        for change in [dict(batch_id=13), dict(head_sha="c" * 40),
                       dict(base_sha="d" * 40), dict(base_ref="pilot"),
                       dict(base_ref="Main"), dict(base_ref="topic/subbranch")]:
            with self.subTest(change=change):
                self.assertNotEqual(group.lower(), concurrency_group(REPO, dict(first, **change)).lower())
        self.assertNotEqual(group, concurrency_group("Other/Repo", first))
        self.assertEqual(group, concurrency_group(REPO.lower(), first))
        self.assertRegex(group, r"^bors-staging-candidate-[0-9a-f]{64}$")

    def test_every_missing_field_fails_before_a_shared_group_exists(self):
        for field in payload():
            for missing in [None, "", False, [], {}]:
                with self.subTest(field=field, missing=missing), self.assertRaises(ValueError):
                    concurrency_group(REPO, dict(payload(), **{field: missing}))
            data = payload()
            del data[field]
            with self.assertRaises(ValueError):
                concurrency_group(REPO, data)
        for data in [None, [], ""]:
            with self.assertRaises(ValueError):
                concurrency_group(REPO, data)

    def test_malformed_identity_cannot_cancel_valid_candidate(self):
        for field, values in {
            "batch_id": [True, 0, -1, 12.0, "12", 2**63],
            "head_sha": ["A" * 40, "a" * 39, "a" * 41, "g" * 40, "a" * 40 + "\n"],
            "base_sha": [12, "not-a-sha"],
            "base_ref": ["bad:branch", "bad\nbranch", "bad\x00branch", "../main", "a..b", "a.lock"],
        }.items():
            for value in values:
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    concurrency_group(REPO, dict(payload(), **{field: value}))

    def test_cli_writes_only_validated_group(self):
        for data in [payload(), dict(payload(), batch_id=None)]:
            with tempfile.TemporaryDirectory() as directory:
                event, output = (Path(directory) / name for name in ["event.json", "output"])
                event.write_text(json.dumps(dict(action="tauceti-bors-staging", client_payload=data)))
                result = subprocess.run(["python3", str(ROOT / "scripts/bors_staging_identity.py")],
                    env={**os.environ, "GITHUB_EVENT_PATH": str(event),
                         "GITHUB_REPOSITORY": REPO, "GITHUB_OUTPUT": str(output)},
                    capture_output=True, text=True)
                if data["batch_id"]:
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(output.read_text(), f"group={concurrency_group(REPO, data)}\n")
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertFalse(output.exists())


class WorkflowTests(unittest.TestCase):
    def test_entrypoint_events_and_recovery_title_are_preserved(self):
        self.assertEqual(ENTRY[True]["repository_dispatch"]["types"],
                         ["tauceti-bors-staging", "tauceti-bors-pr-approved"])
        self.assertIn("bors branch={0} batch={1} head={2} base={3}", ENTRY["run-name"])
        self.assertEqual(set(BUILD[True]), {"workflow_call"})

    def test_workflow_level_staging_keys_are_run_specific(self):
        group = ENTRY["concurrency"]["group"]
        self.assertEqual(expression(group), "pr-build-bors-staging-run-42")
        self.assertNotEqual(expression(group), expression(group, run=43))
        self.assertIs(ENTRY["concurrency"]["cancel-in-progress"], True)

    def test_ordinary_pr_manual_approved_pr_and_native_merge_group_keys(self):
        group = ENTRY["concurrency"]["group"]
        for fields, expected in [
            (dict(event="pull_request_target", pr=123), "pr-build-123"),
            (dict(event="workflow_dispatch", manual="123"), "pr-build-123"),
            (dict(action="tauceti-bors-pr-approved", pr=123), "pr-build-123"),
            (dict(event="merge_group"), "pr-build-" + "c" * 40),
        ]:
            with self.subTest(fields=fields):
                self.assertEqual(expression(group, **fields), expected)
        candidate = concurrency_group(REPO, payload())
        self.assertNotEqual(expression(group, event="workflow_dispatch", manual=candidate), candidate)

    def test_validation_precedes_concurrency_for_the_whole_reusable_build(self):
        job = ENTRY["jobs"]["build-candidate"]
        self.assertEqual(job["needs"], "staging-identity")
        self.assertEqual(job["uses"], "./.github/workflows/pr-build-jobs.yml")
        self.assertIs(job["concurrency"]["cancel-in-progress"], True)
        group = concurrency_group(REPO, payload())
        self.assertEqual(expression(job["concurrency"]["group"], group=group), group)
        self.assertEqual(expression(job["if"]), "True")
        for result in ["failure", "skipped", "cancelled"]:
            self.assertEqual(expression(job["if"], result=result), "False")
        self.assertEqual(expression(job["if"], event="pull_request_target", result="skipped"), "True")
        # The ordinary nested group cannot cancel the outer PR group.
        self.assertEqual(expression(job["concurrency"]["group"], event="pull_request_target"),
                         "pr-build-jobs-run-42")

    def test_validator_uses_trusted_revision_and_no_publication_secret(self):
        job = ENTRY["jobs"]["staging-identity"]
        checkout = job["steps"][0]["with"]
        self.assertEqual(checkout["ref"], "${{ github.workflow_sha }}")
        self.assertIs(checkout["persist-credentials"], False)
        self.assertEqual(job["permissions"], {"contents": "read"})
        self.assertNotIn("secrets", job)
        self.assertNotIn("concurrency", job)
        self.assertEqual(ENTRY["jobs"]["build-candidate"]["permissions"],
                         {"contents": "read", "statuses": "write", "actions": "read"})
        self.assertEqual(BUILD["permissions"], {"contents": "read", "statuses": "write"})
        self.assertEqual(BUILD["jobs"]["pick-runner"]["permissions"], {"actions": "read"})
        self.assertEqual(set(BUILD["jobs"]), {"pick-runner", "sandboxed-build",
                         "publish-merge-group-cache", "finalize-merge-group-build"})

    def test_candidate_defined_reusable_callers_cannot_supply_trusted_tooling(self):
        guard = BUILD["jobs"]["sandboxed-build"]["if"]
        self.assertEqual(expression(guard), "True")
        self.assertEqual(expression(guard, caller=f"{REPO}/.github/workflows/evil.yml@refs/heads/main"), "False")
        self.assertEqual(expression(guard, event="pull_request"), "False")


if __name__ == "__main__":
    unittest.main()
