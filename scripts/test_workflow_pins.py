"""Ensure TauCeti runs and reads one TauCetiReview commit everywhere.

The policy commit appears in the three reusable-workflow `uses:` lines and their required
`review_ref` inputs, and in the checkout-merge-policy composite action. Other policy readers
go through that action; every explicit reference must agree.

Run with: python3 scripts/test_workflow_pins.py
"""

import pathlib
import re
import unittest

import yaml


ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOW_DIR = ROOT / ".github/workflows"
CALLERS = ("auto-merge.yml", "merge-sweep.yml", "review.yml")
ACTION = ROOT / ".github/actions/checkout-merge-policy/action.yml"
LOCAL_ACTION = "./.github/actions/checkout-merge-policy"
# Each job that reads the merge policy, with how many times it does so.
POLICY_READERS = {
    ("infrastructure-tests.yml", "python-tests"): 1,
    ("pages.yml", "build-data"): 1,
    ("pr-labels.yml", "label-resolved"): 1,
    ("pr-labels.yml", "sweep"): 1,
    ("pr-status.yml", "reconcile"): 1,
}
# Triggers under which a plain `actions/checkout` gets trusted code: the default branch, or the
# base of a pull request. `pull_request` and `merge_group` check out code a PR controls, so a
# workflow on either must not load the local action from its checkout.
TRUSTED_TRIGGERS = {
    "push", "schedule", "workflow_dispatch", "workflow_run", "pull_request_target", "issue_comment",
}
CALL_PIN = re.compile(
    r"uses:\s+TauCetiProject/TauCetiReview/\.github/workflows/[^@\s]+@([0-9a-f]{40})"
)


def action_pin():
    steps = yaml.safe_load(ACTION.read_text())["runs"]["steps"]
    checkouts = [s for s in steps if str(s.get("uses", "")).startswith("actions/checkout@")]
    assert len(checkouts) == 1, "expected one checkout in the merge-policy action"
    w = checkouts[0]["with"]
    assert w["repository"] == "TauCetiProject/TauCetiReview"
    assert w["path"] == ".tauceti-review"
    assert str(w["sparse-checkout"]).split() == ["runner"]
    assert w["persist-credentials"] is False
    return str(w["ref"])


def workflow_jobs(name):
    return yaml.safe_load((WORKFLOW_DIR / name).read_text())["jobs"]


def workflow_triggers(name):
    data = yaml.safe_load((WORKFLOW_DIR / name).read_text())
    on = data.get("on", data.get(True))  # YAML 1.1 reads a bare `on` key as True
    if isinstance(on, str):
        return {on: None}
    if isinstance(on, list):
        return {t: None for t in on}
    return on


def covers(sparse_entry, path):
    """Whether a sparse-checkout entry includes `path`, compared by whole path components."""
    entry = pathlib.PurePosixPath(sparse_entry.strip("/")).parts
    return pathlib.PurePosixPath(path).parts[: len(entry)] == entry


class WorkflowPins(unittest.TestCase):
    def test_reusable_calls_and_action_share_one_sha(self):
        pin = action_pin()
        self.assertRegex(pin, r"^[0-9a-f]{40}$")
        for name in CALLERS:
            with self.subTest(workflow=name):
                calls = CALL_PIN.findall((WORKFLOW_DIR / name).read_text())
                self.assertEqual(calls, [pin], f"{name} calls a different TauCetiReview commit")

    def test_callers_pass_the_exact_review_ref(self):
        # The engine requires an explicit immutable ref; keep it equal to the workflow pin.
        for name in CALLERS:
            with self.subTest(workflow=name):
                for job in workflow_jobs(name).values():
                    if CALL_PIN.search(str(job.get("uses", ""))):
                        self.assertEqual((job.get("with") or {}).get("review_ref"), action_pin())

    def test_policy_is_only_checked_out_through_the_action(self):
        for path in WORKFLOW_DIR.glob("*.yml"):
            with self.subTest(workflow=path.name):
                text = path.read_text()
                self.assertNotRegex(text, r"repository:\s*TauCetiProject/TauCetiReview")
                self.assertNotIn(action_pin(), re.sub(r"review_ref:\s*[0-9a-f]{40}", "", CALL_PIN.sub("", text)))

    def test_policy_readers_use_the_action_from_a_trusted_checkout(self):
        found = {}
        for path in WORKFLOW_DIR.glob("*.yml"):
            for job_name, job in workflow_jobs(path.name).items():
                steps = job.get("steps") or []
                uses = [i for i, s in enumerate(steps) if s.get("uses") == LOCAL_ACTION]
                if not uses:
                    continue
                found[(path.name, job_name)] = len(uses)
                with self.subTest(workflow=path.name, job=job_name):
                    # A plain checkout is trusted code only under these triggers.
                    triggers = workflow_triggers(path.name)
                    if path.name == "infrastructure-tests.yml":
                        # This job deliberately tests candidate tooling. It has no
                        # secrets or write token, and publishes no merge verdict.
                        self.assertEqual(set(triggers), {"push", "pull_request"})
                        document = yaml.safe_load(path.read_text())
                        self.assertEqual(document["permissions"], {"contents": "read"})
                        self.assertNotIn("secrets", job)
                    else:
                        self.assertLessEqual(set(triggers), TRUSTED_TRIGGERS,
                                             "a production trigger checks out PR-controlled code")
                    if "push" in triggers:
                        self.assertEqual((triggers["push"] or {}).get("branches"), ["main"])
                    # The local action must come from the last checkout at the workspace root
                    # before it, of this repository's own ref: no repository or ref override.
                    root = [s for s in steps[: uses[0]]
                            if str(s.get("uses", "")).startswith("actions/checkout@")
                            and "path" not in (s.get("with") or {})]
                    self.assertTrue(root, "no checkout at the workspace root before the action")
                    w = root[-1].get("with") or {}
                    for key in ("repository", "ref"):
                        self.assertNotIn(key, w)
                    sparse = str(w.get("sparse-checkout", "")).split()
                    if sparse:
                        self.assertTrue(
                            any(covers(p, LOCAL_ACTION.removeprefix("./")) for p in sparse),
                            f"sparse checkout {sparse} omits {LOCAL_ACTION}")
        self.assertEqual(found, POLICY_READERS)


class ContentWorkflowCompleteness(unittest.TestCase):
    """Setup-only success must not replace candidate testing or guarded reporting."""

    def test_pr_build_retains_candidate_audits_and_status_publication(self):
        jobs = workflow_jobs("pr-build.yml")
        steps = jobs["sandboxed-build"]["steps"]
        names = [step.get("name") for step in steps]
        required = [
            "Resolve PR head",
            "Checkout the exact candidate head (untrusted contents, no credentials)",
            "Attest exact-head Lake configuration before executing Lake",
            "Reject option overrides and metaprogramming (allow local macros)",
            "Build the trusted environment-lint driver (before any candidate code runs)",
            "Build exact candidate under bwrap with workflow-pinned audits, offline",
            "Report build and bump-guard statuses to the PR head commit",
        ]
        for name in required:
            self.assertIn(name, names)
        self.assertEqual([names.index(name) for name in required],
                         sorted(names.index(name) for name in required))
        build = next(step for step in steps if step.get("id") == "build")
        self.assertIn("sandbox-build.sh", build["run"])
        report = next(step for step in steps if step.get("id") == "report")
        self.assertEqual(report["if"], "always()")
        self.assertIn("post_status build", report["run"])
        self.assertIn("gate/scripts/ci_status.py resume", report["run"])
        self.assertIn("publish-merge-group-cache", jobs)
        self.assertIn("finalize-merge-group-build", jobs)

    def test_status_retry_retains_intent_discovery_and_guarded_resumption(self):
        steps = workflow_jobs("retry-ci-status.yml")["publish"]["steps"]
        names = [step.get("name") for step in steps]
        required = [
            "Discover retained intents from this exact original run",
            "Download only the selected original-run status artifacts",
            "Prepare scoped CI reporting credentials",
            "Resume status publication without rebuilding",
        ]
        for name in required:
            self.assertIn(name, names)
        self.assertEqual([names.index(name) for name in required],
                         sorted(names.index(name) for name in required))
        for name in required[1:]:
            self.assertEqual(steps[names.index(name)]["if"],
                             "steps.intents.outputs.present == 'true'")
        resume = steps[names.index(required[-1])]["run"]
        self.assertIn("scripts/ci_status.py resume", resume)
        self.assertIn("scripts/finalize_batch.py --resume", resume)


if __name__ == "__main__":
    unittest.main()
