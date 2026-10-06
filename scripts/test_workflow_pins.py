"""Ensure TauCeti runs and reads one TauCetiReview commit everywhere.

The commit appears literally in exactly two kinds of place: the three reusable-workflow `uses:`
lines (GitHub requires a literal there) and the checkout-merge-policy composite action. Every other
reader of the merge policy goes through that action, and the reusable workflows check out their own
commit, so re-pinning is one SHA replaced in four files.

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
    ("ci.yml", "readiness-tests"): 1,
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

    def test_callers_do_not_pass_review_ref(self):
        # The reusable workflows default to their own commit (job.workflow_sha); passing a ref here
        # would reintroduce a second copy of the SHA that can drift from the `uses:` line.
        for name in CALLERS:
            with self.subTest(workflow=name):
                for job in workflow_jobs(name).values():
                    self.assertNotIn("review_ref", job.get("with") or {})

    def test_policy_is_only_checked_out_through_the_action(self):
        for path in WORKFLOW_DIR.glob("*.yml"):
            with self.subTest(workflow=path.name):
                text = path.read_text()
                self.assertNotRegex(text, r"repository:\s*TauCetiProject/TauCetiReview")
                self.assertNotIn(action_pin(), CALL_PIN.sub("", text))

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
                    self.assertLessEqual(set(triggers), TRUSTED_TRIGGERS,
                                         "a trigger checks out PR-controlled code")
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


if __name__ == "__main__":
    unittest.main()
