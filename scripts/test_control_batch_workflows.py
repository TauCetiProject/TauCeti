"""Exercise label batching and the retirement of finite Actions admission execution."""

import json
import pathlib
import subprocess
import unittest

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
REPO = "TauCetiProject/TauCeti"
LABELS = "roadmap-label-reconcile.yml"


def workflow(name):
    return yaml.safe_load((ROOT / ".github/workflows" / name).read_text())


class ControlBatches(unittest.TestCase):
    def test_label_batch_filters_before_one_runner_free_debounce_group(self):
        doc = workflow(LABELS)
        self.assertEqual(len(doc["jobs"]), 1)
        self.assertNotIn("concurrency", doc)
        job = next(iter(doc["jobs"].values()))
        self.assertFalse(job["concurrency"]["cancel-in-progress"])
        self.assertNotIn("${{", job["concurrency"]["group"])
        self.assertEqual(job["environment"], dict(name="control-batch-debounce", deployment=False))
        self.assertNotIn("strategy", job)
        self.assertEqual(job["runs-on"], "ubuntu-24.04")
        for step in job["steps"]:
            self.assertNotIn("sleep ", step.get("run", ""))

    def test_pr_status_reconciles_labels_without_zulip_credentials(self):
        doc = workflow("pr-status.yml")
        steps = doc["jobs"]["reconcile"]["steps"]
        reconcile = next(s for s in steps if "scripts/pr_status/batch.py" in s.get("run", ""))
        self.assertFalse(any(k.startswith("ZULIP_") for k in reconcile["env"]))
        self.assertNotIn("--labels-only", reconcile["run"])
        for name in ("zulip-healthcheck.yml", "zulip-pr-backfill.yml"):
            self.assertFalse((ROOT / ".github/workflows" / name).exists())
        tracked = subprocess.run(
            ["git", "ls-files", "--error-unmatch", "scripts/pr_status/zulip.py"],
            cwd=ROOT, capture_output=True, text=True,
        )
        self.assertNotEqual(tracked.returncode, 0, "the PR-posting entrypoint must not be tracked")

    def test_pr_status_ignores_its_own_lifecycle_label_writes(self):
        import re
        import sys
        sys.path.insert(0, str(ROOT / "scripts/pr_status"))
        import labels
        condition = workflow("pr-status.yml")["jobs"]["reconcile"]["if"]
        found = re.search(r"contains\(fromJSON\('(\[[^']*\])'\),\s*github\.event\.label\.name\)", condition)
        self.assertIsNotNone(found, "label events must be filtered by name")
        self.assertEqual(json.loads(found.group(1)), labels.STATUS_LABELS)
        self.assertIn("!((github.event.action == 'labeled' || github.event.action == 'unlabeled')", condition)
        for label in ("self-tested", "full-lint", "lint-repair", "hold"):
            self.assertNotIn(label, labels.STATUS_LABELS)
        sweep = next(s for s in workflow("pr-labels.yml")["jobs"]["sweep"]["steps"]
                     if s.get("name") == "Reconcile open PRs")
        self.assertEqual(json.loads(sweep["env"]["LIFECYCLE"]), labels.STATUS_LABELS)

    def test_scheduled_label_sweep_is_bounded_and_keeps_a_manual_full_pass(self):
        job = workflow("pr-labels.yml")["jobs"]["sweep"]
        self.assertLess(job["timeout-minutes"], 60, "the App installation token expires after an hour")
        step = next(s for s in job["steps"] if s.get("name") == "Reconcile open PRs")
        self.assertLess(int(step["env"]["BUDGET_SECONDS"]), job["timeout-minutes"] * 60)
        self.assertIn("gh api graphql --paginate", step["run"])
        self.assertIn("labels.py reconcile \"$pr\"", step["run"])
        self.assertIn("exec python3 scripts/pr_status/labels.py reconcile-all", step["run"])
        self.assertEqual(step["env"]["FULL_PASS"], "${{ github.event_name == 'workflow_dispatch' && '1' || '' }}")

    def test_fleet_jobs_hold_no_repository_app_key(self):
        # Fleet guests receive the workflow token and the narrow CI Apps only. Jobs that mint the
        # repository App token (APP_ID/APP_PRIVATE_KEY) stay on GitHub-hosted runners.
        fleet = dict(group="TauCetiFleet", labels=["self-hosted", "linux", "x64", "tauceti-fleet-pr"])
        moved = [("pr-ci-cleanup.yml", "cleanup")] + [("pages.yml", name) for name in workflow("pages.yml")["jobs"]]
        for name, job in moved:
            with self.subTest(workflow=name, job=job):
                self.assertEqual(workflow(name)["jobs"][job]["runs-on"], fleet)
        for path in sorted((ROOT / ".github/workflows").glob("*.yml")):
            for job_name, job in (yaml.safe_load(path.read_text()).get("jobs") or {}).items():
                if "TauCetiFleet" in json.dumps(job.get("runs-on", "")):
                    with self.subTest(workflow=path.name, job=job_name):
                        self.assertNotIn("secrets.APP_PRIVATE_KEY", yaml.dump(job))

    def test_admission_has_no_actions_execution_or_sweep_wake(self):
        for name in ("auto-merge.yml", "merge-sweep.yml", "queue-release.yml"):
            self.assertFalse((ROOT / ".github/workflows" / name).exists())
        self.assertFalse((ROOT / "scripts/control_batches/merge_batch.py").exists())
        for path in (ROOT / ".github/workflows").glob("*.yml"):
            self.assertNotIn("merge-sweep.yml", path.read_text(), path.name)
            self.assertNotIn("merge_batch.py", path.read_text(), path.name)
        self.assertFalse(workflow("review.yml")["jobs"]["review"]["with"]["enable_automerge"])

    def test_label_batch_has_stateful_discovery_and_no_duplicate_event_workflow(self):
        self.assertFalse((ROOT / ".github/workflows/roadmap-label.yml").exists())
        doc = workflow(LABELS)
        triggers = doc.get("on", doc.get(True))
        self.assertEqual(triggers["pull_request_target"]["branches"], ["main"])
        self.assertIn("schedule", triggers, "unfinished work must retry after the final event")
        job = doc["jobs"]["reconcile"]
        self.assertIn("github.event.changes.body != null", job["if"])
        root_checkout = next(s for s in job["steps"] if s.get("uses", "").startswith("actions/checkout@"))
        self.assertEqual(root_checkout["with"]["ref"], "main")
        reconcile = next(s for s in job["steps"] if "--reconcile-open" in s.get("run", ""))
        self.assertIn("scripts/control_batches/roadmap_batch.py", reconcile["run"])
        self.assertIn("--max-wait 15", reconcile["run"])
        self.assertIn("--state-in", reconcile["run"])
        self.assertIn("--state-out", reconcile["run"])
        self.assertNotIn("--pr ", reconcile["run"])
        self.assertIn("limit=$((2 * count + 1))", reconcile["run"], "listing bound must grow with the repository")
        self.assertTrue(any(s.get("uses") == "actions/upload-artifact@v4" and s.get("if") == "always()"
                            for s in job["steps"]))

    def test_artifact_discovery_cannot_be_crowded_out_by_cancelled_runs(self):
        job = workflow(LABELS)["jobs"]["reconcile"]
        restore = next(s["run"] for s in job["steps"] if s.get("name") == "Restore label progress")
        self.assertIn("actions/artifacts?name=roadmap-label-state", restore)
        self.assertNotIn("status=completed", restore)
        self.assertLess(restore.index('if [[ "$trusted" == true ]]'), restore.index("gh run download"))

    def test_checkpoint_restore_recovers_from_producer_or_download_failure(self):
        import os
        import tempfile
        job = workflow(LABELS)["jobs"]["reconcile"]
        script = next(s["run"] for s in job["steps"] if s.get("name") == "Restore label progress")
        for failure in ("producer", "download"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                root = pathlib.Path(directory)
                binary = root / "gh"
                binary.write_text("#!/usr/bin/env python3\n" +
                    "import sys,os,pathlib\n" +
                    "a=sys.argv[1:]; r=pathlib.Path(os.environ['RUNNER_TEMP'])/'roadmap-state-in'\n" +
                    "if a[0]=='api' and 'actions/artifacts?' in a[1]: print('2\\n1')\n" +
                    "elif a[0]=='api':\n" +
                    " if '/runs/2' in a[1] and os.environ['FAILURE']=='producer': sys.exit(1)\n" +
                    " print('true')\n" +
                    "elif a[:2]==['run','download']:\n" +
                    " r.mkdir(parents=True,exist_ok=True)\n" +
                    " if a[2]=='2':\n" +
                    "  (r/'state.json').write_text('partial download');sys.exit(1)\n" +
                    " (r/'state.json').write_text('older valid progress')\n")
                binary.chmod(0o755)
                env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ["PATH"],
                           RUNNER_TEMP=str(root), FAILURE=failure, REPO=REPO, GH_TOKEN="test-not-a-credential")
                result = subprocess.run(["bash", "-c", script], cwd=ROOT, env=env, text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual((root / "roadmap-state-in/state.json").read_text(), "older valid progress")

    def trusted(self, value):
        predicate = (ROOT / "scripts/control_batches/trusted-label-run.jq").read_text()
        r = subprocess.run(["jq", "-e", predicate], input=json.dumps(value), text=True, capture_output=True)
        self.assertIn(r.returncode, (0, 1), r.stderr)
        return r.returncode == 0

    def test_progress_accepts_trusted_base_events_and_rejects_fork_or_unrelated_writers(self):
        base = dict(repository=dict(full_name=REPO), path=".github/workflows/" + LABELS,
                    head_repository=dict(full_name=REPO), head_branch="main", event="schedule")
        for event in ("schedule", "workflow_dispatch", "pull_request_target"):
            with self.subTest(event=event):
                self.assertTrue(self.trusted(dict(base, event=event)))
        fork_target = dict(base, event="pull_request_target", head_repository=dict(full_name="fork/TauCeti"),
                           head_branch="contribution")
        self.assertTrue(self.trusted(fork_target), "pull_request_target code comes from trusted base")
        for changes in (dict(event="pull_request"), dict(path=".github/workflows/other.yml"),
                        dict(repository=dict(full_name="fork/TauCeti")), dict(head_branch="unreviewed"),
                        dict(head_repository=dict(full_name="fork/TauCeti"))):
            with self.subTest(changes=changes):
                self.assertFalse(self.trusted(dict(base, **changes)))


if __name__ == "__main__":
    unittest.main()
