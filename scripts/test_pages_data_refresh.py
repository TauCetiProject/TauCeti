"""Exercise the Pages reuse/refresh paths and their real artifact/freshness shell steps."""

import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOW = yaml.safe_load((ROOT / ".github/workflows/pages.yml").read_text())
DATA = WORKFLOW["jobs"]["build-data"]
STEPS = {step.get("name", step.get("uses")): step for step in DATA["steps"]}


def selected(event):
    refresh = "false" if event == "push" else "true"
    names = []
    for name, step in STEPS.items():
        condition = str(step.get("if", "true"))
        condition = condition.replace("env.REFRESH_SITE_DATA", repr(refresh))
        condition = condition.replace("steps.snapshot.outputs.present", "'true'")
        condition = condition.replace("always()", "True").replace("&&", " and ")
        if condition == "true":
            condition = "True"
        # These workflow guards contain only comparisons/booleans, never function calls.
        if eval(condition, {"__builtins__": {}}, {}):
            names.append(name)
    return names


class PagesDataRefresh(unittest.TestCase):
    def test_every_push_selects_only_restore_collect_and_artifact_steps(self):
        self.assertEqual(DATA["env"]["REFRESH_SITE_DATA"], "${{ github.event_name != 'push' }}")
        self.assertEqual(selected("push"), [
            "actions/checkout@v4", "Prepare pinned shared tools", "Restore the last published data assets",
            "Note retained data on a push deploy", "Collect the generated data assets",
            "Collect which data assets could not be regenerated", "Hand the generated data to the site build",
        ])
        self.assertEqual(WORKFLOW["concurrency"], dict(group="pages", **{"cancel-in-progress": False}))
        site = WORKFLOW["jobs"]["build-site"]
        self.assertEqual(site["needs"], "build-data")
        self.assertIn("!cancelled()", site["if"])
        self.assertTrue(any(s.get("name") == "Fold the API docs into the site under /docs" for s in site["steps"]))

    def test_scheduled_and_manual_runs_keep_every_generator_and_snapshot_save(self):
        for event in ("schedule", "workflow_dispatch"):
            with self.subTest(event=event):
                names = selected(event)
                self.assertEqual(set(names), set(STEPS) - {"Note retained data on a push deploy"})
                for name in ("Regenerate the pull-request statistics into static_files",
                             "Derive pipeline health from the same snapshot", "Wait for the background generators",
                             "Check whether a snapshot is present to save", "Save the pull-request snapshot for the next run",
                             "Save the data assets for the next run"):
                    self.assertIn(name, names)
        save = STEPS["Save the pull-request snapshot for the next run"]
        self.assertIn("always()", save["if"])
        self.assertIn("steps.snapshot.outputs.present == 'true'", save["if"])
        self.assertTrue(STEPS["Save the data assets for the next run"]["continue-on-error"])

    def run_step(self, step, root, **extra):
        env = dict(os.environ, RUNNER_TEMP=str(root / "temp"), GITHUB_OUTPUT=str(root / "outputs"), **extra)
        return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", step["run"]], cwd=root,
                              env=env, capture_output=True, text=True)

    def fixture(self, root):
        (root / "temp").mkdir()
        (root / "web/static_files").mkdir(parents=True)
        (root / "scripts").mkdir()
        # The real collector must ask its generator for the allowlist, not copy the directory.
        (root / "scripts/generated_assets.py").write_text(
            "print('pipeline-health.json\\nci-freshness.json\\nloc-tauceti.svg')\n")

    def test_retained_artifact_preserves_timestamp_bytes_and_excludes_cached_frontend(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            self.fixture(root)
            static = root / "web/static_files"
            old = b'{"generated_at":"2026-11-06T20:00:00Z","coverage":"partial"}\n'
            for name in ("pipeline-health.json", "ci-freshness.json"):
                (static / name).write_bytes(old)
            (static / "loc-tauceti.svg").write_text('<svg><!-- 2026-11-06T20:00:00Z --></svg>')
            for name in ("ci-operations.js", "site.js", "style.css"):
                (static / name).write_text("old cached frontend")
            result = self.run_step(STEPS["Collect the generated data assets"], root)
            self.assertEqual(result.returncode, 0, result.stderr)
            artifact = root / "temp/site-data"
            self.assertEqual({p.name for p in artifact.iterdir()}, {"pipeline-health.json", "ci-freshness.json", "loc-tauceti.svg"})
            target = root / "new-site/static"
            target.mkdir(parents=True)
            (target / "ci-operations.js").write_text("current commit frontend")
            for asset in artifact.iterdir():
                shutil.copyfile(asset, target / asset.name)
            self.assertEqual((target / "ci-operations.js").read_text(), "current commit frontend")
            self.assertEqual((target / "pipeline-health.json").read_bytes(), old)
            self.assertEqual(json.loads((target / "ci-freshness.json").read_text())["coverage"], "partial")
            result = self.run_step(STEPS["Collect which data assets could not be regenerated"], root)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((root / "outputs").read_text(), "assets=\n")

    def test_cold_cache_retains_available_fallbacks_and_reports_missing_pipeline_data(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            self.fixture(root)
            (root / "web/static_files/loc-tauceti.svg").write_text("committed fallback")
            result = self.run_step(STEPS["Collect the generated data assets"], root)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((root / "temp/site-data/loc-tauceti.svg").read_text(), "committed fallback")
            self.assertIn("absent or empty", result.stdout)
            self.assertIn("pipeline health (nothing to publish)", (root / "temp/data-failures").read_text())
            result = self.run_step(STEPS["Collect which data assets could not be regenerated"], root)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("pipeline health (nothing to publish)", (root / "outputs").read_text())

    def test_freshness_report_distinguishes_retained_data_and_still_fails_missing_assets_or_deploy(self):
        step = WORKFLOW["jobs"]["report-data-freshness"]["steps"][0]
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            env = dict(ASSETS="", DATA_RESULT="success", SITE_RESULT="success", FALLBACK_RESULT="skipped",
                       RESTORED_KEY="", DEPLOY_RESULT="success", REFRESH_SITE_DATA="false", GITHUB_RUN_ID="1")
            result = self.run_step(step, root, **env)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("without refreshing statistics", result.stdout)
            self.assertIn("timestamps and coverage are unchanged", result.stdout)
            self.assertNotIn("every data asset regenerated", result.stdout)
            for changed in (dict(ASSETS="pipeline health (nothing to publish)"), dict(DEPLOY_RESULT="failure")):
                result = self.run_step(step, root, **dict(env, **changed))
                self.assertEqual(result.returncode, 1)
            result = self.run_step(step, root, **dict(env, REFRESH_SITE_DATA="true"))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("every data asset regenerated", result.stdout)


if __name__ == "__main__":
    unittest.main()
