#!/usr/bin/env python3
"""Keep native publication, mandatory verdicts and retry work on their intended paths."""
from pathlib import Path
import json
import unittest
import os
import subprocess
import tempfile
import yaml

ROOT = Path(__file__).resolve().parents[1]

def workflow(name):
    return yaml.safe_load((ROOT / '.github/workflows' / name).read_text())

class Throughput(unittest.TestCase):
    def test_workflow_steps_have_an_action_and_mapping_environment(self):
        for path in (ROOT / '.github/workflows').glob('*.yml'):
            for job in workflow(path.name).get('jobs', {}).values():
                if not isinstance(job, dict):
                    continue
                for step in job.get('steps', []):
                    with self.subTest(workflow=path.name, step=step.get('name')):
                        self.assertTrue('run' in step or 'uses' in step)
                        if 'env' in step:
                            self.assertIsInstance(step['env'], dict)

    def test_publication_is_native_and_secret_is_confined_to_upload(self):
        steps = workflow('publish-lake-cache.yml')['jobs']['publish']['steps']
        upload = next(s for s in steps if s.get('id') == 'upload')
        self.assertIn('lake cache put-staged', upload['run'])
        self.assertIn('--repo TauCetiProject/TauCeti', upload['run'])
        self.assertIn('--rev="$REVISION" --toolchain="$ELAN_TOOLCHAIN"', upload['run'])
        self.assertEqual([s['id'] for s in steps if 'secrets.LAKE_CACHE_KEY' in str(s)], ['upload'])
        confirm = next(s for s in steps if s.get('id') == 'confirm')
        self.assertIn('--expected "$RUNNER_TEMP/lake-publication-plan/outputs.jsonl"', confirm['run'])

    def test_required_status_delivery_retries_and_failure_is_visible_for_batches(self):
        jobs = workflow('pr-build.yml')['jobs']
        report = next(s for s in jobs['sandboxed-build']['steps'] if s.get('id') == 'report')['run']
        self.assertIn('CI_STATUS_MAX_WAIT=600', report)
        self.assertNotIn('status_wait=0', report)
        self.assertIn("outputs.build-state == 'success'", jobs['publish-merge-group-cache']['if'])
        self.assertIn('finalize-merge-group-build', jobs)
        # Execute the actual delivery tail: a failed required status must make
        # batch reporting red so retained intents are recovered without a build.
        tail = report[report.index('          CI_STATUS_MAX_WAIT=600'.strip()):]
        tail = tail.replace('${{ env.IS_BATCH }}', 'true')
        with tempfile.TemporaryDirectory() as directory:
            command = Path(directory) / 'python3'
            command.write_text('#!/bin/sh\nexit "${STATUS_RC}"\n')
            command.chmod(0o755)
            for rc in (0, 1):
                env = dict(os.environ, PATH=directory + os.pathsep + os.environ['PATH'],
                           STATUS_RC=str(rc), RUNNER_TEMP=directory)
                result = subprocess.run(['bash', '-eu', '-c', 'post_fail=0; state=success\n' + tail],
                                        env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, rc, result.stdout + result.stderr)

    def test_retained_statuses_recover_even_if_the_build_workflow_succeeded(self):
        retry = workflow('retry-ci-status.yml')['jobs']['publish']
        self.assertIn("workflow_run.conclusion == 'failure'", retry['if'])
        self.assertIn("workflow_run.conclusion == 'success'", retry['if'])
        self.assertIn("startsWith(github.event.workflow_run.display_title, 'bors branch=')", retry['if'])
        discover = next(s for s in retry['steps'] if s.get('id') == 'intents')
        self.assertIn('ci-status-intents-sandbox-', discover['run'])
        self.assertIn("present=", discover['run'])

    def test_manual_reporting_recovery_keeps_original_run_identity_and_skips_build_sweep(self):
        retry = workflow('retry-ci-status.yml')
        jobs = retry['jobs']
        publish = jobs['publish']
        self.assertIn("inputs.source_run_id != ''", publish['if'])
        self.assertIn('inputs.source_run_id', publish['env']['CI_STATUS_SOURCE_RUN_ID'])
        self.assertIn('inputs.source_run_id && inputs.source_attempt', publish['concurrency']['group'])
        self.assertIn("inputs.source_run_id == ''", jobs['recover-builds']['if'])
        discover = next(s for s in publish['steps'] if s.get('id') == 'intents')['run']
        for guard in ("run.get('path') != '.github/workflows/pr-build.yml'", "run.get('event') not in allowed",
                      "run.get('status') != 'completed'", "get('full_name') != repo"):
            self.assertIn(guard, discover)

    def test_fork_status_recovery_accepts_the_automatic_trusted_workflow(self):
        steps = workflow('retry-ci-status.yml')['jobs']['publish']['steps']
        shell = next(s['run'] for s in steps if s.get('id') == 'intents')
        guard = shell.split("python3 - <<'PY'\n", 1)[1].rsplit('\nPY', 1)[0]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            run = dict(id=99, path='.github/workflows/pr-build.yml', event='pull_request_target',
                       status='completed', conclusion='failure',
                       repository={'full_name': 'org/Project'}, head_repository={'full_name': 'fork/Project'})
            (root / 'source-status-run.json').write_text(json.dumps(run))
            (root / 'source-status-artifacts.json').write_text(json.dumps(dict(total_count=0, artifacts=[])))
            for event, accepted in (('workflow_run', True), ('workflow_dispatch', False)):
                env = dict(os.environ, RUNNER_TEMP=directory, GITHUB_OUTPUT=str(root / 'out'),
                           CI_STATUS_SOURCE_RUN_ID='99', CI_STATUS_SOURCE_ATTEMPT='1',
                           GITHUB_REPOSITORY='org/Project', DEFAULT_BRANCH='main', GITHUB_EVENT_NAME=event)
                result = subprocess.run(['python3', '-c', guard], env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode == 0, accepted, result.stdout + result.stderr)

    def test_old_secondary_publication_protocol_is_removed(self):
        producer = (ROOT / '.github/workflows/pr-build.yml').read_text()
        self.assertNotIn('lake_cache_reuse.py', producer)
        self.assertFalse((ROOT / 'scripts/lake_cache_reuse.py').exists())
        self.assertNotIn('LAKE_CACHE_FULL_PUBLICATION', producer)

if __name__ == '__main__':
    unittest.main()
