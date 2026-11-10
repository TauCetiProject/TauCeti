#!/usr/bin/env python3
"""Keep native publication, mandatory verdicts and retry work on their intended paths."""
from pathlib import Path
import unittest
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

    def test_optional_status_retry_does_not_change_the_build_verdict(self):
        jobs = workflow('pr-build.yml')['jobs']
        report = next(s for s in jobs['sandboxed-build']['steps'] if s.get('id') == 'report')['run']
        self.assertIn('status_wait=0', report)
        self.assertIn('CI_STATUS_MAX_WAIT="$status_wait"', report)
        self.assertIn('[ "$state" = "success" ]', report)
        self.assertIn('"${{ env.IS_BATCH }}" != "true"', report)
        self.assertIn("outputs.build-state == 'success'", jobs['publish-merge-group-cache']['if'])
        self.assertIn('finalize-merge-group-build', jobs)

    def test_old_secondary_cache_protocol_is_removed(self):
        producer = (ROOT / '.github/workflows/pr-build.yml').read_text()
        self.assertNotIn('bulk-unpack-cache.py', producer)
        for name in ('bulk-unpack-cache.py', 'lake_cache_reuse.py'):
            self.assertFalse((ROOT / 'scripts' / name).exists())
        self.assertNotIn('LAKE_CACHE_FULL_PUBLICATION', producer)

if __name__ == '__main__':
    unittest.main()
