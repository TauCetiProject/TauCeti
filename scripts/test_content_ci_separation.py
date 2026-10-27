"""Infrastructure regressions must never gate content builds or cache publication."""

from pathlib import Path
import re
import subprocess
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / '.github/workflows'


def workflow(name):
    return yaml.safe_load((WORKFLOWS / name).read_text())


class ContentCISeparationTests(unittest.TestCase):
    def test_infrastructure_runs_only_for_infrastructure_changes(self):
        infra = workflow('infrastructure-tests.yml')
        events = infra.get('on', infra.get(True))
        self.assertEqual(set(events), {'push', 'pull_request'})
        self.assertEqual(events['push']['branches'], ['main'])
        for event in events.values():
            self.assertEqual(set(event['paths']), {'scripts/**', '.github/**'})
        self.assertEqual(infra['permissions'], {'contents': 'read'})
        for job in infra['jobs'].values():
            self.assertNotIn('secrets', job)
            self.assertNotIn('needs', job)

    def test_content_jobs_never_invoke_regression_suites(self):
        for name in ('ci.yml', 'pr-build.yml', 'lint-full.yml', 'stack-policy.yml'):
            for job in workflow(name)['jobs'].values():
                for step in job.get('steps', []):
                    with self.subTest(workflow=name, step=step.get('name')):
                        self.assertNotRegex(step.get('run', ''),
                                            r'\b(?:python3?|bash)\s+(?:gate/)?scripts/(?:[\w/-]+/)?test_[\w-]+\.(?:py|sh)\b'
                                            r'|\b(?:python3?\s+-m\s+(?:unittest|pytest)|pytest|bash\s+scripts/run-infrastructure-tests\.sh)\b')
        ci = workflow('ci.yml')['jobs']
        self.assertEqual(set(ci), {'build', 'publish-lake-cache'})
        self.assertEqual(ci['publish-lake-cache']['needs'], ['build'])

    def test_workflow_contracts_are_restored_after_the_shared_overlay(self):
        for job in workflow('infrastructure-tests.yml')['jobs'].values():
            steps = job['steps']
            setup = next(i for i, s in enumerate(steps)
                         if s.get('name') == 'Prepare pinned shared tools')
            restore = next(i for i, s in enumerate(steps)
                           if 'git restore --source=HEAD --' in s.get('run', ''))
            self.assertGreater(restore, setup)
            self.assertIn('scripts/test_bors_scope_approval.py', steps[restore]['run'])
            self.assertIn('scripts/test_content_ci_separation.py', steps[restore]['run'])

    def test_dependency_warming_probes_are_manual_only(self):
        path = WORKFLOWS / 'warm-dependencies.yml'
        if not path.exists():
            self.skipTest('this generated project has no dependency warmer')
        steps = workflow(path.name)['jobs']['warm']['steps']
        probes = [step for step in steps
                  if 'bash scripts/probe_dependency_sandbox.sh' in step.get('run', '')]
        self.assertTrue(probes)
        for probe in probes:
            self.assertEqual(probe.get('if'), 'inputs.capacity')

    def test_workflow_shell_steps_parse(self):
        for name in ('ci.yml', 'pr-build.yml', 'infrastructure-tests.yml', 'lint-full.yml'):
            for job in workflow(name)['jobs'].values():
                for step in job.get('steps', []):
                    if 'run' in step:
                        shell = re.sub(r'\$\{\{.*?\}\}', 'placeholder', step['run'])
                        result = subprocess.run(['bash', '-n'], input=shell, text=True,
                                                capture_output=True)
                        self.assertEqual(result.returncode, 0,
                                         f"{name}: {step.get('name')}: {result.stderr}")


if __name__ == '__main__':
    unittest.main()
