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
        self.assertNotIn('secrets.', (WORKFLOWS / 'infrastructure-tests.yml').read_text())
        for job in infra['jobs'].values():
            self.assertNotIn('secrets', job)

    def test_content_jobs_never_invoke_regression_suites(self):
        independent_tests = {'infrastructure-tests.yml', 'shadow-audits.yml', 'ci-live-tests.yml'}
        for path in WORKFLOWS.glob('*.yml'):
            if path.name in independent_tests:
                continue
            name = path.name
            for job in workflow(name)['jobs'].values():
                for step in job.get('steps', []):
                    with self.subTest(workflow=name, step=step.get('name')):
                        self.assertNotRegex(step.get('run', ''),
                                            r'\b(?:python3?|bash)\s+(?:gate/)?scripts/(?:[\w/-]+/)?test_[\w-]+\.(?:py|sh)\b'
                                            r'|\b(?:python3?\s+-m\s+(?:unittest|pytest)|pytest|bash\s+scripts/run-infrastructure-tests\.sh)\b')
        ci = workflow('ci.yml')['jobs']
        self.assertNotIn('readiness-tests', ci)
        self.assertNotIn('duplicate-audit-tests', ci)
        self.assertEqual(ci['publish-lake-cache']['needs'], ['build'])

    def test_stack_policy_suite_uses_the_production_tools_pin(self):
        production = workflow('stack-policy.yml')['jobs']['enforce']['steps']
        tests = workflow('infrastructure-tests.yml')['jobs']['python-tests']['steps']
        production_setup = next(step for step in production
                                if '/.github/actions/setup@' in step.get('uses', ''))
        test_setup = next(step for step in tests
                          if step.get('name') == 'Prepare stack-policy tools at the production pin')
        self.assertEqual(test_setup['uses'], production_setup['uses'])
        self.assertEqual(test_setup['with'], production_setup['with'])
        setup_index = tests.index(test_setup)
        regression_index = next(i for i, step in enumerate(tests)
                                if step.get('name') == 'Stack-policy regression tests')
        self.assertLess(setup_index, regression_index)

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
