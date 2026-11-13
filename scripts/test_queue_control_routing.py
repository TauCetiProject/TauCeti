"""Queue-critical jobs use reserved hosts while ordinary builds retain their routes."""
import json
import unittest
from pathlib import Path
import yaml
from test_pick_runner import expression

ROOT = Path(__file__).resolve().parents[1]


class QueueControlRouting(unittest.TestCase):
    def test_all_three_queue_control_jobs_use_the_reserved_class_and_host(self):
        build = yaml.safe_load((ROOT / '.github/workflows/pr-build.yml').read_text())
        publisher = yaml.safe_load((ROOT / '.github/workflows/publish-lake-cache.yml').read_text())
        picker = yaml.safe_load((ROOT / '.github/workflows/pick-runner.yml').read_text())
        expected = ['self-hosted', 'linux', 'x64', 'tauceti-fleet-queue-control',
                    'fleet-74773fc7f54d4877add11d80113fe340']
        for job in (build['jobs']['finalize-merge-group-build'], publisher['jobs']['publish']):
            self.assertEqual(expression(job['runs-on'], event='repository_dispatch', action='tauceti-bors-staging'), expected)
            self.assertNotEqual(expression(job['runs-on']), expected)
        self.assertEqual(expression(picker['jobs']['pick']['runs-on'], staging=True), expected)
        finalizer = build['jobs']['finalize-merge-group-build']
        configured = expression(finalizer['env']['CI_PUBLISHER_RUNNER_LABELS'], event='repository_dispatch', action='tauceti-bors-staging')
        self.assertEqual(json.loads(configured), expected)
        steps = finalizer['steps']
        setup = next(i for i,s in enumerate(steps) if s.get('name') == 'Prepare pinned shared tools')
        run = next(i for i,s in enumerate(steps) if s.get('run') == 'python3 scripts/finalize_batch.py')
        self.assertLess(setup, run)
        pin = steps[setup]['with']['tools-ref']
        self.assertRegex(pin, r'^[0-9a-f]{40}$')
        self.assertNotIn('queue-finalization-tools', str(steps))

    def test_smoke_dispatch_cannot_disable_reusable_manual_pr_selection(self):
        workflow = yaml.safe_load((ROOT / '.github/workflows/pick-runner.yml').read_text())
        trigger = workflow.get('on', workflow.get(True))
        self.assertIs(trigger['workflow_call']['inputs']['control_smoke']['default'], False)
        self.assertIs(trigger['workflow_dispatch']['inputs']['control_smoke']['default'], True)
        self.assertEqual(workflow['jobs']['pick']['if'], '${{ !inputs.control_smoke }}')
        self.assertIn('inputs.control_smoke', workflow['jobs']['queue-control-smoke']['if'])
