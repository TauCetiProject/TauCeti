"""A pr-build whose runner setup fails posts a recoverable `build`, not a verdict on the PR.

Run with: python3 scripts/test_setup_failure_status.py
"""

import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = yaml.safe_load((ROOT / '.github/workflows/pr-build.yml').read_text())
STEPS = WORKFLOW['jobs']['sandboxed-build']['steps']
CLASSIFY = 'Name the runner setup step that failed, if any'
SETUP_IDS = ('install_elan', 'lean_toolchain', 'install_bwrap', 'mathlib_ltars',
             'mathlib_fetch', 'tauceti_cache', 'watchdog_toolchain')

FAKE_GH = r"""import json, os, sys
args = sys.argv[1:]
method = args[args.index('--method') + 1]
path = next(arg for arg in args if arg.startswith('repos/'))
with open(os.environ['REQUESTS'], 'a') as log:
    log.write(f'{method} {path}\n')
if method == 'POST':
    with open(os.environ['POSTS'], 'a') as output:
        output.write(json.dumps({'path': path, 'payload': json.load(sys.stdin)}) + '\n')
    response = {}
elif path.endswith('/actions/runs/9'):
    response = {'id': 9, 'run_attempt': 1, 'conclusion': None,
                'run_started_at': '2026-11-16T00:00:00Z'}
elif path.endswith('/pulls/42'):
    response = {'state': 'open', 'head': {'sha': 'a' * 40}, 'base': {'ref': 'main'}}
elif '/commits/' in path and '/statuses?' in path:
    response = []
else:
    raise SystemExit('unexpected API request: ' + path)
print('HTTP/2 200 OK\nContent-Type: application/json\n')
print(json.dumps(response))
"""


def step(name=None, ident=None):
    return next(s for s in STEPS if (name and s.get('name') == name) or (ident and s.get('id') == ident))


class Contract(unittest.TestCase):
    def test_classifier_follows_every_setup_step_and_precedes_the_build(self):
        names = [s.get('name') for s in STEPS]
        at = names.index(CLASSIFY)
        classify = STEPS[at]
        self.assertIn('always()', classify['if'])
        for ident in SETUP_IDS:
            with self.subTest(step=ident):
                self.assertLess(names.index(step(ident=ident)['name']), at)
                self.assertIn(f"steps.{ident}.outcome == 'failure'", classify['env']['FAILED_SETUP'])
        self.assertEqual(at + 1, names.index(step(ident='build')['name']))
        self.assertIn('SETUP_FAILED=', classify['run'])

    def test_shim_probe_is_skipped_after_a_setup_failure(self):
        self.assertIn('!env.SETUP_FAILED', step(ident='shim_expiry')['if'])


class Report(unittest.TestCase):
    def run_report(self, setup_failed, *, batch=False):
        head, base, tree = 'a' * 40, 'b' * 40, 'd' * 40
        # A batch builds its frozen candidate unchanged, so T is H.
        mode, tested = ('frozen-candidate', head) if batch else ('pr-integration', 'c' * 40)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'gate').symlink_to(ROOT)
            (root / 'tested-integration.json').write_text(json.dumps(dict(
                schema=1, mode=mode, head_sha=head, base_sha=base,
                tested_sha=tested, tested_tree=tree, pin_resolution='merged')))
            fake = root / 'bin'
            fake.mkdir()
            (fake / 'gh').write_text(f'#!{sys.executable}\n' + FAKE_GH)
            (fake / 'gh').chmod(0o755)
            # A failed setup step skips the build and, with this change, the shim probe.
            values = {'env.IS_BATCH': 'true' if batch else 'false', 'env.PINS_KNOWN': '1',
                      'env.SCOPE_OK': '1', 'steps.pr.outputs.sha': head,
                      'steps.pr.outputs.status_sha': head, 'steps.pr.outputs.base_ref': 'main',
                      'steps.pr.outputs.num': '42', 'steps.build.outcome': 'skipped',
                      'steps.shim_expiry.outcome': 'skipped', 'steps.import_headers.outcome': 'success'}
            script = re.sub(r'\$\{\{ (.*?) \}\}', lambda m: values.get(m[1], ''), step(ident='report')['run'])
            script = script.replace('CI_STATUS_MAX_WAIT=600', 'CI_STATUS_MAX_WAIT=0')
            env = dict(os.environ, PATH=str(fake) + os.pathsep + os.environ['PATH'],
                       RUNNER_TEMP=str(root), RAW_HEAD=head, CAPTURED_BASE=base,
                       CANDIDATE_MODE=mode, TESTED_SHA=tested, TESTED_TREE=tree,
                       POSTS=str(root / 'posts'), REQUESTS=str(root / 'requests'),
                       GITHUB_OUTPUT=str(root / 'output'), GITHUB_REPOSITORY='o/r',
                       GITHUB_RUN_ID='9', GITHUB_RUN_ATTEMPT='1',
                       IS_BATCH='true' if batch else 'false', SETUP_FAILED=setup_failed)
            result = subprocess.run(['bash', '-e', '-c', script], cwd=root, env=env,
                                    capture_output=True, text=True)
            posts, requests = root / 'posts', root / 'requests'
            lines = posts.read_text().splitlines() if posts.exists() else []
            self.requests = requests.read_text().splitlines() if requests.exists() else []
            return result, {p['payload']['context']: p['payload'] for p in map(json.loads, lines)}

    def test_pr_setup_failure_posts_pending_build_and_green_scope(self):
        result, posts = self.run_report('Lean toolchain install')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(posts['build']['state'], 'pending', result.stderr)
        self.assertIn('runner setup failed (Lean toolchain install)', posts['build']['description'])
        self.assertNotIn('shim', posts['build']['description'])
        self.assertEqual(posts['scope']['state'], 'success')
        self.assertEqual(posts['bump-guard']['state'], 'success')
        self.assertIn('GET repos/o/r/pulls/42', self.requests)

    def test_batch_setup_failure_stays_terminal(self):
        result, posts = self.run_report('elan install', batch=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(posts['build']['state'], 'failure', result.stderr)
        self.assertIn('runner setup failed (elan install)', posts['build']['description'])
        self.assertFalse([r for r in self.requests if '/pulls/' in r], self.requests)

    def test_without_setup_failure_a_skipped_build_is_still_a_failure(self):
        _, posts = self.run_report('')
        self.assertEqual(posts['build']['state'], 'failure')


if __name__ == '__main__':
    unittest.main()
