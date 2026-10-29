"""Exercise nightly cache verification and reporting without builds or network access."""

import contextlib
import io
import json
import os
from pathlib import Path
import re
import shutil
from types import SimpleNamespace
import subprocess
import tempfile
import unittest
from unittest.mock import MagicMock, patch
import urllib.parse

import yaml


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = yaml.safe_load((ROOT / '.github/workflows/nightly-verify.yml').read_text())
JOBS = WORKFLOW['jobs']


def step(job, name):
    return next(s for s in JOBS[job]['steps'] if name in (s.get('id'), s.get('name')))


def condition(source, **values):
    source = source.removeprefix('${{').removesuffix('}}').strip()
    source = re.sub(r'!(?!=)', 'not ', source).replace('&&', ' and ').replace('||', ' or ')
    return eval(source, {'__builtins__': {}, 'always': lambda: True,
                         'cancelled': lambda: False, **values})


class NightlyVerification(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.temp = self.root / 'temp'
        self.temp.mkdir()
        self.helper = self.root / 'fresh/scripts'
        self.helper.mkdir(parents=True)
        (self.root / 'reference/scripts').mkdir(parents=True)
        shutil.copyfile(ROOT / 'scripts/compare-build-outputs.py',
                        self.helper / 'compare-build-outputs.py')
        self.env = {**os.environ, 'GITHUB_OUTPUT': str(self.temp / 'outputs'),
                    'GITHUB_ENV': str(self.temp / 'environment'), 'RUNNER_TEMP': str(self.temp),
                    'LAKE_ARTIFACT_CACHE': 'true', 'LAKE_RESTORE_ARTIFACTS': 'true'}

    def shell(self, body, substitutions=None):
        for key, value in (substitutions or {}).items():
            body = body.replace('${{ ' + key + ' }}', value)
        self.assertNotIn('${{', body)
        return subprocess.run(['bash', '-euo', 'pipefail', '-c', body], cwd=self.root,
                              env=self.env, text=True, capture_output=True)

    def outputs(self):
        output = Path(self.env['GITHUB_OUTPUT'])
        return dict(line.split('=', 1) for line in output.read_text().splitlines())

    def test_jobs_have_separate_budgets_and_transfer_only_the_clean_manifest(self):
        self.assertEqual(JOBS['verify']['timeout-minutes'], 360)
        self.assertEqual(JOBS['reference']['timeout-minutes'], 240)
        self.assertIn('verify', JOBS['reference']['needs'])
        for s in JOBS['reference']['steps']:
            if s.get('uses', '').startswith('actions/checkout@'):
                self.assertEqual(s['with']['ref'], '${{ needs.verify.outputs.sha }}')
                self.assertFalse(s['with']['persist-credentials'])
        steps = JOBS['verify']['steps']
        snapshot = step('verify', 'Record what the clean build produced')
        upload = step('verify', 'Retain the clean manifest for cache verification')
        self.assertLess(steps.index(snapshot), steps.index(upload))
        self.assertLess(steps.index(snapshot), steps.index(step('verify', 'fresh_audit')))
        self.assertLess(steps.index(step('verify', 'fresh_audit')), steps.index(upload))
        self.assertTrue(upload['continue-on-error'])
        self.assertEqual(upload['with']['path'], '${{ runner.temp }}/clean-manifest.txt')
        self.assertEqual(upload['with']['if-no-files-found'], 'error')
        download = step('reference', 'Download the clean manifest from the source-build job')
        self.assertEqual(download['with']['name'], '${{ needs.verify.outputs.manifest }}')
        self.assertIn('github.run_attempt', step('verify', 'rev')['run'])
        self.assertEqual(step('verify', 'fresh_build')['env']['LAKE_RESTORE_ARTIFACTS'], 'false')

    def test_audit_failure_allows_comparison_but_missing_clean_evidence_blocks_it(self):
        for build, upload, expected in (
            ('success', 'success', True), ('failure', 'skipped', False),
            ('cancelled', 'skipped', False), ('success', 'failure', False),
        ):
            # A lint failure makes verify.result=failure; it must not suppress the
            # independent comparison when the source build and evidence transfer succeeded.
            needs = SimpleNamespace(verify=SimpleNamespace(result='failure',
                outputs=SimpleNamespace(build=build, manifest_upload=upload)))
            for job in ('pick-reference-runner', 'reference'):
                self.assertEqual(condition(JOBS[job]['if'], needs=needs,
                    github=SimpleNamespace(repository='TauCetiProject/TauCeti')), expected)
            self.assertEqual(condition(step('verify', 'fresh_manifest')['if'],
                steps=SimpleNamespace(fresh_build=SimpleNamespace(outcome=build))), build == 'success')

    def test_reference_placement_uses_a_new_capacity_decision_and_attempt_fence(self):
        self.assertEqual(JOBS['pick-reference-runner']['needs'], 'verify')
        source = JOBS['reference']['runs-on'].replace('needs.pick-reference-runner', 'needs.picker')
        for current, selected, target, expected in (
            (1, '1', '["namespace-build"]', ['namespace-build']),
            (2, '1', '["namespace-build"]', 'ubuntu-24.04'),
            (2, '', '', 'ubuntu-24.04'),
        ):
            with self.subTest(current=current, selected=selected):
                actual = condition(source, github=SimpleNamespace(run_attempt=current),
                                   needs=SimpleNamespace(picker=SimpleNamespace(
                                       outputs=SimpleNamespace(attempt=selected, runner=target))),
                                   fromJSON=json.loads, format=lambda s, *args: s.format(*args))
                self.assertEqual(actual, expected)

    def test_restore_uses_the_materialized_helper_with_the_reference_as_target(self):
        # Model the reference checkout's uvx wrapper failing on a runner without uvx.
        (self.root / 'reference/scripts/lake-cache-get.sh').write_text('exit 127\n')
        (self.helper / 'lake-cache-get.sh').write_text(
            'set -eu\n[ "$1" = reference ]\nmkdir -p "$1/.lake/cache"\n'
            'echo restored > "$1/.lake/cache/artifact"\n')
        result = self.shell(step('reference', 'restore')['run'])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((self.root / 'reference/.lake/cache/artifact').exists())

    def test_a_failed_disabled_or_empty_restore_never_reaches_reference_build(self):
        for enabled, outcome, cache_enabled, populated, expected in (
            ('false', 'skipped', 'true', True, False),
            ('true', 'failure', 'true', True, False),
            ('true', 'success', 'false', True, False),
            ('true', 'success', 'true', False, False),
            ('true', 'success', 'true', True, True),
        ):
            with self.subTest(enabled=enabled, outcome=outcome,
                              cache_enabled=cache_enabled, populated=populated):
                cache = self.root / 'reference/.lake/cache'
                shutil.rmtree(cache, ignore_errors=True)
                cache.mkdir(parents=True)
                if populated:
                    (cache / 'artifact').write_text('cached')
                self.env['LAKE_ARTIFACT_CACHE'] = cache_enabled
                result = self.shell(step('reference', 'restored')['run'], {
                    'steps.refcfg.outputs.enabled': enabled, 'steps.restore.outcome': outcome})
                self.assertEqual(result.returncode, 0, result.stderr)
                outputs = self.outputs()
                builds = condition(step('reference', 'reference_build')['if'],
                                   steps=SimpleNamespace(restored=SimpleNamespace(
                                       outputs=SimpleNamespace(**outputs))))
                self.assertEqual(builds, expected)
                if not expected:
                    self.assertTrue(outputs['why'])

    def test_real_manifests_agree_diverge_or_fail_closed_when_missing(self):
        for changed, expected in ((False, 'agree'), (True, 'disagree')):
            for tree, content in (('fresh', 'clean'), ('reference', 'changed' if changed else 'clean')):
                build = self.root / tree / '.lake/build/lib/lean'
                build.mkdir(parents=True, exist_ok=True)
                (build / 'Example.olean').write_text(content)
            for job, name in (
                ('verify', 'Record what the clean build produced'),
                ('reference', 'Record what the cache-restored build produced'),
            ):
                result = self.shell(step(job, name)['run'])
                self.assertEqual(result.returncode, 0, result.stderr)
            substitutions = {'steps.restored.outputs.restored': 'true',
                             'steps.restored.outputs.why': '',
                             'steps.reference_build.outcome': 'success'}
            result = self.shell(step('reference', 'compare')['run'], substitutions)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(self.outputs()['status'], expected)
        (self.temp / 'clean-manifest.txt').unlink()
        result = self.shell(step('reference', 'compare')['run'], substitutions)
        self.assertNotEqual(result.returncode, 0, 'missing evidence must not count as agreement')

    def test_incomplete_reference_reports_inconclusive_without_a_comparison(self):
        for restored, build in (('false', 'skipped'), ('true', 'failure')):
            result = self.shell(step('reference', 'compare')['run'], {
                'steps.restored.outputs.restored': restored,
                'steps.restored.outputs.why': 'cache fetch failed',
                'steps.reference_build.outcome': build})
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(self.outputs()['status'], 'inconclusive')

    def test_reporting_alerts_on_any_incomplete_or_divergent_job(self):
        for source in ('success', 'failure', 'cancelled', 'skipped'):
            for reference in ('success', 'failure', 'cancelled', 'skipped'):
                for compare in ('agree', 'disagree', 'inconclusive', ''):
                    needs = SimpleNamespace(
                        verify=SimpleNamespace(result=source),
                        reference=SimpleNamespace(result=reference,
                                                  outputs=SimpleNamespace(compare=compare)))
                    for repo in ('TauCetiProject/TauCeti', 'someone/fork'):
                        actual = condition(JOBS['report']['if'], needs=needs,
                                           github=SimpleNamespace(repository=repo))
                        expected = repo == 'TauCetiProject/TauCeti' and (
                            source != 'success' or reference != 'success' or compare != 'agree')
                        self.assertEqual(actual, expected)

    def test_report_distinguishes_proof_failures_timeouts_and_cache_failures(self):
        body = JOBS['report']['steps'][0]['run'].split("python3 - <<'PY'\n", 1)[1].rsplit('\nPY', 1)[0]
        cases = (
            ('failure', 'failure', 'skipped', 'skipped', '', 'from-source build FAILED'),
            ('failure', 'success', 'failure', 'skipped', '', 'audit or lint FAILED'),
            ('cancelled', 'cancelled', 'skipped', 'skipped', '', 'did not complete'),
            ('success', 'success', 'success', 'cancelled', '', 'cache verification did not complete'),
            ('success', 'success', 'success', 'success', 'inconclusive', 'comparison could not be made'),
            ('success', 'success', 'success', 'success', 'disagree', 'DIFFERENT oleans'),
        )
        for result, build, audit, reference, compare, expected in cases:
            with self.subTest(result=result, build=build, reference=reference, compare=compare):
                env = {'RESULT': result, 'BUILD': build, 'AUDIT': audit, 'REFERENCE_RESULT': reference,
                       'COMPARE': compare, 'DETAIL': 'example', 'SHA': 'a' * 40,
                       'ZULIP_EMAIL': 'test@example.com', 'ZULIP_API_KEY': 'fixture',
                       'ZULIP_SITE': 'https://zulip.invalid', 'ZULIP_CHANNEL': 'Tau Ceti',
                       'ZULIP_TOPIC': 'Nightly verification', 'RUN_URL': 'https://example.com/run'}
                response = MagicMock()
                response.__enter__.return_value.read.return_value = b'{"result":"success"}'
                with patch.dict(os.environ, env, clear=True), \
                        patch('urllib.request.urlopen', return_value=response) as send, \
                        contextlib.redirect_stdout(io.StringIO()):
                    exec(compile(body, 'nightly-report', 'exec'), {})
                content = urllib.parse.parse_qs(send.call_args.args[0].data.decode())['content'][0]
                self.assertIn(expected, content)
                if build == 'cancelled':
                    self.assertNotIn('FAILED', content)
                    self.assertNotIn('suspect', content)

    def test_all_workflow_shell_steps_parse(self):
        for job in JOBS.values():
            for s in job.get('steps', []):
                if 'run' in s:
                    body = re.sub(r'\$\{\{.*?\}\}', 'placeholder', s['run'])
                    result = subprocess.run(['bash', '-n'], input=body, text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, f"{s.get('name')}: {result.stderr}")


if __name__ == '__main__':
    unittest.main()
