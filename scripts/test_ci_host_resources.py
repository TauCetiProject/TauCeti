#!/usr/bin/env python3
"""Regression checks for observational isolation and unchanged command outcomes."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('host_resources', HERE / 'ci_host_resources.py')
host = importlib.util.module_from_spec(spec)
spec.loader.exec_module(host)


class HostResourcesTests(unittest.TestCase):
    def invoke(self, command, out, snapshot=None):
        with patch.object(sys, 'argv', ['ci_host_resources.py', '--out', str(out), '--', *command]):
            if snapshot:
                with patch.object(host, 'snapshot', snapshot):
                    return host.main()
            return host.main()

    def test_success_failure_and_cpu_are_observed_without_changing_status(self):
        with tempfile.TemporaryDirectory() as directory:
            for code in (0, 7):
                out = Path(directory) / f'{code}.json'
                command = [sys.executable, '-c', f'sum(i*i for i in range(1000000)); raise SystemExit({code})']
                self.assertEqual(self.invoke(command, out), code)
                value = json.loads(out.read_text())
                self.assertEqual(value['exit_code'], code)
                self.assertGreater(value['command_cpu_user_s'], 0)
                self.assertGreater(value['command_max_process_rss_bytes'], 0)
                self.assertLessEqual(value['samples'], host.MAX_SAMPLES)
                self.assertGreaterEqual(value['sampler_cpu_s'], 0)

    def test_missing_proc_and_unwritable_output_are_nonfatal(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / 'observation.json'
            self.assertEqual(self.invoke([sys.executable, '-c', 'pass'], out,
                             lambda: {'missing': ['stat', 'meminfo', 'pressure/cpu']}), 0)
            self.assertIn('meminfo', json.loads(out.read_text())['missing'])
            with contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(self.invoke([sys.executable, '-c', 'raise SystemExit(1)'], out / 'absent.json'), 1)
            self.assertIn('telemetry unavailable', output.getvalue())

    def test_cancellation_flushes_partial_resources(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / 'cancel.json'
            ready = Path(directory) / 'ready'
            child = subprocess.Popen([sys.executable, str(HERE / 'ci_host_resources.py'),
                '--out', str(out), '--', sys.executable, '-c',
                f'from pathlib import Path; import time; Path({str(ready)!r}).touch(); time.sleep(30)'])
            try:
                deadline = time.monotonic() + 10
                while not ready.exists() and time.monotonic() < deadline:
                    time.sleep(.02)
                self.assertTrue(ready.exists())
                child.send_signal(signal.SIGTERM)
                self.assertEqual(child.wait(timeout=10), 128 + signal.SIGTERM)
                value = json.loads(out.read_text())
                self.assertEqual(value['cancel_signals'], [signal.SIGTERM])
                self.assertEqual(value['exit_code'], -signal.SIGTERM)
            finally:
                if child.poll() is None:
                    child.kill()
                    child.wait()

    def test_sampler_bound_and_missing_counter_coverage(self):
        sampler = host.Sampler()
        with patch.object(host, 'snapshot', return_value={'missing': ['pressure/io']}):
            sampler.sample()
            with patch.object(host, 'MAX_SAMPLES', 1):
                sampler.watch(host.threading.Event())
        self.assertEqual(sampler.samples, 1)
        self.assertIsNone(sampler.summary()['host_cpu_busy_fraction'])
        self.assertIn('pressure/io', sampler.summary()['missing'])

    def test_workflow_source_and_actual_candidate_metadata_remain_distinct(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)/'resources.json'
            with patch.dict(os.environ, {'CI_RESOURCE_WORKFLOW_SHA': 'a'*40,
                    'CI_RESOURCE_TESTED_HEAD': 'b'*40, 'CI_RESOURCE_TESTED_BASE': 'c'*40,
                    'CI_RESOURCE_DEPENDENCY_BUMP': '0', 'GITHUB_SHA': 'd'*40}):
                self.assertEqual(self.invoke([sys.executable, '-c', 'pass'], out), 0)
            value = json.loads(out.read_text())
            self.assertEqual(value['workflow_sha'], 'a'*40)
            self.assertEqual(value['tested_head_sha'], 'b'*40)
            self.assertEqual(value['tested_base_sha'], 'c'*40)
            self.assertEqual(value['dependency_bump'], '0')

    def test_failed_sample_attempts_obey_the_same_cap(self):
        sampler = host.Sampler()
        done = type('Done', (), {'wait': lambda self, interval: False})()
        with patch.object(host, 'snapshot', side_effect=RuntimeError('failed snapshot')), \
                patch.object(host, 'MAX_SAMPLES', 3):
            sampler.watch(done)
            self.assertEqual(sampler.attempts, 3)
            self.assertEqual(sampler.samples, 0)
            self.assertTrue(sampler.summary()['sample_limit_reached'])
            self.assertIn('sampler-error', sampler.summary()['missing'])

    def publication(self, directory):
        workflow = (HERE.parent / '.github/workflows/publish-lake-cache.yml').read_text()
        step = workflow.split('- name: Observe publication volume')[1]
        code = textwrap.dedent(step.split("python3 - <<'PY'\n", 1)[1].split('          PY', 1)[0])
        env = dict(STAGING=str(directory), RUNNER_TEMP=str(directory), GITHUB_RUN_ID='1',
                   GITHUB_RUN_ATTEMPT='1', UPLOADED='true', CONFIRMED='true')
        with patch.dict(os.environ, env):
            exec(compile(code, 'publication-observation', 'exec'), {})
        return json.loads((directory / 'ci-publication.json').read_text())

    def test_publication_deduplicates_mapped_artifacts_and_excludes_junk(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            artifact = '0123456789abcdef.ltar'
            (root / artifact).write_bytes(b'payload')
            (root / 'junk.ltar').write_bytes(b'junk' * 1000)
            (root / '000000000000002a.art').write_bytes(b'number')
            lines = ['"2026-03-17"', json.dumps(['a'*16, {'key': [artifact, artifact, True, 42]}]),
                     json.dumps(['b'*16, 'ffffffffffffffff.ltar']),
                     json.dumps(['b'*16, artifact])]
            mapping = '\n'.join(lines) + '\n'
            (root / 'outputs.jsonl').write_text(mapping)
            value = self.publication(root)
            self.assertTrue(value['complete'])
            self.assertEqual(value['staged_objects'], 3)
            self.assertEqual(value['staged_bytes'], len(mapping) + 7 + 6)
            self.assertTrue(value['confirmed'])

    def test_publication_missing_symlink_fifo_and_oversized_maps_are_gaps(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertFalse(self.publication(root)['complete'])
            artifact = '0123456789abcdef.ltar'
            (root / 'outputs.jsonl').write_text('"2026-03-17"\n' + json.dumps(['a'*16, artifact]))
            (root / artifact).symlink_to('/etc/passwd')
            self.assertFalse(self.publication(root)['complete'])
            (root / artifact).unlink()
            os.mkfifo(root / artifact)
            self.assertFalse(self.publication(root)['complete'])
            (root / 'outputs.jsonl').unlink()
            os.mkfifo(root / 'outputs.jsonl')
            self.assertFalse(self.publication(root)['complete'])
            (root / 'outputs.jsonl').unlink()
            with (root / 'outputs.jsonl').open('wb') as handle:
                handle.truncate(8*1024*1024 + 1)
            self.assertFalse(self.publication(root)['complete'])

    def test_workflow_output_is_outside_candidate_mounts_and_nonfatal(self):
        workflow = (HERE.parent / '.github/workflows/pr-build.yml').read_text()
        self.assertIn('python3 gate/scripts/ci_host_resources.py --out "$RUNNER_TEMP/ci-host-resources.json" --', workflow)
        self.assertIn('env -i /usr/bin/bwrap', workflow)
        self.assertNotIn('--bind "$RUNNER_TEMP"', workflow)
        self.assertNotIn('--ro-bind "$RUNNER_TEMP"', workflow)
        step = workflow.split('- name: Upload trusted host resource observations')[1].split('- name:')[0]
        self.assertIn('if: always()', step)
        self.assertIn('continue-on-error: true', step)
        publication = (HERE.parent / '.github/workflows/publish-lake-cache.yml').read_text()
        observe = publication.split('- name: Observe publication volume')[1]
        self.assertNotIn('LAKE_CACHE_KEY', observe)
        self.assertIn('follow_symlinks=False', observe)
        self.assertIn('MAX_ENTRIES = 100000', observe)


if __name__ == '__main__':
    unittest.main()
