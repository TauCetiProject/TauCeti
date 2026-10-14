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
        self.assertIn('entries > 100000', observe)


if __name__ == '__main__':
    unittest.main()
