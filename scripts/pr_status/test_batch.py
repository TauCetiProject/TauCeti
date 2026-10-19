"""Hermetic interruption/resume and artifact-provenance regressions."""

import contextlib
import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
from unittest.mock import Mock, patch

import batch
import core


class ResumeTests(unittest.TestCase):
    def setUp(self):
        stack = self.stack = contextlib.ExitStack()
        self.addCleanup(stack.close)
        root = stack.enter_context(tempfile.TemporaryDirectory())
        self.path = Path(root) / 'state.json'
        self.args = ['--since', '2026-10-19T08:00:00Z', '--state-in', str(self.path), '--state-out', str(self.path)]
        stack.enter_context(patch.dict(os.environ, {'ZULIP_EMAIL': 'bot', 'ZULIP_API_KEY': 'test'}, clear=True))
        stack.enter_context(patch.object(batch, 'PARALLEL', 1))
        self.heads = stack.enter_context(patch.object(batch, 'open_heads', return_value={'h': [1, 2, 3]}))
        self.updated = stack.enter_context(patch.object(batch, 'updated_prs', return_value=([1, 2, 3], {1})))
        stack.enter_context(patch.object(batch, 'touched_by_runs', return_value=(set(), set())))
        stack.enter_context(patch.object(batch, 'currently_running', return_value=set()))
        self.labels = stack.enter_context(patch.object(batch.labels, 'reconcile'))
        self.zulip = stack.enter_context(patch.object(batch.zulip, 'reconcile'))
        client = Mock()
        client.my_user_id.return_value = 7
        stack.enter_context(patch.object(batch.zulip, 'Zulip', return_value=client))
        core._BLOCKED_UNTIL = 0
        self.addCleanup(setattr, core, '_BLOCKED_UNTIL', 0)

    def read(self):
        return json.loads(self.path.read_text())

    def test_quota_failure_resumes_without_repeating_successful_prefix(self):
        def label(number):
            if number == '2':
                core._block_for(600)
                raise core.RateLimited('quota')
        self.labels.side_effect = label
        self.assertEqual(batch.main(self.args), 1)
        failed = self.read()
        self.assertEqual(failed['active']['pending'], [2, 3])
        self.assertEqual(failed['retry'], {})
        self.labels.reset_mock()
        self.heads.reset_mock()
        self.assertEqual(batch.main(self.args), 1)
        self.labels.assert_not_called()
        self.heads.assert_not_called()
        # Simulate the deadline passing, including in the old worker's breaker.
        failed['blocked_until'] = 0
        self.path.write_text(json.dumps(failed))
        core._BLOCKED_UNTIL = 0
        self.labels.side_effect = None
        self.assertEqual(batch.main(self.args), 0)
        self.assertEqual([c.args[0] for c in self.labels.call_args_list], ['2', '3'])
        done = self.read()
        self.assertIsNone(done['active'])
        self.assertEqual(done['watermark'], failed['active']['started_at'])

    def test_a_mid_scan_change_is_covered_by_the_next_window(self):
        state = batch.load_progress(None, '2026-10-19T08:00:00Z')
        state['active'] = {'started_at': '2026-10-19T09:00:00Z', 'pending': [2], 'opened': []}
        self.path.write_text(json.dumps(state))
        self.assertEqual(batch.main(self.args), 0)
        self.assertEqual(self.read()['watermark'], '2026-10-19T09:00:00Z')
        self.updated.return_value = ([3], set())
        self.assertEqual(batch.main(self.args), 0)
        self.updated.assert_called_with('2026-10-19T08:58:00Z')

    def test_per_pr_failure_is_queued_without_holding_healthy_work_back(self):
        self.labels.side_effect = lambda n: (_ for _ in ()).throw(RuntimeError('bad input')) if n == '2' else None
        self.assertEqual(batch.main(self.args), 0)
        self.assertEqual(self.read()['retry'], {'2': 1})
        self.updated.return_value = ([], set())
        self.labels.reset_mock()
        self.labels.side_effect = None
        self.assertEqual(batch.main(self.args), 0)
        self.labels.assert_called_once_with('2')
        self.assertEqual(self.read()['retry'], {})

    def test_parallel_completions_leave_no_pending_or_partially_written_state(self):
        with patch.object(batch, 'PARALLEL', 4):
            self.assertEqual(batch.main(self.args), 0)
        self.assertIsNone(self.read()['active'])
        self.assertEqual(self.labels.call_count, 3)

    def test_dry_run_does_not_write_or_reconcile(self):
        self.assertEqual(batch.main(self.args + ['--dry-run']), 0)
        self.assertFalse(self.path.exists())
        self.labels.assert_not_called()
        self.zulip.assert_not_called()

    def test_bad_cooldown_and_duplicate_pending_records_fail_closed(self):
        for value in (True, '600', -1, float('nan'), float('inf')):
            state = batch.load_progress(None, '2026-10-19T08:00:00Z')
            state['blocked_until'] = value
            self.path.write_text(json.dumps(state))
            with self.assertRaises(ValueError):
                batch.load_progress(self.path, 'ignored')
        state['blocked_until'] = 0
        state['active'] = {'started_at': state['watermark'], 'pending': [1, 1], 'opened': []}
        self.path.write_text(json.dumps(state))
        with self.assertRaises(ValueError):
            batch.load_progress(self.path, 'ignored')

    def test_old_retry_only_artifact_is_migrated(self):
        self.path.write_text('{"2": 3}')
        state = batch.load_progress(self.path, '2026-10-19T08:00:00Z')
        self.assertEqual(state['retry'], {'2': 3})
        self.assertIsNone(state['active'])


class ProvenanceTests(unittest.TestCase):
    def test_exact_restore_selector_rejects_untrusted_pr_workflows(self):
        workflow = Path(__file__).resolve().parents[2] / '.github/workflows/pr-status.yml'
        text = workflow.read_text()
        query = re.search(r"trusted=\$\(gh api .*?--jq '(.*?)'\)", text, re.S).group(1)
        base = {'repository': {'full_name': 'TauCetiProject/TauCeti'},
                'head_repository': {'full_name': 'TauCetiProject/TauCeti'},
                'event': 'workflow_run', 'path': '.github/workflows/pr-status.yml', 'head_branch': 'main'}
        cases = [(base, True), ({**base, 'event': 'pull_request'}, False),
            ({**base, 'event': 'pull_request_target', 'head_branch': 'fork-branch',
              'head_repository': {'full_name': 'someone/fork'}}, True),
            ({**base, 'head_repository': {'full_name': 'someone/fork'}}, False),
            ({**base, 'path': '.github/workflows/untrusted.yml'}, False),
            ({**base, 'repository': {'full_name': 'someone/fork'}}, False)]
        for run, expected in cases:
            actual = subprocess.run(['jq', '-r', query], input=json.dumps(run), text=True,
                                    capture_output=True, check=True)
            self.assertEqual(actual.stdout.strip(), str(expected).lower())


if __name__ == '__main__':
    unittest.main()
