"""Offline coverage and accounting regressions for the API usage report."""

import json
import contextlib
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import github_api
import github_api_report as report


class ReportTests(unittest.TestCase):
    def test_response_attempts_count_once_and_query_post_is_a_read(self):
        rows = ["job\tstep\t2026-10-19T08:00:00.123Z github-api: " + json.dumps({
            "credential": "workflow-read", "method": "POST", "path": "graphql",
            "status": status, "resource": "graphql", "remaining": "0"})
            for status in (403, 200)]
        rows.append('github-api-summary: {"workflow-read":{"requests":2,"graphql_points":3}}')
        requests, points, limited, _ = report.inspect_log("\n".join(rows))
        self.assertEqual(len(requests), 2)
        self.assertTrue(all(r[2] for r in requests))
        self.assertEqual(points, {"workflow-read": 3})
        self.assertTrue(limited)

    def test_uninstrumented_and_missing_logs_are_unknown_not_zero(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            (root / '1.log').write_text('normal log without API counters')
            runs = [{"id": n, "name": "worker", "conclusion": "success"} for n in (1, 2)]
            value = report.summarize(runs, root)['workflows']['worker']
        self.assertEqual(value['runs'], 2)
        self.assertEqual(value['logs_available'], 1)
        self.assertEqual(value['runs_with_request_telemetry'], 0)
        self.assertEqual(value['usage'], {})

    def test_no_false_limits_from_shell_echoes_pr_text_or_permission_errors(self):
        text = '\n'.join([
            '\x1b[36;1mecho "github-api: {}"',
            'a PR says rate limit exceeded',
            'github-api: {"credential":"app-write","method":"POST","resource":"core","status":403}',
            'github-api: malformed',
            'github-api-summary: null'])
        requests, _, limited, _ = report.inspect_log(text)
        self.assertEqual(len(requests), 1)
        self.assertFalse(limited)

    def test_merge_errors_establish_failure_without_inventing_request_counts(self):
        text = json.dumps({"schema": "tauceti-merge.api-error/v1",
            "gh_invocation": 50, "rate_limit_kind": "secondary"})
        requests, points, limited, _ = report.inspect_log(text)
        self.assertEqual((requests, points, limited), ([], {}, True))

    def test_duplicate_run_ids_are_rejected(self):
        runs = [{"id": 1, "name": "worker"}] * 2
        with tempfile.TemporaryDirectory() as root, self.assertRaises(ValueError):
            report.summarize(runs, Path(root))

    def test_client_classifies_graphql_200_and_secondary_403_for_the_report(self):
        for status, body, headers in [
            (200, {'errors': [{'type': 'RATE_LIMITED', 'message': 'API rate limit already exceeded'}]},
             'X-RateLimit-Resource: graphql\nX-RateLimit-Remaining: 0\nX-RateLimit-Reset: 9999999999\n'),
            (403, {'message': 'Please wait before trying again'},
             'Retry-After: 600\nX-RateLimit-Remaining: 100\n')]:
            raw = f'HTTP/2.0 {status}\n' + headers + '\n' + json.dumps(body)
            result = subprocess.CompletedProcess([], int(status >= 400), raw, '')
            output = io.StringIO()
            path = 'graphql' if status == 200 else 'repos/o/r/labels'
            with (patch.object(github_api.subprocess, 'run', return_value=result),
                  contextlib.redirect_stderr(output), self.assertRaises(github_api.Deferred)):
                github_api.GitHub(max_wait=0).request('POST', path, {}, read=True)
            requests, _, limited, _ = report.inspect_log(output.getvalue())
            self.assertEqual(len(requests), 1)
            self.assertTrue(limited)

    def test_skipped_decisions_are_distinct_from_response_counts(self):
        requests, _, _, skipped = report.inspect_log(
            'github-api-skip: {"kind":"roadmap-label","credential":"app-write"}')
        self.assertEqual(requests, [])
        self.assertEqual(skipped, {'roadmap-label': 1})

    def test_shared_quota_drops_do_not_inflate_this_workers_request_count(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            (root / '1.log').write_text('\n'.join('github-api: ' + json.dumps({
                "credential": "app-write", "method": "POST", "path": "repos/o/r/issues/1/labels",
                "resource": "core", "status": 200, "remaining": remaining})
                for remaining in (1000, 400)))
            value = report.summarize([{"id": 1, "name": "worker"}], root)
        bucket = value['workflows']['worker']['usage']['app-write/core']
        self.assertEqual((bucket['requests'], bucket['writes']), (2, 2))
        self.assertEqual(bucket['minimum_remaining_observed'], 400)


if __name__ == '__main__':
    unittest.main()
