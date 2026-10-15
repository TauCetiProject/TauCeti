#!/usr/bin/env python3
"""Dedicated placement and same-run fallback are bounded and fail closed."""

import unittest

from fleet_recovery import recover
from fleet_runner import choose
from finalize_batch import unacquired_fleet_retry


def runner(*, busy=False, status="online", labels=None):
    return dict(
        busy=busy,
        status=status,
        labels=[
            dict(name=n)
            for n in (labels or ["self-hosted", "linux", "x64", "tauceti-fleet"])
        ],
    )


class Selection(unittest.TestCase):
    def test_idle_host_preferred_and_busy_offline_hosts_excluded(self):
        for runners, expected in [
            ([runner()], True),
            ([runner(busy=True)], False),
            ([runner(status="offline")], False),
            ([runner(busy=True), runner()], True),
            ([runner(labels=["ubuntu-latest"])], False),
        ]:
            self.assertEqual(
                choose(
                    [dict(total_count=len(runners), runners=runners)],
                    enabled=True,
                    attempt=1,
                ),
                expected,
            )

    def test_partial_inventory_disabled_feature_and_retries_use_namespace(self):
        page = dict(total_count=1, runners=[runner()])
        self.assertFalse(choose([page], enabled=False, attempt=1))
        self.assertFalse(choose([page], enabled=True, attempt=2))
        self.assertFalse(
            choose([dict(total_count=2, runners=[runner()])], enabled=True, attempt=1)
        )


class Recovery(unittest.TestCase):
    def test_unacquired_cancellation_does_not_publish_a_false_bors_failure(self):
        env = dict(FLEET_FALLBACK_CANDIDATE="true", BORS_STAGING="true",
                   GITHUB_RUN_ATTEMPT="1", GITHUB_RUN_ID="42", BUILD_JOB_RESULT="cancelled")
        job = dict(name="sandboxed-build", labels=["tauceti-fleet"], runner_id=0,
                   runner_name="", conclusion="cancelled")
        def fetch(path):
            return dict(total_count=1, jobs=[job])
        self.assertTrue(unacquired_fleet_retry(env, fetch=fetch))
        job["runner_id"] = 123
        self.assertFalse(unacquired_fleet_retry(env, fetch=fetch))
        job["runner_id"] = 0
        env["GITHUB_RUN_ATTEMPT"] = "2"
        self.assertFalse(unacquired_fleet_retry(env, fetch=fetch))

    def fixture(self, *, acquired=False):
        self.now = 1000
        self.calls = []
        self.canceled = False
        self.run = dict(
            id=42,
            event="repository_dispatch",
            run_attempt=1,
            status="in_progress",
            display_title="bors branch=main batch=1 head="
            + "a" * 40
            + " base="
            + "b" * 40,
            path=".github/workflows/pr-build.yml",
            repository=dict(full_name="TauCetiProject/TauCeti"),
        )
        self.job = dict(
            name="sandboxed-build",
            labels=["self-hosted", "tauceti-fleet"],
            status="queued",
            runner_name="runner" if acquired else "",
            created_at="1970-01-01T00:00:00Z",
        )

        def fetch(path, data=None):
            self.calls.append((path, data))
            if path.endswith("/cancel"):
                self.canceled = True
                return {}
            if path.endswith("/rerun"):
                return {}
            if "/jobs?" in path:
                return dict(total_count=1, jobs=[self.job])
            return dict(
                self.run,
                **(
                    dict(status="completed", conclusion="cancelled")
                    if self.canceled
                    else {}
                ),
            )

        return fetch

    def test_two_minute_wait_reuses_same_run_and_does_not_redispatch(self):
        fetch = self.fixture()
        result = recover(
            42,
            fetch=fetch,
            clock=lambda: self.now,
            wall=lambda: self.now,
            sleep=lambda n: None,
        )
        self.assertEqual(result, "rerun-on-namespace-requested")
        self.assertEqual(
            [p for p, d in self.calls if d is not None],
            ["/actions/runs/42/cancel", "/actions/runs/42/rerun"],
        )

    def test_acquired_runner_is_never_canceled(self):
        fetch = self.fixture(acquired=True)
        self.assertEqual(recover(42, fetch=fetch), "runner-acquired")
        self.assertFalse(any(d is not None for _, d in self.calls))

    def test_second_attempt_has_no_fallback_loop(self):
        fetch = self.fixture()
        self.run["run_attempt"] = 2
        self.assertEqual(recover(42, fetch=fetch), "not-an-initial-bors-attempt")

    def test_truncated_jobs_cannot_authorize_cancellation(self):
        fetch = self.fixture()

        def incomplete(path, data=None):
            value = fetch(path, data)
            if "/jobs?" in path:
                value["total_count"] = 2
            return value

        with self.assertRaises(ValueError):
            recover(42, fetch=incomplete)
        self.assertFalse(self.canceled)


if __name__ == "__main__":
    unittest.main()
