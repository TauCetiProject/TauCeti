#!/usr/bin/env python3
"""Exercise exact-candidate cancellation with mocked Bors and GitHub responses.

Cover authenticated dispatch, malformed and changing authority/run bindings,
expiry, completed work, observed reruns, API failure and idempotent normal
cancellation. No test sends production HTTP or creates approval authority.
"""
import unittest
from cancel_bors_candidate import cancel, validate_authority, validate_run, Refused


class CancellationTest(unittest.TestCase):
    def setUp(self):
        self.actor = {"id": 337246530, "login": "tau-ceti-bors[bot]", "type": "Bot"}
        self.repo = {"id": 1256881326, "full_name": "TauCetiProject/TauCeti"}
        self.payload = {"intent_id": 10, "run_id": 123, "run_attempt": 1}
        self.event = {"action": "tauceti-bors-cancel", "sender": self.actor,
                      "repository": self.repo, "client_payload": self.payload}
        self.authority = dict(self.payload, schema="tauceti-bors.cancellation/v1",
                              repository=self.repo["full_name"], repository_id=self.repo["id"],
                              batch_id=868, candidate_id=255, generation=1, branch="main",
                              head_sha="a" * 40, base_sha="b" * 40,
                              dispatch_at=1792139640000000, expires_at=1792141500)
        self.run = {"id": 123, "run_attempt": 1, "event": "repository_dispatch",
                    "path": ".github/workflows/pr-build.yml", "workflow_id": 288851159,
                    "repository": self.repo, "actor": self.actor, "triggering_actor": self.actor,
                    "created_at": "2026-10-16T08:34:25Z", "status": "in_progress",
                    "head_sha": "c" * 40,
                    "display_title": "bors branch=main batch=868 head=" + "a" * 40 + " base=" + "b" * 40}
        self.calls = []
        self.responses = [self.authority, self.run, self.run, self.authority]

    def http(self, url, token=None, method="GET"):
        self.calls.append((url, token, method))
        if method == "POST":
            return 202, None
        result = self.responses.pop(0)
        if isinstance(result, Exception):
            raise result
        return 200, result

    def execute(self):
        return cancel(self.event, "token", self.http, lambda: 1792139700)

    def test_exact_candidate_normal_cancel_uses_bound_run_and_no_candidate_checkout(self):
        self.assertEqual(self.execute(), "normal_cancellation_requested")
        self.assertEqual(self.calls[-1], ("https://api.github.com/repos/TauCetiProject/TauCeti/actions/runs/123/cancel", "token", "POST"))
        self.assertEqual(len(self.calls), 5)
        self.assertTrue(self.calls[-2][0].startswith("https://bors.taucetiproject.org/"))
        self.assertIsNone(self.calls[-2][1])

    def test_ordinary_pr_and_spoofed_dispatch_never_make_a_request(self):
        for key, value in [("action", "other"), ("repository", {}), ("sender", {}),
                           ("client_payload", {}), ("client_payload", dict(self.payload, run_attempt=2)),
                           ("client_payload", dict(self.payload, run_id=True))]:
            with self.subTest(key=key, value=value):
                event = dict(self.event, **{key: value})
                with self.assertRaises(Refused):
                    cancel(event, "token", self.http)
                self.assertFalse(self.calls)

    def test_missing_or_malformed_authority(self):
        for key, value in [("schema", "wrong"), ("repository_id", 1), ("intent_id", 11),
                           ("candidate_id", None), ("generation", None), ("head_sha", ""),
                           ("base_sha", "bad"), ("expires_at", 1), ("branch", "main\n"),
                           ("run_id", 456), ("run_attempt", 2)]:
            with self.subTest(key=key, value=value), self.assertRaises(Refused):
                validate_authority(dict(self.authority, **{key: value}), self.payload, 1792139700)

    def test_different_candidate_batch_base_repository_workflow_or_actor(self):
        changes = [("display_title", self.run["display_title"].replace("868", "869")),
                   ("display_title", self.run["display_title"].replace("b" * 40, "a" * 40)),
                   ("display_title", self.run["display_title"].replace("main", "other")),
                   ("repository", {}), ("actor", {}), ("triggering_actor", {}),
                   ("workflow_id", 1), ("path", ".github/workflows/publish-lake-cache.yml"),
                   ("event", "pull_request_target"), ("id", 456), ("run_attempt", 2),
                   ("created_at", "2026-10-15T08:34:25Z"), ("created_at", "bad")]
        for key, value in changes:
            with self.subTest(key=key, value=value), self.assertRaises(Refused):
                validate_run(dict(self.run, **{key: value}), self.authority, self.payload)

    def test_completed_cancelled_and_failed_runs_never_send_cancel(self):
        for conclusion in ("cancelled", "success", "failure"):
            with self.subTest(conclusion=conclusion):
                self.calls.clear()
                self.responses = [self.authority, dict(self.run, status="completed", conclusion=conclusion)]
                self.assertEqual(self.execute(), "already_completed")
                self.assertEqual(len(self.calls), 2)

    def test_completion_during_lookup_preserves_finalization(self):
        self.responses[2] = dict(self.run, status="completed", conclusion="success")
        self.assertEqual(self.execute(), "already_completed")
        self.assertFalse(any(c[-1] == "POST" for c in self.calls))

    def test_new_attempt_between_lookups_is_protected(self):
        self.responses[2] = dict(self.run, run_attempt=2)
        with self.assertRaises(Refused):
            self.execute()
        self.assertFalse(any(c[-1] == "POST" for c in self.calls))

    def test_requeue_or_promotion_revokes_last_authority(self):
        self.responses[3] = OSError("404 withdrawn intent no longer authorized")
        with self.assertRaises(OSError):
            self.execute()
        self.assertFalse(any(c[-1] == "POST" for c in self.calls))

    def test_generation_changed_between_checks(self):
        self.responses[3] = dict(self.authority, generation=2, candidate_id=256)
        with self.assertRaises(Refused):
            self.execute()
        self.assertFalse(any(c[-1] == "POST" for c in self.calls))

    def test_expiry_during_lookup(self):
        times = iter([1792139700, self.authority["expires_at"] + 1])
        with self.assertRaises(Refused):
            cancel(self.event, "token", self.http, lambda: next(times))
        self.assertFalse(any(c[-1] == "POST" for c in self.calls))

    def test_transient_api_errors_never_force_cancel(self):
        self.responses[1] = OSError("503")
        with self.assertRaises(OSError):
            self.execute()
        self.assertEqual(len(self.calls), 2)
        self.assertFalse(any("force" in c[0] for c in self.calls))

    def test_replay_is_exact_and_normal_cancellation_is_idempotent(self):
        self.assertEqual(self.execute(), "normal_cancellation_requested")
        self.responses = [self.authority, dict(self.run, status="completed", conclusion="cancelled")]
        self.assertEqual(self.execute(), "already_completed")
        self.assertEqual(sum(c[-1] == "POST" for c in self.calls), 1)


if __name__ == "__main__":
    unittest.main()
