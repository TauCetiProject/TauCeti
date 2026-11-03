"""Lost wake-ups and concurrent edits must remain fresh ahead of bounded queue rechecks."""

import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / ".tauceti-review/runner"))
spec = importlib.util.spec_from_file_location("merge_batch", ROOT / "scripts/control_batches/merge_batch.py")
batch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(batch)
sweep = batch.sweep


def pr(number, updated="2026-11-03T02:00:00Z", labels=()):
    return dict(number=number, updated_at=updated, head=dict(sha=str(number) * 40),
                labels=[dict(name=label) for label in labels], isDraft=False)


def observed(p, at=100):
    return dict(head=p["head"]["sha"], at=at, batch_observed_updated_at=p["updated_at"])


class MergeBatch(unittest.TestCase):
    def setUp(self):
        self.original_candidates = sweep.candidates
        self.original_remember = sweep.remember_sweep_attempt
        self.original_open_prs = sweep.open_prs
        self.addCleanup(setattr, sweep.api_budget, "begin_pr", sweep.api_budget.begin_pr)
        self.addCleanup(setattr, sweep.api_budget, "run", sweep.api_budget.run)
        self.addCleanup(setattr, sweep, "pr_diff", sweep.pr_diff)
        self.addCleanup(setattr, sweep, "open_prs", self.original_open_prs)
        self.addCleanup(setattr, sweep, "candidates", self.original_candidates)
        self.addCleanup(setattr, sweep, "remember_sweep_attempt", self.original_remember)
        self.addCleanup(setattr, sweep, "_sweep_progress", {})
        self.env = patch.dict(os.environ, FOCUSED="1")
        self.env.start()
        self.addCleanup(self.env.stop)
        self.repository = patch.object(sweep, "REPO", "TauCetiProject/TauCeti")
        self.repository.start()
        self.addCleanup(self.repository.stop)
        self.focused = patch.object(sweep, "FOCUSED", True)
        self.focused.start()
        self.addCleanup(self.focused.stop)
        batch.install()

    def test_comment_edits_and_deletions_are_fresh_even_without_pr_timestamp_change(self):
        p = pr(1)
        p["batch_comments"] = dict(count=3, latest=[dict(id="comment-3", updatedAt="2026-11-03T02:00:00Z")])
        previous = observed(p) | dict(batch_observed_comments=p["batch_comments"])
        self.assertFalse(batch.changed(p, previous))
        edited = dict(p, batch_comments=dict(count=3, latest=[dict(id="older-scoreboard", updatedAt="2026-11-03T03:00:00Z")]))
        self.assertTrue(batch.changed(edited, previous))
        deleted = dict(p, batch_comments=dict(count=2, latest=p["batch_comments"]["latest"]))
        self.assertTrue(batch.changed(deleted, previous))

    def test_comment_deletion_priority_does_not_depend_on_remaining_comment_timestamp(self):
        changed = pr(1, "2026-11-01T01:00:00Z")
        changed["batch_comments"] = dict(count=1, latest=[dict(id="old", updatedAt="2026-11-01T00:00:00Z")])
        prior = observed(changed) | dict(batch_observed_comments=dict(count=2, latest=changed["batch_comments"]["latest"]))
        new = pr(2, "2026-11-03T03:00:00Z")
        with patch.object(sweep, "read_sweep_progress", return_value={"1": prior}):
            selected = sweep.candidates([new, changed], set(), set())
        self.assertEqual([p["number"] for p in selected], [1, 2])

    def test_discovery_reads_comment_versions_in_pages_not_one_request_per_pr(self):
        # Reinstall against a fake REST listing so the wrapper uses it without network.
        sweep.open_prs = lambda: [pr(1), pr(2)]
        batch.install()
        def page(number, more):
            return dict(data=dict(rateLimit=dict(cost=1), repository=dict(pullRequests=dict(
                nodes=[dict(number=number, headRefOid=str(number)*40, comments=dict(totalCount=1, nodes=[dict(id=str(number), updatedAt="2026-11-03T02:00:00Z")]))],
                pageInfo=dict(hasNextPage=more, endCursor=str(number))))))
        with patch.object(sweep, "gh_json", return_value=[page(1, True), page(2, False)]) as api:
            result = sweep.open_prs()
        self.assertEqual(api.call_count, 1)
        self.assertEqual(result[1]["batch_comments"]["count"], 1)
        query = api.call_args_list[0].args[0]
        self.assertIn("--paginate", query)
        self.assertIn("--slurp", query)
        self.assertIn("$endCursor", " ".join(query))
        self.assertIn("orderBy:{field:UPDATED_AT,direction:DESC}", " ".join(query))
        self.assertNotIn("body", " ".join(query))

    def test_incomplete_comment_discovery_fails_before_any_policy_decision(self):
        sweep.open_prs = lambda: [pr(1)]
        batch.install()
        page = dict(data=dict(repository=dict(pullRequests=dict(nodes=[], pageInfo=dict(hasNextPage=True)))))
        with patch.object(sweep, "gh_json", return_value=[page]):
            with self.assertRaisesRegex(RuntimeError, "before the final page"):
                sweep.open_prs()

    def test_active_revocation_precedes_many_newer_unqueued_comment_changes(self):
        queued = pr(1)
        queued["batch_comments"] = dict(count=2, latest=[dict(id="revoked", updatedAt="2026-11-03T02:01:00Z")])
        old = observed(queued) | dict(batch_observed_comments=dict(count=1, latest=[]))
        others = [pr(n, "2026-11-03T03:00:00Z") for n in range(2, 22)]
        for other in others:
            other["batch_comments"] = dict(count=1, latest=[dict(id="new", updatedAt="2026-11-03T03:00:00Z")])
        progress = {"1": old}
        for other in others:
            progress[str(other["number"])] = observed(other) | dict(batch_observed_comments=dict(count=0, latest=[]))
        with patch.object(sweep, "read_sweep_progress", return_value=progress):
            selected = sweep.candidates(others + [queued], {1}, set())
        self.assertEqual(selected[0]["number"], 1)
        self.assertEqual(len(selected), 21)
        # Without active membership in the ordering key, every newer changed
        # comment would beat this revocation. The fixture must exercise that case.
        with patch.object(sweep, "read_sweep_progress", return_value=progress):
            without_active_priority = sweep.candidates(others + [queued], set(), set())
        self.assertNotEqual(without_active_priority[0]["number"], 1)

    def test_failed_policy_attempt_does_not_acknowledge_changed_comments(self):
        p = pr(1)
        p["batch_comments"] = dict(count=1, latest=[])
        with tempfile.TemporaryDirectory() as directory, \
             patch.dict(os.environ, SWEEP_PROGRESS_FILE=str(Path(directory) / "progress.json")), \
             patch.object(sweep, "DRY_RUN", False), \
             patch.object(sweep.api_budget, "limit", None), \
             patch.object(sweep.api_budget, "rate_limited", False):
            sweep._sweep_progress = {}
            sweep.api_budget.begin_pr()
            import pr_diff as policy_diff
            with patch.object(policy_diff, "resolve_shas", side_effect=RuntimeError("offline fixture fetch failure")):
                with self.assertRaises(RuntimeError):
                    sweep.pr_diff("o/r", 1, "a"*40, "b"*40)
            sweep.remember_sweep_attempt(p)
            self.assertTrue(batch.changed(p, sweep._sweep_progress["1"]))
            self.assertNotIn("batch_observed_comments", sweep._sweep_progress["1"])

    def test_coalesced_revocation_on_recently_checked_pr_precedes_unchanged_queue(self):
        queued = [pr(n) for n in range(1, 31)]
        progress = {str(p["number"]): observed(p, p["number"]) for p in queued}
        # Two revocation events collapse into another event's pending run. Both
        # changed inputs must be considered without trusting a trigger PR number.
        queued[-1] = pr(30, "2026-11-03T03:00:00Z")
        queued[-2] = pr(29, "2026-11-03T02:59:00Z")
        with patch.object(sweep, "read_sweep_progress", return_value=progress):
            selected = sweep.candidates(queued, set(range(1, 31)), set())
        self.assertEqual([p["number"] for p in selected[:2]], [30, 29])
        self.assertEqual(len({p["number"] for p in selected}), 30)

    def test_revocation_reaches_withdrawal_before_bounded_policy_pass_exhausts(self):
        queued = [pr(n) for n in range(1, 31)]
        progress = {str(p["number"]): observed(p) for p in queued}
        queued[-1] = pr(30, "2026-11-03T03:00:00Z")
        with patch.object(sweep, "read_sweep_progress", return_value=progress):
            selected = sweep.candidates(queued, set(range(1, 31)), set())
        begun = []
        def begin():
            if len(begun) >= 15:
                raise sweep.api_budget.Exhausted("bounded fixture pass")
            begun.append(1)
        def view(args):
            number = int(args[2])
            return dict(headRefOid=str(number)*40, baseRefName="main", id=str(number), labels=[], statusCheckRollup=[])
        def decision(comments, head, *args, **kwargs):
            return dict(review_safe=head != str(30)*40, merge=False)
        with patch.object(sweep.api_budget, "begin_pr", side_effect=begin), \
             patch.object(sweep, "gh_json", side_effect=view), \
             patch.object(sweep, "gh_jsonl", return_value=[]), \
             patch.object(sweep, "merge_base_now", return_value="base"), \
             patch.object(sweep, "current_head", side_effect=lambda n: str(n)*40), \
             patch.object(sweep, "pr_diff", return_value=["TauCeti/Foo.lean"]), \
             patch.object(sweep, "status_states", return_value=("success", "success", "success")), \
             patch.object(sweep, "decide_from_comments", side_effect=decision), \
             patch.object(sweep, "withdraw_both", return_value=True) as withdraw, \
             patch.object(sweep, "reconcile_rebase_request", return_value="ready"), \
             patch.object(sweep.backend, "publish_eligibility"), \
             patch.object(sweep, "remember_sweep_attempt"):
            with self.assertRaises(sweep.api_budget.Exhausted):
                sweep.sweep_bors(selected)
        withdraw.assert_called_once_with(30, "30", str(30)*40)
        self.assertEqual(len(begun), 15)

    def test_new_approval_does_not_require_pr_status_readiness_label(self):
        p = pr(1)
        with patch.object(sweep, "read_sweep_progress", return_value={}):
            self.assertEqual(sweep.candidates([p], set(), set()), [p])

    def test_concurrent_edit_after_discovery_remains_fresh_after_attempt_finishes(self):
        p = pr(1)
        with tempfile.TemporaryDirectory() as directory, \
             patch.dict(os.environ, SWEEP_PROGRESS_FILE=str(Path(directory) / "progress.json")), \
             patch.object(sweep, "DRY_RUN", False):
            sweep._sweep_progress = {}
            sweep.remember_sweep_attempt(p)
            checkpoint = json.loads(Path(os.environ["SWEEP_PROGRESS_FILE"]).read_text())["1"]
            self.assertFalse(batch.changed(p, checkpoint))
            self.assertTrue(batch.changed(pr(1, "2026-11-03T02:00:01Z"), checkpoint))

    def test_missing_legacy_or_bad_checkpoint_rechecks_without_granting_authority(self):
        p = pr(1)
        for previous in (None, {}, "bad", dict(head=p["head"]["sha"], at=99999999999)):
            with self.subTest(previous=previous):
                self.assertTrue(batch.changed(p, previous))
        self.assertTrue(batch.changed(pr(2), observed(p)))


if __name__ == "__main__":
    unittest.main()
