"""Contract tests using the actual pinned Auto-merge engine, without network calls."""

import copy
import json
import unittest
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import readiness


HEAD = "current"
NOW = 1700000000
PR = {"number": 1, "state": "open", "head": {"sha": HEAD}, "base": {"ref": "main", "sha": "tip"},
      "draft": False, "labels": []}
STATUSES = {"build": "success", "scope": "success", "bump-guard": "success"}
MERGE_BASE = "mergebase"
PATHS = ["TauCeti/X.lean"]


def board(states=None, head=HEAD, mode="commit", updated="2026-09-16T01:00:00Z", extra=None):
    if states is None:
        states = {r: "green" for r in readiness.engine().DEFAULT_RUBRICS}
    meta = {"head_sha": head, "mode": mode, "states": states, "merge_base_sha": MERGE_BASE}
    meta.update(extra or {})
    return {"body": "<!--tauceti-scoreboard--><!--tauceti-meta:v1 " + json.dumps(meta) + "-->",
            "updated_at": updated}


def marker(head=HEAD, expires=NOW + 60):
    return {"body": "<!--tauceti-review-in-progress " +
            json.dumps({"head": head, "expires_at": expires}) + "-->"}


class GateContract(unittest.TestCase):
    def check(self, expected, comments=None, statuses=None, paths=PATHS, pr=None,
              merge_base=MERGE_BASE):
        result = readiness.classify(pr or PR, [board()] if comments is None else comments,
                                    STATUSES if statuses is None else statuses, paths,
                                    merge_base, NOW)
        self.assertEqual(result["category"], expected, result)
        self.assertEqual(result["eligible"], expected == "ready-to-merge")
        if result["eligible"]:
            self.assertTrue(result["gate"]["merge"])
        return result

    def test_complete_current_review_and_all_guards_are_ready(self):
        self.check("ready-to-merge")

    def test_scope_failure_for_human_files_is_not_ready(self):
        self.check("needs-human-review", statuses=dict(STATUSES, scope="failure"),
                   paths=["web/examples/Examples.lean"])

    def test_green_scope_does_not_override_forbidden_path(self):
        self.check("needs-human-review", paths=["scripts/x.py"])

    def test_missing_scope_is_pending_and_failed_scope_is_ci_failure(self):
        self.check("awaiting-CI", statuses={"build": "success"})
        self.check("merge-check-failed", statuses=dict(STATUSES, scope="failure"))

    def test_pin_requires_bump_guard(self):
        paths = ["lake-manifest.json"]
        self.check("awaiting-CI", statuses=dict(STATUSES, **{"bump-guard": ""}), paths=paths)
        self.check("merge-check-failed", statuses=dict(STATUSES, **{"bump-guard": "failure"}),
                   paths=paths)
        self.check("ready-to-merge", paths=paths)

    def test_review_of_another_merge_base_is_not_ready(self):
        self.check("awaiting-review", merge_base="retargeted")
        self.check("awaiting-review", merge_base="")

    def test_blocking_review_of_another_merge_base_awaits_review_not_author(self):
        states = {r: "green" for r in readiness.engine().DEFAULT_RUBRICS}
        states["proof-quality"] = "blocking_request"
        self.check("awaiting-author", comments=[board(states=states)])
        self.check("awaiting-review", comments=[board(states=states)], merge_base="retargeted")
        self.check("awaiting-review", comments=[board(states=states, extra={"merge_base_sha": ""})])

    def test_stale_and_incomplete_scoreboards_cannot_be_ready(self):
        self.check("awaiting-review", comments=[board(head="old")])
        self.check("awaiting-review", comments=[board(states={"correctness": "green"})])
        self.check("awaiting-review", comments=[board(mode="init")])
        self.check("awaiting-review", comments=[])

    def test_live_review_delays_enqueue_even_after_green_review(self):
        self.check("review-in-progress", comments=[board(), marker()])
        self.check("ready-to-merge", comments=[board(), marker(expires=NOW)])
        self.check("ready-to-merge", comments=[board(), marker(head="old")])

    def test_selects_completed_current_head_not_newer_old_head_or_init(self):
        self.check("ready-to-merge", comments=[board(), board(head="old", states={}, updated="z")])
        self.check("ready-to-merge", comments=[board(), board(mode="init", states={}, updated="z")])

    def test_newer_completed_blocking_review_supersedes_approval(self):
        states = {r: "green" for r in readiness.engine().DEFAULT_RUBRICS}
        states["proof-quality"] = "blocking_request"
        self.check("awaiting-author", comments=[board(), board(states=states, updated="z")])

    def test_legacy_runs_cannot_substitute_for_complete_table(self):
        old = board(states={}, extra={"runs": [{"verdict": "approve"}]})
        self.check("awaiting-review", comments=[old])
        old["body"] += "\n" + "\n".join(
            f"| ✅ | [{r}](url) | approved | judge | summary |"
            for r in readiness.engine().DEFAULT_RUBRICS)
        self.check("ready-to-merge", comments=[old])

    def test_ci_failure_and_missing_build_are_never_ready(self):
        self.check("ci-failed", statuses=dict(STATUSES, build="failure"))
        self.check("awaiting-CI", statuses=dict(STATUSES, build="pending"))
        self.check("awaiting-CI", statuses=dict(STATUSES, build=""))

    def test_queue_independent_routing(self):
        self.check("awaiting-dependency", pr=dict(PR, base={"ref": "parent"}))
        self.check("on-hold", pr=dict(PR, draft=True))
        for label in readiness.sweep_engine().KEEP_LABELS:
            self.check("on-hold", pr=dict(PR, labels=[{"name": label.upper()}]))
        self.check(None, pr=dict(PR, state="closed"))

    def test_explicit_merge_conflict_is_not_ready(self):
        self.check("awaiting-author", pr=dict(PR, mergeable=False))


class ReadEvidence(unittest.TestCase):
    def node(self):
        return {"number": 1, "state": "OPEN", "isDraft": False, "baseRefName": "main",
                "baseRefOid": "tip",
                "headRefOid": HEAD, "mergeable": "MERGEABLE",
                "labels": {"nodes": [], "pageInfo": {"hasNextPage": False}},
                "commits": {"nodes": [{"commit": {"oid": HEAD, "status": {"contexts": [
                    {"context": k, "state": v.upper()} for k, v in STATUSES.items()]}}}]},
                "comments": {"nodes": [{"body": board()["body"], "updatedAt": "z", "createdAt": "a"}],
                             "pageInfo": {"hasNextPage": False}}}

    def test_paginated_comments_and_commit_status_contexts(self):
        first, second = self.node(), self.node()
        first["comments"]["nodes"] = []
        first["comments"]["pageInfo"] = {"hasNextPage": True, "endCursor": "next"}
        with patch.object(readiness, "graphql", side_effect=[first, second]) as api:
            pr, comments, statuses = readiness.evidence(1, "owner/repo")
        self.assertEqual(api.call_args.kwargs["cursor"], "next")
        self.assertEqual(statuses, STATUSES)
        self.assertEqual(comments[0]["updated_at"], "z")
        self.assertEqual(pr["head"]["sha"], HEAD)

    def test_missing_status_is_not_green_and_mismatched_head_fails(self):
        node = self.node()
        node["commits"]["nodes"][0]["commit"]["status"] = None
        with patch.object(readiness, "graphql", return_value=node):
            self.assertEqual(readiness.evidence(1, "owner/repo")[2], {})
            node["commits"]["nodes"][0]["commit"]["oid"] = "old"
            with self.assertRaisesRegex(RuntimeError, "current PR head"):
                readiness.evidence(1, "owner/repo")

    def test_truncated_labels_fail_closed(self):
        node = self.node()
        node["labels"]["pageInfo"]["hasNextPage"] = True
        with patch.object(readiness, "graphql", return_value=node):
            with self.assertRaisesRegex(RuntimeError, "truncated labels"):
                readiness.evidence(1, "owner/repo")

    @patch.object(readiness.core, "gh_api", return_value=MERGE_BASE + "\n")
    @patch.object(readiness, "diff_engine", return_value=SimpleNamespace(
        git_diff=lambda remote, merge_base, head: PATHS))
    @patch.object(readiness, "evidence")
    def test_head_change_invalidates_result(self, evidence, diff, api):
        moved = copy.deepcopy(PR)
        moved["head"]["sha"] = "moved"
        evidence.side_effect = [(PR, [board()], STATUSES), (moved, [], STATUSES)]
        result = readiness.assess(1, repo="owner/repo", now=NOW)
        self.assertTrue(result["gate"]["merge"])
        self.assertFalse(result["eligible"])
        self.assertEqual(result["head"], "moved")

    def test_only_approved_active_prs_fetch_diff(self):
        for current, comments, statuses, expected in (
                (PR, [board()], STATUSES, True), (PR, [], STATUSES, False),
                (PR, [board()], dict(STATUSES, build="failure"), False),
                (dict(PR, draft=True), [board()], STATUSES, False),
                (dict(PR, base={"ref": "parent", "sha": "tip"}), [board()], STATUSES, False)):
            fake = MagicMock()
            fake.git_diff.return_value = PATHS
            with patch.object(readiness, "evidence", return_value=(current, comments, statuses)), \
                 patch.object(readiness.core, "gh_api", return_value=MERGE_BASE) as api, \
                 patch.object(readiness, "diff_engine", return_value=fake):
                result = readiness.assess(1, now=NOW)
                self.assertEqual(fake.git_diff.called, expected)
                self.assertIn("compare/tip...current", api.call_args.args[0])
                self.assertEqual(result["eligible"], expected)

    @patch.object(readiness, "diff_engine")
    @patch.object(readiness, "evidence", side_effect=RuntimeError("rate limited"))
    def test_failed_read_is_not_a_merge_verdict(self, evidence, diff):
        with self.assertRaisesRegex(RuntimeError, "rate limited"):
            readiness.assess(1)
        diff.return_value.git_diff.assert_not_called()

    @patch.object(readiness, "diff_engine")
    @patch.object(readiness.core, "gh_api", side_effect=readiness.core.RateLimited("limited"))
    @patch.object(readiness, "evidence", return_value=(PR, [board()], STATUSES))
    def test_rate_limited_merge_base_read_stays_a_rate_limit(self, evidence, api, diff):
        with self.assertRaises(readiness.core.RateLimited):
            readiness.assess(1)
        diff.return_value.git_diff.assert_not_called()

    def test_graphql_http_200_rate_limit_opens_circuit(self):
        from types import SimpleNamespace
        out = SimpleNamespace(returncode=1, stdout='{"errors":[{"type":"RATE_LIMITED"}]}', stderr="")
        with patch.object(readiness.core, "_BLOCKED_UNTIL", 0), \
             patch.object(readiness.subprocess, "run", return_value=out) as run:
            for _ in range(2):
                with self.assertRaises(readiness.core.RateLimited):
                    readiness.graphql("query")
            self.assertEqual(run.call_count, 1)

    def test_missing_policy_publishes_unverified_audit(self):
        with patch.object(readiness, "engine", side_effect=RuntimeError("missing policy")):
            result = readiness.audit({"repo": "owner/repo", "prs": []})
        self.assertFalse(result["queue"]["known"])
        self.assertEqual(result["prs"], {})
        self.assertEqual(result["error"], "missing policy")


if __name__ == "__main__":
    unittest.main()
