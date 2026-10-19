"""Hermetic API, mutation, recovery, and workflow tests: python3 scripts/test_roadmap_api.py."""

import argparse
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
from unittest.mock import Mock, patch

import github_api as ga
import roadmap_label as rl
import structure_nudge as sn


def reply(status=200, data=None, headers=None):
    headers = {"X-RateLimit-Remaining": "100", "X-RateLimit-Reset": "2000", **(headers or {})}
    raw = f"HTTP/2.0 {status}\r\n" + "".join(f"{k}: {v}\r\n" for k, v in headers.items())
    return subprocess.CompletedProcess([], 0 if status < 400 else 1,
                                       raw + "\r\n" + json.dumps(data), "gh: error" if status >= 400 else "")


def info(number=1, labels=("roadmap/PDE",), updated="2026-10-12T00:00:00Z"):
    return {"number": number, "title": "test", "body": "Roadmap: PDE", "state": "open",
            "head": {"sha": "head"}, "base": {"sha": "base", "ref": "main"}, "changed_files": 1,
            "labels": [{"name": label} for label in labels], "updated_at": updated}


FILES = [{"filename": "TauCeti/FooBar.lean", "status": "added"}]


def graph_row(head="head"):
    return {"title": "test", "body": "Roadmap: PDE", "state": "OPEN",
            "headRefOid": head, "baseRefOid": "base", "baseRefName": "main", "changedFiles": 1,
            "labels": {"nodes": [{"name": "roadmap/PDE"}], "pageInfo": {"hasNextPage": False}},
            "files": {"nodes": [{"path": "TauCeti/FooBar.lean", "changeType": "ADDED"}],
                      "totalCount": 1, "pageInfo": {"hasNextPage": False, "endCursor": "last"}}}


def graph_result(row):
    return {"repository": {"pullRequest": row}}


class API(unittest.TestCase):
    def setUp(self):
        self.clock = 1000.0
        self.sleeps = []
        self.stack = contextlib.ExitStack()
        self.addCleanup(self.stack.close)
        self.output = io.StringIO()
        self.stack.enter_context(contextlib.redirect_stderr(self.output))
        self.stack.enter_context(patch.dict(os.environ, {}, clear=True))
        self.stack.enter_context(patch.object(ga.time, "time", side_effect=lambda: self.clock))
        self.stack.enter_context(patch.object(ga.time, "monotonic", side_effect=lambda: self.clock))
        self.stack.enter_context(patch.object(ga.time, "sleep", side_effect=self.sleep))
        self.run = self.stack.enter_context(patch.object(ga.subprocess, "run"))
        self.api = ga.GitHub()

    def sleep(self, seconds):
        self.sleeps.append(seconds)
        self.clock += seconds

    def test_read_and_write_select_different_credentials_without_leaking_them(self):
        os.environ.update(GH_READ_TOKEN="read-secret", GH_TOKEN="write-secret", GITHUB_TOKEN="other-secret")
        self.run.return_value = reply(data={})
        self.api.request("GET", "repos/o/r/pulls/1")
        self.api.request("POST", "repos/o/r/issues/1/labels", {"labels": ["roadmap/none"]})
        read, write = self.run.call_args_list
        self.assertEqual(read.kwargs["env"]["GH_TOKEN"], "read-secret")
        self.assertNotIn("GITHUB_TOKEN", read.kwargs["env"])
        self.assertEqual(write.kwargs["env"]["GH_TOKEN"], "write-secret")
        self.assertEqual(json.loads(write.kwargs["input"]), {"labels": ["roadmap/none"]})
        self.api.report()
        self.assertEqual(self.api.stats["workflow-read"]["reads"], 1)
        self.assertEqual(self.api.stats["app-write"]["writes"], 1)
        for secret in ("read-secret", "write-secret", "other-secret"):
            self.assertNotIn(secret, self.output.getvalue())

    def test_graphql_queries_use_read_credential_and_record_points(self):
        os.environ.update(GH_READ_TOKEN="read-secret", GH_TOKEN="write-secret")
        self.run.return_value = reply(data={"data": {"rateLimit": {"cost": 2}, "repository": {}}},
                                      headers={"X-RateLimit-Resource": "graphql"})
        self.assertEqual(self.api.graphql("query { rateLimit { cost } }", {}),
                         {"rateLimit": {"cost": 2}, "repository": {}})
        self.assertEqual(self.run.call_args.kwargs["env"]["GH_TOKEN"], "read-secret")
        self.assertEqual(self.api.stats["workflow-read"]["graphql_points"], 2)
        self.assertEqual(self.api.stats["workflow-read"]["writes"], 0)

    def test_unchanged_write_decisions_are_counted_without_requests(self):
        rl.apply_label(self.api, "o/r", 1, "roadmap/PDE", {"PDE"}, info()["labels"])
        self.run.assert_not_called()
        self.assertEqual(self.api.stats['gh-default']['requests'], 0)
        self.assertEqual(self.api.stats['gh-default']['skipped_writes'], {'roadmap-label': 1})

    def test_graphql_http_200_exhaustion_is_deferred(self):
        self.run.return_value = reply(data={"errors": [{"message": "API rate limit already exceeded"}]},
                                      headers={"X-RateLimit-Remaining": "0", "X-RateLimit-Resource": "graphql"})
        with self.assertRaises(ga.Deferred):
            self.api.graphql("query { repository { name } }", {})
        self.run.assert_called_once()

    def test_graphql_partial_data_and_schema_errors_are_not_used(self):
        self.run.return_value = reply(data={"data": {"repository": {}},
                                           "errors": [{"message": "Field does not exist"}]})
        with self.assertRaises(ga.APIError):
            self.api.graphql("query { badField }", {})
        self.run.assert_called_once()

    def test_non_json_server_error_on_get_is_retried(self):
        error = subprocess.CompletedProcess([], 1, "HTTP/2.0 502\r\n\r\nBad gateway", "")
        self.run.side_effect = [error, reply(data={})]
        self.assertEqual(self.api.request("GET", "repos/o/r/labels"), {})
        self.assertEqual(self.sleeps, [2])

    def test_transport_failure_retries_reads_and_redacts_diagnostic(self):
        os.environ["GH_TOKEN"] = "secret"
        self.run.return_value = subprocess.CompletedProcess([], 1, "", "connection failed: secret")
        with self.assertRaises(ga.APIError) as caught:
            self.api.request("GET", "repos/o/r/labels")
        self.assertEqual(caught.exception.status, 0)
        self.assertIn("connection failed", str(caught.exception))
        self.assertNotIn("secret", str(caught.exception))
        self.assertEqual(self.run.call_count, 3)
        self.assertEqual(self.sleeps, [2, 4])

    def test_transport_failure_does_not_repeat_ambiguous_post(self):
        self.run.return_value = subprocess.CompletedProcess([], 1, "", "connection reset")
        with self.assertRaises(ga.APIError):
            self.api.request("POST", "repos/o/r/issues/1/comments", {"body": "test"})
        self.run.assert_called_once()

    def test_graphql_timeout_retries_without_using_partial_data(self):
        self.run.side_effect = [reply(data={"errors": [{"message": "Something went wrong: timeout", "type": "INTERNAL"}]}),
                                reply(data={"data": {"repository": {}}})]
        self.assertEqual(self.api.graphql("query { repository { name } }", {}), {"repository": {}})
        self.assertEqual(self.sleeps, [2])

    def test_retry_after_header_is_respected_without_specific_error_wording(self):
        self.run.side_effect = [reply(403, {"message": "Please wait before trying again"}, {"Retry-After": "90"}),
                                reply(data={})]
        self.api.request("GET", "repos/o/r/labels")
        self.assertEqual(self.sleeps, [90])

    def test_invalid_retry_after_falls_back_to_secondary_wait(self):
        self.run.side_effect = [reply(429, {}, {"Retry-After": "invalid date"}), reply(data={})]
        self.api.request("GET", "repos/o/r/labels")
        self.assertEqual(self.sleeps, [60])

    def test_local_auth_does_not_replace_inherited_credential(self):
        os.environ["GH_TOKEN"] = "local"
        self.run.return_value = reply(data={})
        self.api.request("GET", "user")
        self.assertEqual(self.run.call_args.kwargs["env"]["GH_TOKEN"], "local")
        self.assertIn("gh-default", self.api.stats)

    def test_primary_far_reset_defers_without_fast_retries_or_repeated_probes(self):
        self.run.return_value = reply(403, {"message": "API rate limit exceeded for installation ID 143500674"},
                                      {"X-RateLimit-Remaining": "0", "X-RateLimit-Reset": "3000"})
        with self.assertRaises(ga.Deferred) as caught:
            self.api.request("POST", "repos/o/r/labels", {})
        self.assertEqual(caught.exception.until, 3005)
        with self.assertRaises(ga.Deferred):
            self.api.request("GET", "repos/o/r/pulls/2")
        self.run.assert_called_once()
        self.assertEqual(self.sleeps, [])

    def test_primary_near_reset_waits_until_reset_with_margin(self):
        self.run.side_effect = [reply(403, {"message": "API rate limit exceeded"},
                                     {"X-RateLimit-Remaining": "0", "X-RateLimit-Reset": "1010"}), reply(data=[])]
        self.assertEqual(self.api.request("GET", "repos/o/r/labels"), [])
        self.assertEqual(self.sleeps, [15])

    def test_missing_primary_reset_is_conservative(self):
        self.run.return_value = reply(403, {"message": "API rate limit exceeded"}, {"X-RateLimit-Reset": ""})
        with self.assertRaises(ga.Deferred):
            self.api.request("GET", "repos/o/r/labels")
        self.run.assert_called_once()

    def test_retry_after_seconds_and_http_date(self):
        for value in ("90", "Thu, 01 Jan 1970 00:18:10 GMT"):
            with self.subTest(value=value):
                self.clock, self.sleeps = 1000, []
                self.run.side_effect = [reply(429, {"message": "secondary rate limit"}, {"Retry-After": value}),
                                        reply(data={})]
                ga.GitHub().request("GET", "repos/o/r/labels")
                self.assertEqual(self.sleeps, [90])

    def test_secondary_backoff_is_bounded_and_shared_across_calls(self):
        self.run.return_value = reply(403, {"message": "You have exceeded a secondary rate limit"})
        with self.assertRaises(ga.Deferred):
            self.api.request("GET", "repos/o/r/labels")
        self.assertEqual(self.sleeps, [60, 120])
        self.assertEqual(self.run.call_count, 3)
        with self.assertRaises(ga.Deferred):
            self.api.request("GET", "repos/o/r/pulls/1")
        self.assertEqual(self.run.call_count, 3)

    def test_permissions_and_validation_errors_are_not_retried(self):
        for status in (403, 404, 422):
            with self.subTest(status=status):
                self.run.reset_mock()
                self.run.return_value = reply(status, {"message": "Resource not accessible"})
                with self.assertRaises(ga.APIError):
                    ga.GitHub().request("GET", "repos/o/r/labels")
                self.run.assert_called_once()
        self.assertEqual(self.sleeps, [])

    def test_ambiguous_comment_post_is_not_retried_but_get_is(self):
        self.run.return_value = reply(502, {"message": "Bad gateway"})
        with self.assertRaises(ga.APIError):
            self.api.request("POST", "repos/o/r/issues/1/comments", {"body": "test"})
        self.run.assert_called_once()
        self.run.reset_mock()
        self.run.side_effect = [reply(502, {}), reply(data=[])]
        self.api.request("GET", "repos/o/r/issues/1/comments")
        self.assertEqual(self.run.call_count, 2)

    def test_mutations_are_spaced(self):
        self.run.return_value = reply(data={})
        self.api.request("POST", "repos/o/r/issues/1/labels", {})
        self.api.request("DELETE", "repos/o/r/issues/1/labels/old")
        self.assertEqual(self.sleeps, [1])

    def test_all_pages_are_read_with_headers(self):
        self.run.side_effect = [reply(data=list(range(100))), reply(data=[100])]
        self.assertEqual(self.api.items("repos/o/r/pulls?state=open"), list(range(101)))
        self.assertIn("state=open&per_page=100&page=2", self.run.call_args.args[0][-1])
        self.assertEqual(self.api.stats["gh-default"]["requests"], 2)


class Mutations(unittest.TestCase):
    def setUp(self):
        self.api = Mock(known_labels=set())

    def test_correct_label_with_other_labels_is_a_true_no_op(self):
        rl.apply_label(self.api, "o/r", 1, "roadmap/PDE", {"PDE"}, info(labels=("roadmap/PDE", "ready"))["labels"])
        self.api.request.assert_not_called()

    def test_relabel_adds_before_removing_and_preserves_unrelated_labels(self):
        self.api.request.return_value = {}
        rl.apply_label(self.api, "o/r", 1, "roadmap/PDE", {"PDE"}, info(labels=("roadmap/none", "ready"))["labels"])
        calls = [call.args for call in self.api.request.call_args_list]
        self.assertEqual(calls, [("GET", "repos/o/r/labels/roadmap%2FPDE"),
                                ("POST", "repos/o/r/issues/1/labels", {"labels": ["roadmap/PDE"]}),
                                ("DELETE", "repos/o/r/issues/1/labels/roadmap%2Fnone")])

    def test_only_missing_labels_are_created_and_cached(self):
        self.api.request.side_effect = [ga.APIError("GET", "label", 404, {}), {}]
        for _ in range(2):
            rl.ensure_label(self.api, "o/r", "roadmap/PDE", "blue", "desc")
        self.assertEqual(self.api.request.call_count, 2)
        self.assertEqual(self.api.request.call_args.args,
                         ("POST", "repos/o/r/labels", {"name": "roadmap/PDE", "color": "blue", "description": "desc"}))

    def test_probe_failure_does_not_become_missing_label(self):
        self.api.request.side_effect = ga.APIError("GET", "label", 403, {})
        with self.assertRaises(ga.APIError):
            rl.ensure_label(self.api, "o/r", "roadmap/PDE", "blue", "desc")
        self.api.request.assert_called_once()

    def test_concurrent_creation_is_accepted_but_other_validation_errors_are_not(self):
        for code in ("already_exists", "invalid"):
            self.api.request.reset_mock()
            self.api.known_labels.clear()
            self.api.request.side_effect = [ga.APIError("GET", "label", 404, {}),
                                           ga.APIError("POST", "label", 422, {"errors": [{"code": code}]})]
            if code == "already_exists":
                rl.ensure_label(self.api, "o/r", "roadmap/PDE", "blue", "desc")
            else:
                with self.assertRaises(ga.APIError):
                    rl.ensure_label(self.api, "o/r", "roadmap/PDE", "blue", "desc")

    def test_partial_relabel_repairs_stale_labels_without_readding_target(self):
        rl.apply_label(self.api, "o/r", 1, "roadmap/PDE", {"PDE"}, info(labels=("roadmap/PDE", "roadmap/none"))["labels"])
        self.api.request.assert_called_once_with("DELETE", "repos/o/r/issues/1/labels/roadmap%2Fnone")

    def test_label_presentation_is_a_separate_no_op_or_one_patch(self):
        color, desc = rl._label_meta("roadmap/none", set())
        self.api.items.return_value = [
            {"name": "roadmap/none", "color": color, "description": desc},
            {"name": "roadmap/Unknown", "color": rl.UNKNOWN_COLOR,
             "description": rl._label_meta("roadmap/Unknown", set())[1]}]
        rl.sync_labels(self.api, "o/r", set())
        self.api.request.assert_not_called()
        self.api.items.return_value[0]["description"] = "old"
        rl.sync_labels(self.api, "o/r", set())
        self.api.request.assert_called_once_with("PATCH", "repos/o/r/labels/roadmap%2Fnone",
                                                 {"color": color, "description": desc})

    def test_structure_reuses_snapshot_and_skips_identical_comment(self):
        snapshot = {"info": info(), "files": FILES}
        findings = {"TauCeti/FooBar.lean": sn.candidates_for("TauCeti/FooBar.lean", {"TauCeti/Foo.lean"})}
        self.api.items.return_value = [{"id": 42, "body": sn.render_comment("head", findings)}]
        with patch.object(sn, "_local_tree", return_value={"TauCeti/Foo.lean"}), patch.object(sn, "pr_snapshot") as fetch:
            sn.run_pr("o/r", 1, True, api=self.api, snapshot=snapshot)
        fetch.assert_not_called()
        self.api.request.assert_not_called()

    def test_structure_duplicate_cleanup_preserves_human_comments(self):
        snapshot = {"info": info(), "files": FILES}
        findings = {"TauCeti/FooBar.lean": sn.candidates_for("TauCeti/FooBar.lean", {"TauCeti/Foo.lean"})}
        body = sn.render_comment("head", findings)
        bot = {"type": "Bot", "login": "app[bot]"}
        self.api.items.return_value = [{"id": 2, "body": body, "user": bot},
                                      {"id": 3, "body": body, "user": {"type": "User", "login": "human"}},
                                      {"id": 4, "body": body, "user": bot}]
        with patch.object(sn, "_local_tree", return_value={"TauCeti/Foo.lean"}):
            sn.run_pr("o/r", 1, True, api=self.api, snapshot=snapshot)
        self.api.request.assert_called_once_with("DELETE", "repos/o/r/issues/comments/4")

    def test_last_comment_post_collapses_racing_bot_duplicates(self):
        snapshot = {"info": info(), "files": FILES}
        bot = {"type": "Bot", "login": "app[bot]"}
        self.api.items.side_effect = [[], [{"id": 2, "body": sn.MARKER, "user": bot},
                                         {"id": 4, "body": sn.MARKER, "user": bot}]]
        self.api.request.return_value = {"id": 4, "user": bot}
        with patch.object(sn, "_local_tree", return_value={"TauCeti/Foo.lean"}):
            sn.run_pr("o/r", 1, True, api=self.api, snapshot=snapshot)
        self.assertEqual(self.api.request.call_args.args, ("DELETE", "repos/o/r/issues/comments/4"))
        patch_call = self.api.request.call_args_list[1].args
        self.assertEqual(patch_call[:2], ("PATCH", "repos/o/r/issues/comments/2"))
        self.assertIn("analyzed head `head`", patch_call[2]["body"])

    def test_expected_bot_actor_does_not_patch_or_delete_a_human_marker(self):
        snapshot = {"info": info(), "files": FILES}
        self.api.items.return_value = [{"id": 2, "body": sn.MARKER, "user": {"type": "User", "login": "human"}}]
        with patch.dict(os.environ, GH_COMMENT_AUTHOR="app[bot]"), patch.object(sn, "_local_tree", return_value={"TauCeti/Foo.lean"}):
            sn.run_pr("o/r", 1, True, api=self.api, snapshot=snapshot)
        self.assertEqual(self.api.request.call_args.args[0], "POST")

    def test_large_structure_comment_is_bounded_without_losing_marker(self):
        candidate = sn.candidates_for("TauCeti/FooBar.lean", {"TauCeti/Foo.lean"})
        body = sn.render_comment("head", {f"TauCeti/Foo{i}.lean": candidate for i in range(500)})
        self.assertLessEqual(len(body.encode("utf-8")), 60000)
        self.assertIn(sn.MARKER, body)
        self.assertIn("Further findings omitted", body)


class Recovery(unittest.TestCase):
    def args(self, **kwargs):
        values = dict(repo="o/r", since="2026-10-12T00:00:00Z", reconcile_open=True,
                      backfill=False, apply=True, allow_relabel=False, limit=5000, pr=None)
        return argparse.Namespace(**(values | kwargs))

    def test_old_missing_invalid_and_multiple_labels_are_repaired(self):
        api = Mock()
        old = "2026-10-11T00:00:00Z"
        api.pages.return_value = [[info(1), info(2, updated=old), info(3, (), old),
                                   info(4, ("roadmap/Removed",), old),
                                   info(5, ("roadmap/PDE", "roadmap/none"), old)]]
        self.assertEqual(list(rl.candidates(api, self.args(), {"PDE"})), [1, 3, 4, 5])

    def test_watermark_is_previous_success_start_and_initial_scan_is_complete(self):
        api = Mock()
        api.request.return_value = {"workflow_runs": [{"run_started_at": "2026-10-12T00:00:00Z"}]}
        self.assertEqual(rl.recovery_since(api, "o/r"), "2026-10-11T23:58:00Z")
        self.assertIn("status=success", api.request.call_args.args[1])
        api.request.return_value = {"workflow_runs": []}
        self.assertEqual(rl.recovery_since(api, "o/r"), "1970-01-01T00:00:00Z")

    def test_listing_cap_fails_instead_of_advancing_incomplete_window(self):
        api = Mock()
        api.pages.return_value = [[info(1), info(2)]]
        with self.assertRaisesRegex(RuntimeError, "listing reached"):
            list(rl.candidates(api, self.args(limit=1), {"PDE"}))

    def test_historical_backfill_honors_an_intentional_limit(self):
        api = Mock()
        api.pages.return_value = [[info(1), info(2)]]
        self.assertEqual(list(rl.candidates(api, self.args(limit=1, reconcile_open=False,
                                                         backfill=True, apply=False), {"PDE"})), [1])

    def test_snapshot_retries_a_changed_head_and_rejects_incomplete_diff(self):
        api = Mock()
        old, changed = graph_row(), graph_row(head="new")
        old["files"]["pageInfo"] = {"hasNextPage": True, "endCursor": "cursor"}
        api.graphql.side_effect = [graph_result(old), graph_result(changed), graph_result(changed)]
        self.assertEqual(ga.pr_snapshot(api, "o/r", 1)["info"]["head"]["sha"], "new")
        changed["changedFiles"] = 2
        api.graphql.side_effect = [graph_result(changed)]
        self.assertTrue(ga.pr_snapshot(api, "o/r", 1)["info"]["incomplete_files"])

    def test_snapshot_combines_file_pages_and_includes_latest_labels(self):
        api = Mock()
        first, second = graph_row(), graph_row()
        for row in (first, second):
            row["changedFiles"] = row["files"]["totalCount"] = 2
        first["files"]["pageInfo"] = {"hasNextPage": True, "endCursor": "next"}
        second["files"]["nodes"] = [{"path": "scripts/infra.py", "changeType": "ADDED"}]
        second["labels"]["nodes"] = [{"name": "roadmap/none"}]
        api.graphql.side_effect = [graph_result(first), graph_result(second)]
        snapshot = ga.pr_snapshot(api, "o/r", 1)
        self.assertEqual([row["filename"] for row in snapshot["files"]],
                         ["TauCeti/FooBar.lean", "scripts/infra.py"])
        self.assertEqual(snapshot["info"]["labels"], [{"name": "roadmap/none"}])
        self.assertEqual(api.graphql.call_args.args[1]["after"], "next")

    def test_snapshot_fetches_labels_beyond_first_page(self):
        api = Mock()
        row = graph_row()
        row["labels"]["pageInfo"]["hasNextPage"] = True
        api.graphql.return_value = graph_result(row)
        api.items.return_value = [{"name": "roadmap/PDE"}]
        self.assertEqual(ga.pr_snapshot(api, "o/r", 1)["info"]["labels"], api.items.return_value)
        api.items.assert_called_once_with("repos/o/r/issues/1/labels")

    def test_historical_bulk_reads_many_prs_without_individual_snapshots(self):
        api = Mock()
        rows = [dict(graph_row(), number=number) for number in (1, 2)]
        api.graphql.return_value = {"repository": {"pullRequests": {"nodes": rows,
                                  "pageInfo": {"hasNextPage": False, "endCursor": "last"}}}}
        with patch.object(ga, "pr_snapshot") as single:
            results = list(ga.history_snapshots(api, "o/r", 2))
        self.assertEqual([pr for pr, _ in results], [1, 2])
        api.graphql.assert_called_once()
        single.assert_not_called()
        self.assertIn("CREATED_AT", api.graphql.call_args.args[0])

    def test_historical_bulk_falls_back_only_for_a_paginated_diff(self):
        api = Mock()
        row = dict(graph_row(), number=1)
        row["files"]["pageInfo"]["hasNextPage"] = True
        api.graphql.return_value = {"repository": {"pullRequests": {"nodes": [row],
                                  "pageInfo": {"hasNextPage": False, "endCursor": "last"}}}}
        with patch.object(ga, "pr_snapshot", return_value={"info": info(), "files": FILES}) as single:
            self.assertEqual(list(ga.history_snapshots(api, "o/r", 1))[0][1]["files"], FILES)
        single.assert_called_once_with(api, "o/r", 1)

    def test_one_failing_history_fallback_does_not_abandon_other_prs(self):
        api = Mock()
        rows = [dict(graph_row(), number=number) for number in (1, 2)]
        rows[0]["files"]["pageInfo"]["hasNextPage"] = True
        api.graphql.return_value = {"repository": {"pullRequests": {"nodes": rows,
                                  "pageInfo": {"hasNextPage": False, "endCursor": "last"}}}}
        error = ga.APIError("POST", "graphql", 503, {"message": "bad PR"})
        with patch.object(ga, "pr_snapshot", side_effect=error):
            results = list(ga.history_snapshots(api, "o/r", 2))
        self.assertIs(results[0][1], error)
        self.assertIsInstance(results[1][1], dict)

    def test_file_cap_returns_a_partial_snapshot_without_unbounded_queries(self):
        api = Mock()
        row = graph_row()
        row["changedFiles"] = row["files"]["totalCount"] = 3001
        row["files"]["nodes"] = [{"path": f"TauCeti/File{i}.lean", "changeType": "ADDED"} for i in range(100)]
        row["files"]["pageInfo"] = {"hasNextPage": True, "endCursor": "unused"}
        count = 0
        def fetch(*_):
            nonlocal count
            count += 1
            copy_row = copy.deepcopy(row)
            copy_row["files"]["pageInfo"]["endCursor"] = str(count)
            return graph_result(copy_row)
        api.graphql.side_effect = fetch
        snapshot = ga.pr_snapshot(api, "o/r", 1)
        self.assertEqual(api.graphql.call_count, 30)
        self.assertEqual(len(snapshot["files"]), 3000)
        self.assertTrue(snapshot["info"]["incomplete_files"])

    def test_deferred_run_fails_and_stops_remaining_items(self):
        api = Mock()
        with tempfile.TemporaryDirectory() as directory:
            area = Path(directory) / "PDE"
            area.mkdir()
            (area / "README.md").touch()
            with patch.object(rl, "GitHub", return_value=api), \
                 patch.object(rl, "candidates", return_value=iter([1, 2])), \
                 patch.object(rl, "run_pr", side_effect=ga.Deferred("app-write", 2000)) as run:
                self.assertEqual(rl.main(["--roadmap-dir", directory, "--reconcile-open", "--apply"]), 1)
            run.assert_called_once()
            api.report.assert_called_once()

    def test_all_candidates_are_listed_before_writes_and_item_failure_fails_pass(self):
        api = Mock()
        order = []
        def listing(*_):
            for pr in (1, 2):
                order.append(f"list {pr}")
                yield pr
        def process(_api, _args, _areas, pr):
            order.append(f"write {pr}")
            if pr == 1:
                raise RuntimeError("failed item")
        with tempfile.TemporaryDirectory() as directory:
            area = Path(directory) / "PDE"
            area.mkdir()
            (area / "README.md").touch()
            with (patch.object(rl, "GitHub", return_value=api),
                  patch.object(rl, "candidates", side_effect=listing),
                  patch.object(rl, "run_pr", side_effect=process)):
                self.assertEqual(rl.main(["--roadmap-dir", directory, "--reconcile-open", "--apply"]), 1)
        self.assertEqual(order, ["list 1", "list 2", "write 1", "write 2"])

    def test_advisory_rate_limit_cannot_advance_recovery_watermark(self):
        args = self.args(structure_nudge=True, nudge=False)
        api = Mock()
        with patch.object(rl, "pr_snapshot", return_value={"info": info(), "files": FILES}), \
             patch.object(sn, "run_pr", side_effect=ga.Deferred("app-write", 2000)):
            with self.assertRaises(ga.Deferred):
                rl.run_pr(api, args, {"PDE"}, 1)
            args.reconcile_open = False
            self.assertEqual(rl.run_pr(api, args, {"PDE"}, 1), "roadmap/PDE")

    def test_historical_backfill_never_posts_attribution_nudges(self):
        args = self.args(structure_nudge=False, nudge=True, backfill=True)
        snapshot = {"info": dict(info(labels=()), body="", state="closed"), "files": FILES}
        with patch.object(rl, "pr_snapshot", return_value=snapshot), patch.object(rl, "apply_label"), patch.object(rl, "nudge") as nudge:
            rl.run_pr(Mock(), args, {"PDE"}, 1)
        nudge.assert_not_called()

    def test_incomplete_diff_labels_only_proven_infra_and_skips_structure(self):
        args = self.args(structure_nudge=True, nudge=False)
        for files, target in ((FILES, "roadmap/Unknown"),
                              ([{"filename": "scripts/infra.py"}], "roadmap/none"), ([], "roadmap/Unknown")):
            snapshot = {"info": dict(info(), incomplete_files=True), "files": files}
            with patch.object(rl, "pr_snapshot", return_value=snapshot), patch.object(rl, "apply_label"), patch.object(sn, "run_pr") as structure:
                self.assertEqual(rl.run_pr(Mock(), args, {"PDE"}, 1), target)
            structure.assert_not_called()

    def test_cached_success_skips_status_comment_churn_but_not_changed_inputs(self):
        state = rl.RecoveryState()
        original = info()
        key = rl.input_key(original, {"PDE"})
        state.success(1, "roadmap/PDE", key)
        self.assertFalse(state.select(dict(original, updated_at="2030-01-01T00:00:00Z"), {"PDE"}))
        self.assertTrue(state.select(dict(original, body="Roadmap: none"), {"PDE"}))

    def test_cache_uses_actual_processed_inputs_not_the_earlier_listing(self):
        args = self.args(structure_nudge=False, nudge=False)
        processed = dict(info(labels=("roadmap/none",)), body="Roadmap: none")
        with patch.object(rl, "pr_snapshot", return_value={"info": processed, "files": FILES}):
            label = rl.run_pr(Mock(), args, {"PDE"}, 1)
        state = rl.RecoveryState()
        state.success(1, label, args._processed_key)
        self.assertFalse(state.select(processed, {"PDE"}))
        reverted = dict(processed, body="Roadmap: PDE")
        self.assertTrue(state.select(reverted, {"PDE"}))

    def test_changed_roadmap_label_is_repaired_outside_the_window(self):
        state = rl.RecoveryState()
        original = info(updated="2000-01-01T00:00:00Z")
        state.success(1, "roadmap/PDE", rl.input_key(original, {"PDE"}))
        self.assertTrue(state.select(dict(original, labels=[{"name": "roadmap/none"}]), {"PDE"}))

    def test_retry_handoff_is_bounded_and_resets_on_new_head(self):
        state = rl.RecoveryState()
        original = info()
        for _ in range(rl.MAX_RETRIES):
            self.assertTrue(state.select(original, {"PDE"}))
            state.failure(1, RuntimeError("bad PR"))
        self.assertFalse(state.select(original, {"PDE"}))
        changed = dict(original, head={"sha": "new"})
        self.assertTrue(state.select(changed, {"PDE"}))
        state.failure(1, RuntimeError("bad PR"))
        self.assertEqual(state.records[1]["attempts"], 1)

    def test_server_failure_exhaustion_resumes_automatically_after_cooldown(self):
        state = rl.RecoveryState()
        original = info()
        with patch.object(rl.time, "time", return_value=1000):
            for _ in range(rl.MAX_RETRIES):
                state.select(original, {"PDE"})
                state.failure(1, ga.APIError("POST", "graphql", 503, {"message": "service unavailable"}))
            self.assertFalse(state.select(original, {"PDE"}))
        with patch.object(rl.time, "time", return_value=1000 + 6 * 3600):
            self.assertTrue(state.select(original, {"PDE"}))
        self.assertNotIn(1, state.records)

    def test_uncached_old_valid_pr_is_recovered_after_a_listing_race(self):
        args = self.args(_state=rl.RecoveryState())
        api = Mock()
        api.pages.return_value = [[info(updated="2000-01-01T00:00:00Z")]]
        self.assertEqual(list(rl.candidates(api, args, {"PDE"})), [1])

    def test_state_round_trip_prunes_closed_prs_and_has_no_body_text(self):
        state = rl.RecoveryState()
        original = dict(info(), body="sensitive body text")
        state.select(original, {"PDE"})
        state.failure(1, RuntimeError("bad PR"))
        state.success(2, "roadmap/PDE", rl.input_key(info(2), {"PDE"}))
        state.listed = True
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "state.json"
            state.save(path)
            self.assertNotIn("sensitive body text", path.read_text())
            restored = rl.RecoveryState(path)
            self.assertEqual(set(restored.records), {1})
            self.assertTrue(restored.select(original, {"PDE"}))
            self.assertEqual(rl.RecoveryState(path, reset=True).records, {})

    def test_manual_full_scan_recovers_from_corrupt_state(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "state.json"
            path.write_text("invalid JSON")
            self.assertEqual(rl.RecoveryState(path, reset=True).records, {})

    def test_recovery_rejects_invalid_retry_timestamps_before_selection(self):
        invalid = (None, "x", True, [], {}, -1, float("nan"), float("inf"), -float("inf"))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "state.json"
            for retry_at in invalid:
                with self.subTest(retry_at=retry_at):
                    record = {"key": rl.input_key(info(), {"PDE"}),
                              "attempts": rl.MAX_RETRIES, "retry_at": retry_at}
                    path.write_text(json.dumps({"version": 1, "prs": {"1": record}}))
                    with self.assertRaisesRegex(RuntimeError, "invalid recovery retry timestamp"):
                        rl.RecoveryState(path)
                    self.assertEqual(rl.RecoveryState(path, reset=True).records, {})

    def test_recovery_loads_finite_retry_timestamps_and_resumes_when_due(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "state.json"
            for retry_at in (0, 1000, 1000.5):
                with self.subTest(retry_at=retry_at):
                    record = {"key": rl.input_key(info(), {"PDE"}),
                              "attempts": rl.MAX_RETRIES, "retry_at": retry_at}
                    path.write_text(json.dumps({"version": 1, "prs": {"1": record}}))
                    restored = rl.RecoveryState(path)
                    with patch.object(rl.time, "time", return_value=1001):
                        self.assertTrue(restored.select(info(), {"PDE"}))
                    self.assertNotIn(1, restored.records)

    def test_restore_only_selects_trusted_main_schedule_and_dispatch_runs(self):
        root = Path(__file__).resolve().parents[1]
        workflow = (root / ".github/workflows/roadmap-label-reconcile.yml").read_text()
        step = workflow.split("      - name: Restore recovery state\n", 1)[1].split("\n      - ", 1)[0]
        selector = re.search(r"--jq '([^']+)'", step).group(1)
        self.assertIn("status=completed&branch=main", step)
        trusted = {"head_branch": "main", "head_repository": {"full_name": "TauCetiProject/TauCeti"}}
        runs = [dict(trusted, id=1, event="pull_request"),
                dict(trusted, id=2, event="pull_request_target"),
                dict(trusted, id=3, event="push"),
                dict(trusted, id=4, event="schedule", head_repository={"full_name": "fork/TauCeti"}),
                dict(trusted, id=5, event="workflow_dispatch", head_repository={"full_name": "fork/TauCeti"}),
                dict(trusted, id=6, event="workflow_dispatch", head_branch="feature"),
                dict(trusted, id=7, event="schedule", head_repository=None),
                dict(trusted, id=8, event="schedule"),
                dict(trusted, id=9, event="workflow_dispatch")]
        result = subprocess.run(["jq", "-r", selector], input=json.dumps({"workflow_runs": runs}),
                                capture_output=True, text=True, check=True)
        self.assertEqual(result.stdout.splitlines(), ["8", "9"])

    def test_bad_pr_does_not_fail_recovery_window_when_retry_handoff_is_saved(self):
        api = Mock()
        api.pages.return_value = [[info(1), info(2)]]
        def process(_api, args, areas, pr):
            if pr == 1:
                raise RuntimeError("persistent bad PR")
            args._processed_key = rl.input_key(info(2), areas)
            return "roadmap/PDE"
        with tempfile.TemporaryDirectory() as directory:
            area = Path(directory) / "PDE"
            area.mkdir()
            (area / "README.md").touch()
            path = Path(directory) / "state.json"
            with patch.object(rl, "GitHub", return_value=api), patch.object(rl, "run_pr", side_effect=process):
                self.assertEqual(rl.main(["--roadmap-dir", directory, "--reconcile-open", "--since", "1970-01-01T00:00:00Z", "--apply", "--state-out", str(path)]), 0)
            records = json.loads(path.read_text())["prs"]
            self.assertEqual(records["1"]["attempts"], 1)
            self.assertEqual(records["2"]["attempts"], 0)

    def test_temporary_incomplete_diff_is_queued_instead_of_cached_success(self):
        for capped, attempts in ((False, 1), (True, 0)):
            with self.subTest(capped=capped), tempfile.TemporaryDirectory() as directory:
                area = Path(directory) / "PDE"
                area.mkdir()
                (area / "README.md").touch()
                api = Mock(known_labels=set())
                api.pages.return_value = [[info()]]
                snapshot = {"info": dict(info(labels=("roadmap/Unknown",)),
                            incomplete_files=True, files_capped=capped), "files": FILES}
                path = Path(directory) / "state.json"
                with patch.object(rl, "GitHub", return_value=api), patch.object(rl, "pr_snapshot", return_value=snapshot):
                    self.assertEqual(rl.main(["--roadmap-dir", directory, "--reconcile-open", "--apply", "--state-out", str(path)]), 0)
                record = json.loads(path.read_text())["prs"]["1"]
                self.assertEqual(record["attempts"], attempts)
                if not capped:
                    self.assertNotIn("label", record)

    def test_state_mode_does_not_read_unused_window_and_lists_by_creation(self):
        args = self.args(since="auto", _state=rl.RecoveryState())
        api = Mock()
        api.pages.return_value = [[info()]]
        with patch.object(rl, "recovery_since") as since:
            self.assertEqual(list(rl.candidates(api, args, {"PDE"})), [1])
        since.assert_not_called()
        self.assertIn("sort=created", api.pages.call_args.args[0])

    def test_workflow_preserves_app_writes_and_filters_title_edits(self):
        root = Path(__file__).resolve().parents[1]
        event = (root / ".github/workflows/roadmap-label.yml").read_text()
        recovery = (root / ".github/workflows/roadmap-label-reconcile.yml").read_text()
        for workflow in (event, recovery):
            self.assertIn("GH_READ_TOKEN: ${{ github.token }}", workflow)
            self.assertIn("GH_TOKEN: ${{ steps.app-token.outputs.token }}", workflow)
            self.assertIn("--structure-nudge", workflow)
            self.assertNotIn("github.event.pull_request.head.sha", workflow)
        self.assertIn("github.event.changes.body != null", event)
        self.assertIn("roadmap-label-ignored-{0}", event)
        self.assertIn("github.run_id", event)
        self.assertLess(event.index("run: sleep 20"), event.index("actions/create-github-app-token"))
        self.assertIn("actions: read", recovery)
        self.assertIn("ref: main", recovery)
        self.assertIn("cancel-in-progress: false", recovery)
        self.assertIn("--state-out", recovery)
        self.assertIn("if: always()", recovery)


if __name__ == "__main__":
    unittest.main()
