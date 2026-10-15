"""Real Git fixtures and mutation/race tests; no network or Lean execution."""

import copy
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch, MagicMock

import stack_policy as sp


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.DEVNULL).decode().strip()


class GitFixtures(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "repo"
        self.root.mkdir()
        git(self.root, "init", "-b", "main")
        git(self.root, "config", "user.name", "Fixture")
        git(self.root, "config", "user.email", "fixture@example.invalid")
        self.write("common", "main ancestor\n")
        self.base = self.commit("base")
        self.prs = []

    def write(self, path, text):
        (self.root / path).write_text(text)

    def commit(self, title):
        git(self.root, "add", ".")
        git(self.root, "commit", "-m", title)
        return git(self.root, "rev-parse", "HEAD")

    def pr(self, number, body="", *, draft=False, fork=True, base="main", state="open"):
        head = git(self.root, "rev-parse", "HEAD")
        git(self.root, "update-ref", f"refs/pull/{number}/head", head)
        p = sp.PR(number, state, head, base, f"branch-{number}",
                  "fork/TauCeti" if fork else sp.REPO, body, draft)
        self.prs.append(p)
        return p

    def detector(self):
        main = git(self.root, "rev-parse", "main")
        src = sp.Source(Path(self.tmp.name) / "source", None, main,
                        self.root / ".git/objects", str(self.root))
        src.fetch(self.prs)
        return sp.Detector(None, src, self.prs)

    def parent_child(self, *, draft=False, explicit=False):
        git(self.root, "checkout", "-b", "parent")
        self.write("parent", "prerequisite\n")
        self.commit("prerequisite")
        parent = self.pr(1)
        git(self.root, "checkout", "-b", "child")
        self.write("child", "own change\n")
        self.commit("own change")
        child = self.pr(2, "Stacked on #1" if explicit else "", draft=draft)
        return parent, child

    def test_ancestor_head_draft_fork(self):
        parent, child = self.parent_child(draft=True)
        evidence, _ = self.detector().detect(child)
        self.assertEqual(evidence.kind, "ancestor-head")
        self.assertEqual(evidence.commit, parent.head)
        self.assertIn("branch is preserved", sp.comment_text(evidence))

    def test_do_not_reverse_stack_and_close_its_standalone_parent(self):
        parent, _ = self.parent_child()
        self.assertIsNone(self.detector().detect(parent)[0])

    def test_nested_stack(self):
        self.parent_child()
        self.write("third", "third\n")
        self.commit("third")
        child = self.pr(3)
        self.assertIsNotNone(self.detector().detect(child)[0])

    def test_child_edits_aggregate_but_retains_complete_unlanded_commit(self):
        git(self.root, "checkout", "-b", "parent")
        self.write("parent-one", "first contribution\n")
        self.commit("first parent change")
        self.write("parent-two", "second contribution\n")
        commit = self.commit("second parent change")
        self.pr(1)
        git(self.root, "checkout", "-b", "child")
        self.write("parent-one", "edited by child\n")
        self.commit("child edits first change")
        child = self.pr(2, "Stacked on #1")
        evidence, _ = self.detector().detect(child)
        self.assertEqual(evidence.kind, "retained-unmerged-commit")
        self.assertEqual(evidence.commit, commit)

    def test_common_main_ancestry_is_not_stack(self):
        self.parent_child()
        git(self.root, "checkout", "main")
        git(self.root, "checkout", "-b", "independent")
        self.write("different", "independent\n")
        self.commit("independent")
        p = self.pr(3)
        self.assertIsNone(self.detector().detect(p)[0])

    def merged_parent(self, retain_one):
        git(self.root, "checkout", "-b", "parent")
        self.write("one", "first parent contribution\n")
        first = self.commit("one")
        self.write("two", "second parent contribution\n")
        self.commit("two")
        git(self.root, "checkout", "main")
        self.write("main-drift", "new main work\n")
        self.commit("main advances")
        git(self.root, "checkout", "parent")
        git(self.root, "merge", "--no-ff", "main", "-m", "merge main into parent")
        self.pr(1)
        git(self.root, "checkout", "-b", "child")
        self.write("two", "child replaces second contribution\n")
        if not retain_one:
            self.write("one", "child replaces first contribution\n")
        self.commit("child")
        return self.pr(2), first

    def test_merge_head_does_not_hide_supported_retained_commit(self):
        child, first = self.merged_parent(True)
        self.assertEqual(self.detector().detect(child)[0].commit, first)

    def test_unsupported_merge_without_alternative_proof_stays_unknown(self):
        child, _ = self.merged_parent(False)
        with self.assertRaisesRegex(sp.Gap, "no alternative retained commit proof"):
            self.detector().detect(child)

    def test_independent_same_file(self):
        git(self.root, "checkout", "-b", "one")
        self.write("common", "independent one\n")
        self.commit("one")
        self.pr(1)
        git(self.root, "checkout", "main")
        git(self.root, "checkout", "-b", "two")
        self.write("common", "independent two\n")
        self.commit("two")
        child = self.pr(2)
        self.assertIsNone(self.detector().detect(child)[0])

    def test_old_main_content_is_not_a_rebased_parent_restore(self):
        for restores_file in (True, False):
            with self.subTest(restores_file=restores_file):
                self.setUp()
                if restores_file:
                    self.write("G", "original main content\n")
                    self.commit("old main has G")
                git(self.root, "checkout", "-b", "child")
                self.write("own", "child's independent change\n")
                self.commit("own work")
                child = self.pr(2, "Depends on #1")
                git(self.root, "checkout", "main")
                if restores_file:
                    git(self.root, "rm", "G")
                else:
                    self.write("G", "new main content\n")
                self.commit("main changes G")
                git(self.root, "checkout", "-b", "parent")
                if restores_file:
                    self.write("G", "original main content\n")
                else:
                    git(self.root, "rm", "G")
                self.commit("parent reverses main's change")
                self.pr(1)
                with self.assertRaisesRegex(sp.Gap, "fork point; base drift"):
                    self.detector().detect(child)

    def test_parent_landed_normally(self):
        parent, child = self.parent_child(explicit=True)
        git(self.root, "update-ref", "refs/heads/main", parent.head)
        self.assertIsNone(self.detector().detect(child)[0])

    def test_parent_landed_by_bors_squash_then_changed_again(self):
        _, child = self.parent_child(explicit=True)
        git(self.root, "checkout", "main")
        git(self.root, "merge", "--squash", "parent")
        self.commit("bors squash")
        self.write("parent", "later modification\n")
        self.commit("later change")
        evidence, reasons = self.detector().detect(child)
        self.assertIsNone(evidence)
        self.assertTrue(any("source equivalent landed" in r for r in reasons))

    def retained_then_reverted_parent(self, landed_aggregate, *, body_only=False):
        git(self.root, "checkout", "-b", "parent")
        self.write("A", "unlanded prerequisite\n")
        added = self.commit("add A")
        git(self.root, "checkout", "-b", "child")
        self.write("child", "own work\n")
        self.commit("child retains A")
        child = self.pr(2, "Stacked on #1", base="main" if body_only else "branch-1")
        git(self.root, "checkout", "parent")
        git(self.root, "revert", "--no-edit", added)
        if landed_aggregate:
            self.write("B", "independently landed\n")
            last = self.commit("add B")
        self.pr(1, fork=False)
        if landed_aggregate:
            git(self.root, "checkout", "main")
            git(self.root, "cherry-pick", last)
        if body_only:
            with self.assertRaises(sp.Gap):
                self.detector().detect(child)
            return
        evidence, _ = self.detector().detect(child)
        self.assertEqual(evidence.kind, "retained-unmerged-commit")
        self.assertEqual(evidence.commit, added)

    def test_empty_parent_aggregate_still_checks_retained_commits(self):
        self.retained_then_reverted_parent(False)

    def test_landed_parent_aggregate_still_checks_retained_commits(self):
        self.retained_then_reverted_parent(True)

    def test_body_only_reverted_parent_has_ambiguous_direction(self):
        self.retained_then_reverted_parent(False, body_only=True)

    def test_parent_parts_landed_separately_never_together_are_not_unmerged_work(self):
        git(self.root, "checkout", "-b", "parent")
        self.write("A", "parent A\n")
        self.commit("parent adds A")
        self.write("B", "parent B\n")
        self.commit("parent adds B")
        self.pr(1)
        git(self.root, "checkout", "-b", "child")
        self.write("child", "own change\n")
        self.commit("child")
        child = self.pr(2, "Stacked on #1")
        git(self.root, "checkout", "main")
        self.write("A", "parent A\n")
        first = self.commit("squash A independently")
        git(self.root, "revert", "--no-edit", first)
        self.write("B", "parent B\n")
        self.commit("squash B independently")
        self.assertIsNone(self.detector().detect(child)[0])

    def test_landed_squash_with_changed_context_is_unknown_never_closed(self):
        self.write("file", "context before\nold value\ncontext after\n")
        self.commit("context base")
        git(self.root, "checkout", "-b", "parent")
        self.write("file", "context before\nparent value\ncontext after\n")
        self.commit("parent")
        parent = self.pr(1, state="closed")
        git(self.root, "checkout", "-b", "child")
        self.write("child", "own work\n")
        self.commit("child")
        child = self.pr(2, "Stacked on #1")
        git(self.root, "checkout", "main")
        self.write("file", "changed context\nold value\ncontext after\n")
        self.commit("main context drift")
        self.write("file", "changed context\nparent value\ncontext after\n")
        self.commit("squash parent on new main")
        with self.assertRaisesRegex(sp.Gap, "possible landed content"):
            self.detector().detect(child)

    def test_closed_parent_discovered_by_other_child_does_not_bleed_into_shared_index(self):
        parent, child = self.parent_child()
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "state": "closed"})
        # This child adopts the closed source; only an unrelated third PR names it.
        self.write("third", "unrelated\n")
        self.commit("third")
        self.pr(3, "Depends on #1")
        detector = self.detector()
        self.assertNotIn(parent.number, detector.index[parent.head])
        self.assertIsNone(detector.detect(child)[0])

    def test_closed_but_unlanded_parent(self):
        parent, child = self.parent_child(explicit=True)
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "state": "closed"})
        self.assertIsNotNone(self.detector().detect(child)[0])

    def test_closed_landing_claim_without_source_proof_is_unknown_not_assumed_landed(self):
        parent, child = self.parent_child(explicit=True)
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "state": "closed", "landing_claim": True})
        with self.assertRaisesRegex(sp.Gap, "reports landing"):
            self.detector().detect(child)

    def test_stale_description_and_reverted_inheritance(self):
        _, child = self.parent_child(explicit=True)
        git(self.root, "rm", "parent")
        self.commit("remove prerequisite")
        self.prs.pop()
        child = self.pr(2, child.body)
        self.assertIsNone(self.detector().detect(child)[0])

    def test_cherry_pick_identity_with_explicit_parent(self):
        parent, _ = self.parent_child()
        self.prs.pop()
        git(self.root, "checkout", "main")
        git(self.root, "checkout", "-b", "rebased")
        self.write("unrelated", "different fork point\n")
        self.commit("advance")
        git(self.root, "cherry-pick", parent.head)
        self.write("child", "own change\n")
        self.commit("child")
        child = self.pr(2, "This PR is stacked on #1.")
        evidence, _ = self.detector().detect(child)
        self.assertEqual(evidence.kind, "explicit-parent-content")

    def test_open_head_branch_parent(self):
        parent, child = self.parent_child()
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "head_repo": sp.REPO})
        child = sp.PR(**{**sp.asdict(child), "base": parent.branch})
        self.prs[1] = child
        self.assertIsNotNone(self.detector().detect(child)[0])

    def test_non_main_base_alone_is_not_evidence(self):
        self.parent_child()
        git(self.root, "checkout", "main")
        git(self.root, "checkout", "-b", "standalone")
        self.write("standalone", "independent\n")
        self.commit("independent")
        child = self.pr(3, base="branch-1")
        self.assertIsNone(self.detector().detect(child)[0])

    def test_identical_heads_are_not_proof(self):
        self.parent_child()
        self.prs = self.prs[1:]
        child = self.pr(3)
        self.assertIsNone(self.detector().detect(child)[0])

    def test_incomplete_history_is_unknown(self):
        _, child = self.parent_child()
        detector = self.detector()
        detector.gaps[child.number] = "incomplete history"
        with self.assertRaises(sp.Gap):
            detector.detect(child)

    def test_changed_head_during_fetch_is_unknown(self):
        _, child = self.parent_child()
        self.write("race", "new head\n")
        self.commit("head changed")
        git(self.root, "update-ref", "refs/pull/2/head", "HEAD")
        with self.assertRaises(sp.Gap):
            self.detector().detect(child)


class ProseTests(unittest.TestCase):
    def test_read_only_historical_explicit_examples(self):
        fixtures = json.loads((Path(__file__).with_name("stack_policy_fixtures.json")).read_text())
        expected = {"16755": {16515}, "16656": {16643, 16632, 15253},
                    "16613": {16611}, "16130": {15856, 16035}}
        for number, parents in expected.items():
            item = fixtures["explicit_prose"][number]
            self.assertEqual(sp.oid(item["head"]), item["head"])
            self.assertEqual(sp.explicit_parents("\n".join(item["body_lines"])), parents)

    def test_affirmative_parent_identity(self):
        self.assertEqual(sp.explicit_parents("This PR is stacked on #12 (#11)."), {11, 12})
        self.assertEqual(sp.explicit_parents(f"Stacked on https://github.com/{sp.REPO}/pull/12"), {12})
        self.assertEqual(sp.explicit_parents("Prerequisite: #12"), {12})

    def test_superseding_closed_source_is_not_a_stack_claim(self):
        self.assertFalse(sp.explicit_parents(
            "Includes the prerequisite source from #12. This PR supersedes that standalone foundation."))
        self.assertFalse(sp.explicit_parents(
            "Includes #12 (a composition theorem, which depends on #11). This PR supersedes them."))
        self.assertEqual(sp.explicit_parents(
            "Prerequisite: #12. This PR includes #11 and supersedes it."), {12})

    def test_misleading_quoted_negative_and_foreign_prose(self):
        for body in ["> Stacked on #12", "```\nStacked on #12\n```", "Not stacked on #12",
                     "This was stacked on #12", '`Stacked on #12`', 'The title is "stacked on #12"',
                     '“Stacked on #12”', "'Stacked on #12'", "    Stacked on #12", "``Stacked on #12``",
                     "Prerequisites: none; #12 will build on this", "Depends on Mathlib PR #12",
                     "<!-- Stacked on #12 -->", "Stacked on https://github.com/other/repo/pull/12"]:
            with self.subTest(body=body):
                self.assertFalse(sp.explicit_parents(body))


class FakeAPI:
    def __init__(self, child, parent, main):
        self.prs = {child.number: child, parent.number: parent}
        self.sha = main
        self.comments = []
        self.calls = []
        self.fail_comment = False
        self.fail_close = False
        self.race = None
        self.labels = set()
        self.events = []

    def main(self):
        return self.sha

    def pr(self, n):
        return self.prs[n]

    def pages(self, path, limit):
        if path.endswith("/comments"):
            return copy.deepcopy(self.comments)
        if path.endswith("/labels"):
            return [{"name": label} for label in sorted(self.labels)]
        if path.endswith("/events"):
            return self.events
        raise AssertionError(f"unexpected page path: {path}")

    def call(self, path, method="GET", data=None):
        self.calls.append((path, method, data))
        if path.endswith("/labels") and method == "POST":
            self.labels.update(data["labels"])
        if path.endswith("/comments"):
            if self.fail_comment:
                raise sp.Gap("comment permission/rate limit")
            self.comments.append({"id": len(self.comments) + 1,
                                  "user": {"login": "trusted[bot]"}, "body": data["body"]})
            if self.race:
                self.race()
        if path.startswith("issues/comments/"):
            number = int(path.rsplit("/", 1)[1])
            next(c for c in self.comments if c["id"] == number)["body"] = data["body"]
        if path.startswith("pulls/") and method == "PATCH" and self.fail_close:
            raise sp.Gap("close failed")
        return {}


class MutationTests(unittest.TestCase):
    def setUp(self):
        self.child = sp.PR(2, "open", "c" * 40, "main", "child", sp.REPO, "Stacked on #1", True)
        self.parent = sp.PR(1, "open", "b" * 40, "main", "parent", sp.REPO, "", False)
        self.evidence = sp.Evidence(1, self.parent.head, self.child.head, "a" * 40,
                                    "ancestor-head", self.parent.head, "d" * 64)
        self.api = FakeAPI(self.child, self.parent, self.evidence.main)

    def enforce(self):
        sp.enforce(self.api, self.child, self.parent, self.evidence, "trusted[bot]")

    def test_comment_precedes_close_and_branch_never_deleted(self):
        self.enforce()
        self.assertEqual([c[1] for c in self.api.calls], ["POST", "PATCH"])
        self.assertEqual(self.api.calls[-1][2], {"state": "closed"})

    def test_closed_unlanded_parent_gets_actionable_advice(self):
        self.assertIn("Remove the inherited work", sp.comment_text(self.evidence, "closed"))

    def test_forged_merge_marker_cannot_trigger_repository_branch_deletion(self):
        self.child = sp.PR(**{**sp.asdict(self.child), "landing_claim": True})
        self.api.prs[self.child.number] = self.child
        with self.assertRaisesRegex(sp.Gap, "branch preservation"):
            self.enforce()
        self.assertEqual([c[1] for c in self.api.calls], ["POST"])
        self.assertIn("Automatic closure is declined", self.api.calls[0][2]["body"])

    def test_comment_failure_does_not_close(self):
        self.api.fail_comment = True
        with self.assertRaises(sp.Gap):
            self.enforce()
        self.assertFalse(any(c[1] == "PATCH" for c in self.api.calls))

    def test_close_failure_retry_has_one_comment(self):
        self.api.fail_close = True
        with self.assertRaises(sp.Gap):
            self.enforce()
        self.api.fail_close = False
        self.enforce()
        self.assertEqual(len(self.api.comments), 1)

    def test_changed_evidence_retry_updates_one_comment(self):
        self.api.fail_close = True
        with self.assertRaises(sp.Gap):
            self.enforce()
        self.api.fail_close = False
        self.evidence = sp.Evidence(**{**sp.asdict(self.evidence), "patch_sha256": "e" * 64})
        self.enforce()
        self.assertEqual(len(self.api.comments), 1)
        self.assertIn("e" * 64, self.api.comments[0]["body"])

    def test_forged_comment_does_not_suppress_explanation(self):
        self.api.comments.append({"user": {"login": "attacker"}, "body": sp.comment_text(self.evidence)})
        self.enforce()
        self.assertEqual(len(self.api.comments), 2)

    def test_main_race_before_comment(self):
        self.api.sha = "f" * 40
        with self.assertRaises(sp.Gap):
            self.enforce()
        self.assertEqual(self.api.calls, [])

    def test_head_base_parent_state_races_after_comment(self):
        changes = [(2, "head", "f" * 40), (2, "base", "changed"),
                   (2, "base_head", "f" * 40),
                   (1, "head", "f" * 40), (1, "state", "closed")]
        for number, key, value in changes:
            with self.subTest(key=key, number=number):
                self.api = FakeAPI(self.child, self.parent, self.evidence.main)
                self.api.race = lambda: self.api.prs.update({number: sp.PR(**{
                    **sp.asdict(self.api.prs[number]), key: value})})
                with self.assertRaises(sp.Gap):
                    self.enforce()
                self.assertFalse(any(c[1] == "PATCH" for c in self.api.calls))


class APITests(unittest.TestCase):
    def test_empty_delete_response_is_success(self):
        api = object.__new__(sp.API)
        api.token, api.calls, api.bytes, api.deadline = "fixture", 0, 0, sp.time.monotonic() + 60
        response = MagicMock()
        response.__enter__.return_value = response
        response.read.return_value = b""
        with patch.object(sp, "urlopen", return_value=response):
            self.assertIsNone(api.request("https://api.github.com/repos/TauCetiProject/TauCeti/issues/2/labels/stacked-pr",
                                          "DELETE"))
    def test_pagination_truncation_and_rate_limit_are_failures(self):
        api = object.__new__(sp.API)
        api.call = lambda *args: [None] * 100
        with self.assertRaises(sp.Gap):
            api.pages("pulls", 100)
        api.call = lambda *args: (_ for _ in ()).throw(sp.Gap("rate limited"))
        with self.assertRaises(sp.Gap):
            api.pages("pulls", 100)

    def test_deleted_or_changed_branch_is_unknown(self):
        api = object.__new__(sp.API)
        api.call = lambda *args: {
            "number": 2, "state": "open", "draft": False, "body": "",
            "base": {"ref": "main", "sha": "a" * 40, "repo": {"full_name": sp.REPO}},
            "head": {"ref": "branch", "sha": "c" * 40, "repo": {"full_name": sp.REPO}},
        }
        for ref in [None, {"target": {"oid": "b" * 40}}]:
            api.request = lambda *args: {"data": {"repository": {"pullRequest": {"headRef": ref}}}}
            with self.assertRaises(sp.Gap):
                api.pr(2)


class MainTests(unittest.TestCase):
    def setUp(self):
        self.child = sp.PR(2, "open", "c" * 40, "main", "child", sp.REPO, "Stacked on #1", False,
                           "a" * 40)
        self.parent = sp.PR(1, "open", "b" * 40, "main", "parent", sp.REPO, "", False, "a" * 40)
        self.api = FakeAPI(self.child, self.parent, "a" * 40)
        self.api.bytes = 0
        self.evidence = sp.Evidence(1, self.parent.head, self.child.head, self.api.sha,
                                    "ancestor-head", self.parent.head, "d" * 64, "a" * 40)
        self.raw = [self.record(self.parent), self.record(self.child)]
        original_pages = self.api.pages
        self.api.pages = lambda path, limit: self.raw if path.startswith("pulls?") else original_pages(path, limit)
        self.detector = SimpleNamespace(prs=self.api.prs, gaps={}, detect=lambda _: (None, []))

    def record(self, p):
        return {"number": p.number, "state": p.state, "draft": p.draft, "body": p.body,
                "head": {"sha": p.head, "ref": p.branch, "repo": {"full_name": p.head_repo}},
                "base": {"sha": p.base_head, "ref": p.base, "repo": {"full_name": sp.REPO}},
                "labels": [{"name": sp.BLOCK_LABEL}] if p.blocked else []}

    def main(self, *args):
        empty_bors = {"schema": "tauceti-bors.observation/v1", "repo": sp.REPO, "base": "main",
                      "batch_ids": [], "batches": [], "held": []}
        with patch.object(sp, "API", return_value=self.api), patch.object(sp, "Source"), \
                patch.object(sp, "Detector", return_value=self.detector), \
                patch.object(sp, "run", return_value=SimpleNamespace(stdout=b"/tmp/policy-fixture")), \
                patch("bors_observation.observation", return_value=empty_bors), \
                patch.dict(os.environ, {"STACK_ACTOR": "trusted[bot]"}), \
                patch.object(sp.sys, "argv", ["stack_policy.py", *args]), redirect_stdout(io.StringIO()):
            return sp.main()

    def test_dry_run_confirmed_has_no_mutations(self):
        self.detector.detect = lambda _: (self.evidence, [])
        self.assertFalse(self.main("--pr", "2"))
        self.assertEqual(self.api.calls, [])

    def test_main_movement_on_clean_result_has_no_global_admission_side_effect(self):
        def result(_):
            self.api.sha = "f" * 40
            return None, []
        self.detector.detect = result
        self.assertFalse(self.main("--apply"))
        self.assertEqual(self.api.calls, [])

    def test_confirmed_blocks_then_comments_then_closes(self):
        self.detector.detect = lambda _: (self.evidence, [])
        self.assertFalse(self.main("--apply", "--pr", "2"))
        writes = [path for path, method, _ in self.api.calls if method != "GET"]
        self.assertEqual(writes, ["issues/2/labels", "issues/2/comments", "pulls/2"])
        self.assertFalse(any(path.startswith("statuses/") for path, _, _ in self.api.calls))

    def test_deleted_fork_in_index_does_not_abort_other_prs(self):
        deleted = copy.deepcopy(self.raw[1])
        deleted["number"] = 3
        deleted["head"]["repo"] = None
        self.raw.append(deleted)
        self.assertFalse(self.main("--apply"))
        self.assertEqual(self.api.calls, [])

    def test_failure_on_one_pr_does_not_write_error_status_or_abort_other_prs(self):
        visited = []
        def result(pr):
            visited.append(pr.number)
            if pr.number == 1:
                raise sp.Gap("incomplete source")
            return None, []
        self.detector.detect = result
        self.assertFalse(self.main("--apply"))
        self.assertEqual(visited, [1, 2])
        self.assertEqual(self.api.calls, [])

    def test_label_retry_is_idempotent(self):
        sp.block(self.api, self.child)
        sp.block(self.api, self.child)
        self.assertEqual(sum(method == "POST" for _, method, _ in self.api.calls), 1)

    def test_workflow_run_association_keeps_full_backlog_sweep(self):
        visited = []
        self.detector.detect = lambda p: (visited.append(p.number) or None, [])
        with tempfile.TemporaryDirectory() as directory:
            event = Path(directory) / "event.json"
            event.write_text(json.dumps({"workflow_run": {"pull_requests": [{"number": 2}]}}))
            self.assertFalse(self.main("--github-event", str(event)))
        self.assertEqual(visited, [1, 2])

    def test_closed_parent_budget_does_not_abort_unrelated_children(self):
        self.raw[1]["body"] = "Dependencies: " + ", ".join(f"#{n}" for n in range(100, 165))
        visited = []
        self.detector.detect = lambda p: (visited.append(p.number) or None, [])
        with patch.object(self.api, "pr", side_effect=sp.Gap("missing prerequisite")) as read:
            self.assertFalse(self.main())
        self.assertEqual(read.call_count, 64)
        self.assertEqual(visited, [1, 2])

    def test_incomplete_index_and_human_label_retain_prior_block(self):
        self.raw[1]["labels"] = [{"name": sp.BLOCK_LABEL}]
        for incomplete in (True, False):
            self.detector.gaps = {1: "source unavailable"} if incomplete else {}
            self.assertTrue(self.main("--apply", "--pr", "2"))
            self.assertFalse(any(method == "DELETE" for _, method, _ in self.api.calls))

    def test_only_latest_policy_owned_label_can_be_removed(self):
        self.raw[1]["labels"] = [{"name": sp.BLOCK_LABEL}]
        self.api.events = [{"id": 1, "event": "labeled", "label": {"name": sp.BLOCK_LABEL},
                            "actor": {"login": "trusted[bot]"}}]
        self.assertFalse(self.main("--apply", "--pr", "2"))
        self.assertEqual(self.api.calls[-1][1], "DELETE")
        self.api.calls.clear()
        self.api.events.append({**self.api.events[0], "id": 2, "actor": {"login": "human"}})
        self.assertTrue(self.main("--apply", "--pr", "2"))
        self.assertEqual(self.api.calls, [])

    def test_failed_label_write_does_not_abort_remaining_prs_or_close(self):
        other = sp.PR(3, "open", "e" * 40, "main", "other", sp.REPO, "", False, "a" * 40)
        self.api.prs[3] = other
        self.raw.append(self.record(other))
        visited = []
        def result(pr):
            visited.append(pr.number)
            return (self.evidence if pr.number == 2 else None), []
        self.detector.detect = result
        original = self.api.call
        def fail(path, method="GET", data=None):
            if path == "issues/2/labels" and method == "POST":
                raise sp.Gap("label write rate limited")
            return original(path, method, data)
        self.api.call = fail
        self.assertTrue(self.main("--apply"))
        self.assertEqual(visited, [1, 2, 3])
        self.assertFalse(any(method == "PATCH" for _, method, _ in self.api.calls))


class WithdrawalTests(unittest.TestCase):
    def setUp(self):
        output = redirect_stdout(io.StringIO())
        output.__enter__()
        self.addCleanup(output.__exit__, None, None, None)
        self.child = sp.PR(2, "open", "c" * 40, "main", "child", sp.REPO, "", False)
        self.data = {"schema": "tauceti-bors.observation/v1", "repo": sp.REPO, "base": "main",
                     "batch_ids": [7], "batches": [{"id": 7, "state": "waiting", "members": [
                         {"pr": 2, "head_sha": self.child.head}]}], "held": []}

    def test_queued_child_withdrawal_after_close_webhook(self):
        before = sp.membership(self.data, self.child)
        self.assertEqual(before["batches"], [7])
        withdrawn = copy.deepcopy(self.data)
        withdrawn["batches"][0]["members"] = []
        observations = iter([self.data, withdrawn])
        sp.verify_withdrawal(self.child, before, lambda: next(observations), sleep=lambda _: None)

    def test_still_queued_is_observable_failure(self):
        with self.assertRaises(sp.Gap):
            sp.verify_withdrawal(self.child, sp.membership(self.data, self.child),
                                 lambda: self.data, sleep=lambda _: None)

    def test_missing_or_truncated_membership_is_not_withdrawal(self):
        for data in [{}, {**self.data, "batch_ids": []}]:
            with self.assertRaises(sp.Gap):
                sp.membership(data, self.child)
        self.data["batches"][0]["members"] = [{"pr": 2}]
        with self.assertRaises(sp.Gap):
            sp.membership(self.data, self.child)


class IntegrationContractTests(unittest.TestCase):
    def test_block_label_and_workflow_trust(self):
        import tomllib
        import yaml
        root = Path(__file__).resolve().parent.parent
        bors = tomllib.loads((root / "bors.toml").read_text())
        self.assertIn(sp.BLOCK_LABEL, bors["block_labels"])
        self.assertEqual(bors["pr_status"], ["build", "bump-guard", "scope"])
        workflow = yaml.safe_load((root / ".github/workflows/stack-policy.yml").read_text())
        events = workflow.get("on", workflow.get(True))
        self.assertEqual(events["pull_request_target"]["branches"], ["main"])
        self.assertTrue(events["workflow_dispatch"]["inputs"]["dry-run"]["default"])
        job = workflow["jobs"]["enforce"]
        self.assertIn("github.ref == 'refs/heads/main'", job["if"])
        checkout = job["steps"][0]["with"]
        self.assertEqual(checkout["ref"], "refs/heads/main")
        self.assertFalse(checkout["persist-credentials"])
        wake = yaml.safe_load((root / ".github/workflows/stack-policy-wake.yml").read_text())
        self.assertEqual(wake["permissions"], {})
        self.assertEqual(wake["jobs"]["wake"]["steps"], [{"run": "true"}])


if __name__ == "__main__":
    unittest.main()
