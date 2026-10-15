"""Real Git fixtures and mutation/race tests; no network or Lean execution."""

import copy
import html
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
                  "fork/TauCeti" if fork else sp.REPO, body, draft, author_id=1)
        self.prs.append(p)
        return p

    def detector(self, api=None):
        main = git(self.root, "rev-parse", "main")
        src = sp.Source(Path(self.tmp.name) / "source", None, main,
                        self.root / ".git/objects", str(self.root))
        src.fetch(self.prs)
        # Plain-text fixtures still exercise the production HTML/prose filters.
        # API integration tests separately bind actual rendered metadata.
        api = api or SimpleNamespace(declared_parents=lambda p: sp.rendered_parents(
            "<p>" + html.escape(p.body) + "</p>"))
        return sp.Detector(api, src, self.prs)

    def test_nested_code_fence_cannot_bind_independent_identical_content(self):
        git(self.root, "checkout", "-b", "parent")
        self.write("P", "independent identical content\n")
        self.commit("parent change")
        self.pr(1)
        git(self.root, "checkout", "main")
        git(self.root, "checkout", "-b", "child")
        self.write("P", "independent identical content\n")
        self.write("C", "own change\n")
        self.commit("independent child change")
        body = "````markdown\n```text\nStacked on #1\n```\n````"
        child = self.pr(2, body)
        api = object.__new__(sp.API)
        api.request = lambda *args: {"data": {"repository": {"pullRequest": {
            "body": body, "headRefOid": child.head,
            "bodyHTML": "<pre><code>```text\nStacked on #1\n```</code></pre>",
        }}}}
        self.assertIsNone(self.detector(api).detect(child)[0])

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

    def test_outsider_copied_prefix_cannot_close_victim(self):
        git(self.root, "checkout", "-b", "victim")
        self.write("prefix", "victim's first contribution\n")
        prefix = self.commit("victim first")
        self.write("own", "victim's next contribution\n")
        self.commit("victim next")
        victim = self.pr(2)
        git(self.root, "checkout", "--detach", prefix)
        attacker = self.pr(3)
        self.prs[-1] = sp.PR(**{**sp.asdict(attacker), "head_repo": "outsider/TauCeti"})
        with self.assertRaisesRegex(sp.Gap, "possible copied prefix"):
            self.detector().detect(victim)

    def test_unpinned_child_declaration_does_not_bypass_cross_fork_provenance(self):
        _, child = self.parent_child(explicit=True)
        child = sp.PR(**{**sp.asdict(child), "head_repo": "another/TauCeti", "author_id": 2})
        self.prs[-1] = child
        with self.assertRaisesRegex(sp.Gap, "possible copied prefix"):
            self.detector().detect(child)

    def test_outsider_opening_existing_same_repository_branch_is_unknown(self):
        parent, child = self.parent_child()
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "author_id": 2})
        with self.assertRaisesRegex(sp.Gap, "possible third-party branch PR"):
            self.detector().detect(child)

    def test_unknown_author_cannot_authorize_ancestry_only_closure(self):
        parent, child = self.parent_child()
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "author_id": 0})
        with self.assertRaisesRegex(sp.Gap, "unknown/different author"):
            self.detector().detect(child)

    def test_stale_explicit_parent_cannot_copy_standalone_child_prefix(self):
        git(self.root, "checkout", "-b", "parent")
        self.write("A", "old prerequisite\n")
        self.commit("original prerequisite")
        parent = self.pr(1)
        git(self.root, "checkout", "-b", "child")
        self.write("B", "child first contribution\n")
        copied_prefix = self.commit("child first")
        self.write("D", "child next contribution\n")
        self.commit("child next")
        child = self.pr(2, "Stacked on #1")
        git(self.root, "checkout", "main")
        git(self.root, "merge", "--squash", "parent")
        self.commit("original prerequisite landed through another squash")
        git(self.root, "update-ref", "refs/pull/1/head", copied_prefix)
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "head": copied_prefix})
        detector = self.detector()
        # Another opener can use the existing fork branch too; test both forms.
        for repository in (parent.head_repo, "outsider/TauCeti"):
            with self.subTest(repository=repository):
                detector.prs[1] = sp.PR(**{**sp.asdict(parent), "head": copied_prefix,
                                      "author_id": 2, "head_repo": repository})
                with self.assertRaisesRegex(sp.Gap, "provenance unproved|unknown/different author"):
                    detector.detect(child)

    def test_explicit_parent_with_unknown_author_remains_unknown(self):
        parent, child = self.parent_child(explicit=True)
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "author_id": 0})
        with self.assertRaisesRegex(sp.Gap, "unknown/different author"):
            self.detector().detect(child)

    def test_current_canonical_base_can_establish_cross_author_relationship(self):
        parent, child = self.parent_child()
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "head_repo": sp.REPO, "author_id": 2})
        child = sp.PR(**{**sp.asdict(child), "base": parent.branch})
        self.prs[-1] = child
        self.assertIsNotNone(self.detector().detect(child)[0])

    def test_closed_parent_cannot_grant_canonical_base_exception(self):
        parent, child = self.parent_child(explicit=True)
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "state": "closed",
                              "head_repo": sp.REPO, "author_id": 2})
        child = sp.PR(**{**sp.asdict(child), "base": parent.branch})
        self.prs[-1] = child
        with self.assertRaisesRegex(sp.Gap, "provenance unproved"):
            self.detector().detect(child)

    def test_cross_principal_prose_cannot_attribute_copied_content(self):
        git(self.root, "checkout", "-b", "victim")
        self.write("copied", "victim contribution\n")
        copied = self.commit("victim change")
        self.write("own", "victim next contribution\n")
        self.commit("victim next")
        child = self.pr(2, "Stacked on #1")
        git(self.root, "checkout", "main")
        git(self.root, "checkout", "-b", "outsider")
        git(self.root, "cherry-pick", copied)
        git(self.root, "commit", "--amend", "-m", "outsider copies victim content")
        parent = self.pr(1)
        self.prs[-1] = sp.PR(**{**sp.asdict(parent), "head_repo": "outsider/TauCeti", "author_id": 2})
        self.assertNotEqual(parent.head, copied)
        with self.assertRaisesRegex(sp.Gap, "provenance unproved"):
            self.detector().detect(child)

    def test_cross_principal_explicit_parent_landed_by_squash_is_not_unknown(self):
        parent, child = self.parent_child(explicit=True)
        self.prs[0] = sp.PR(**{**sp.asdict(parent), "head_repo": "other/TauCeti", "author_id": 2})
        git(self.root, "checkout", "main")
        git(self.root, "merge", "--squash", "parent")
        self.commit("land parent through independent squash")
        evidence, reasons = self.detector().detect(child)
        self.assertIsNone(evidence)
        self.assertTrue(any("source equivalent landed" in reason for reason in reasons))

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
    def test_rendered_code_quotes_and_link_labels_are_not_declarations(self):
        cases = [
            "<pre><code>```\nStacked on #12\n```</code></pre>",
            "<blockquote><p>Stacked on #12</p><p>lazy continuation</p></blockquote>",
            "<p><code>Stacked on #12</code></p>",
            '<p>&quot;Example:</p><p>Stacked on #12</p><p>end quote&quot;</p>',
            '<p><a href="https://github.com/other/repo/pull/12">Stacked on #12</a></p>',
            "<p>Example: stacked on #12</p>",
            "<q><p>Stacked on #12</p></q>",
            "<p>Example:\nStacked on #12</p>",
            "<p>Example:<br>Stacked on #12</p>",
            "<p><code>Example:</code>Stacked on #12</p>",
            '<p><a href="https://example.com">Example:</a>Stacked on #12</p>',
            "<p>Example: <code>ignored</code>Stacked on #12</p>",
            "<p><del>Stacked on #12</del> Rebased onto main.</p>",
            "<p><s>Stacked on #12</s></p>",
            "<p><strike>Stacked on #12</strike></p>",
            "<p>«Example:</p><p>Stacked on #12</p><p>end»</p>",
            "<summary>Example</summary><p>Stacked on #12</p>",
            "<p>Do not write:</p><ul><li>Stacked on #12</li></ul>",
            '<p>Stacked on <a href="https://githubxcom/TauCetiProject/TauCeti/pull/12">parent</a></p>',
            '<p>Stacked on <a href="/TauCetiProject/TauCeti/pull/12">not a dependency</a></p>',
            '<p>Stacked on #12 <a href="https://example.com">no longer</a></p>',
        ]
        for html in cases:
            with self.subTest(html=html):
                self.assertEqual(sp.rendered_parents(html), set())

    def test_rendered_current_statement_and_canonical_parent_link(self):
        html = '<p>This PR is stacked on <a href="/TauCetiProject/TauCeti/pull/12">parent</a>.</p>'
        self.assertEqual(sp.rendered_parents(html), {12})
        html = '<p>Stacked on <a href="/TauCetiProject/TauCeti/pull/12">first</a>, <a href="/TauCetiProject/TauCeti/pull/13">second</a>.</p>'
        self.assertEqual(sp.rendered_parents(html), {12, 13})
        self.assertEqual(sp.rendered_parents("<p>Dependencies: #12, #13</p>"), {12, 13})
        self.assertEqual(sp.rendered_parents("<p>This PR is\nstacked on #12</p>"), {12})

    def test_parent_reference_list_cannot_absorb_supersession_clause(self):
        for separator in ("<br>\n", "\n", ", ", "; "):
            with self.subTest(separator=separator):
                self.assertEqual(sp.rendered_parents(
                    "<p>Depends on #12" + separator + "Supersedes #13</p>"), set())
        self.assertEqual(sp.rendered_parents("<p>Depends on #12<br>#13 is superseded by this PR</p>"), set())
        self.assertEqual(sp.rendered_parents("<p>Depends on #12, #13 and #14</p>"), {12, 13, 14})

    def test_rendered_literal_markup_is_not_stripped_again(self):
        self.assertEqual(sp.rendered_parents("<p>`Template:` Stacked on #12</p>"), set())
        self.assertEqual(sp.rendered_parents("<p>&lt;!-- x --&gt; Stacked on #12</p>"), set())
        self.assertEqual(sp.rendered_parents("<p>`x. Stacked on #12`</p>"), set())

    def test_rendered_metadata_cache_identity_and_failures(self):
        child = sp.PR(2, "open", "c" * 40, "main", "branch", sp.REPO,
                      "Stacked on #1", False)
        api = object.__new__(sp.API)
        result = {"data": {"repository": {"pullRequest": {
            "body": child.body, "headRefOid": child.head, "bodyHTML": "<p>Stacked on #1</p>",
        }}}}
        api.request = MagicMock(return_value=result)
        self.assertEqual(api.declared_parents(child), {1})
        self.assertEqual(api.declared_parents(child), {1})
        self.assertEqual(api.request.call_count, 1)
        for field in ("body", "headRefOid", "bodyHTML"):
            with self.subTest(field=field):
                api.__dict__.pop("declarations", None)
                changed = copy.deepcopy(result)
                changed["data"]["repository"]["pullRequest"][field] = None
                api.request = MagicMock(return_value=changed)
                with self.assertRaises(sp.Gap):
                    api.declared_parents(child)
                with self.assertRaises(sp.Gap):
                    api.declared_parents(child)
                self.assertEqual(api.request.call_count, 1)
        api.__dict__.pop("declarations", None)
        api.request = lambda *args: {"errors": [{"type": "RATE_LIMITED"}]}
        with self.assertRaises(sp.BudgetGap):
            api.declared_parents(child)

    def test_render_transport_failure_is_cached_gap_for_one_child(self):
        child = sp.PR(2, "open", "c" * 40, "main", "branch", sp.REPO, "Stacked on #1", False)
        api = object.__new__(sp.API)
        api.request = MagicMock(side_effect=TimeoutError("transient rendering timeout"))
        for _ in range(2):
            with self.assertRaisesRegex(sp.Gap, "transient rendering timeout"):
                api.declared_parents(child)
        self.assertEqual(api.request.call_count, 1)
    def test_read_only_historical_rendered_examples(self):
        fixtures = json.loads((Path(__file__).with_name("stack_policy_fixtures.json")).read_text())
        # Current captured bodies are separate from the immutable audit heads.
        # Quoted/negative context conservatively declines three declarations;
        # exact ancestry may still establish their stacks independently.
        expected = {"16755": set(), "16656": {16643, 16632, 15253},
                    "16613": set(), "16130": set()}
        for number, parents in expected.items():
            item = fixtures["explicit_prose"][number]
            self.assertEqual(sp.oid(item["head"]), item["head"])
            captured = fixtures["rendered_prose_capture"]["prs"][number]
            self.assertEqual(sp.oid(captured["head"]), captured["head"])
            self.assertEqual(sp.rendered_parents(captured["body_html"]), parents)

    def test_affirmative_parent_identity(self):
        self.assertEqual(sp.rendered_parents("<p>This PR is stacked on #12 (#11).</p>"), {11, 12})
        self.assertEqual(sp.rendered_parents('<p>Stacked on <a href="/TauCetiProject/TauCeti/pull/12">parent</a></p>'), {12})
        self.assertEqual(sp.rendered_parents("<p>Prerequisite: #12</p>"), {12})

    def test_superseding_closed_source_is_not_a_stack_claim(self):
        for body in ("Includes the prerequisite source from #12. This PR supersedes that standalone foundation.",
                     "Includes #12 (a composition theorem, which depends on #11). This PR supersedes them.",
                     "Prerequisite: #12. This PR includes #11 and supersedes it."):
            self.assertFalse(sp.rendered_parents("<p>" + html.escape(body) + "</p>"))

    def test_misleading_quoted_negative_and_foreign_prose(self):
        for body in ["> Stacked on #12", "```\nStacked on #12\n```", "Not stacked on #12",
                     "This was stacked on #12", '`Stacked on #12`', 'The title is "stacked on #12"',
                     '“Stacked on #12”', "'Stacked on #12'", "``Stacked on #12``",
                     "Prerequisites: none; #12 will build on this", "Depends on Mathlib PR #12",
                     "<!-- Stacked on #12 -->", "Stacked on https://github.com/other/repo/pull/12"]:
            with self.subTest(body=body):
                self.assertFalse(sp.rendered_parents("<p>" + html.escape(body) + "</p>"))


class FakeAPI:
    def declared_parents(self, child):
        return sp.rendered_parents("<p>" + html.escape(child.body) + "</p>")
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

    def begin_child(self):
        pass

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
    def test_child_budget_declines_before_io_then_next_child_can_continue(self):
        api = object.__new__(sp.API)
        api.token, api.calls, api.bytes, api.deadline = "fixture", 0, 0, sp.time.monotonic() + 60
        api.begin_child()
        api.calls = api.child_calls
        with patch.object(sp, "urlopen") as request:
            with self.assertRaises(sp.ChildGap):
                api.request("https://api.github.com/repos/TauCetiProject/TauCeti/pulls")
            request.assert_not_called()
            api.begin_child()
            request.return_value.__enter__.return_value.read.return_value = b"[]"
            self.assertEqual(api.request("https://api.github.com/repos/TauCetiProject/TauCeti/pulls"), [])

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
        api.request = lambda *args: {"errors": [{"type": "RATE_LIMITED"}]}
        with self.assertRaises(sp.BudgetGap):
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
        source = SimpleNamespace(fetch=MagicMock(), begin_child=lambda: None, calls=0, started=sp.time.monotonic())
        self.last_source = source
        with patch.object(sp, "API", return_value=self.api), patch.object(sp, "Source", return_value=source), \
                patch.object(sp, "Detector", return_value=self.detector) as constructor, \
                patch.object(sp, "run", return_value=SimpleNamespace(stdout=b"/tmp/policy-fixture")), \
                patch("bors_observation.observation", return_value=empty_bors), \
                patch.dict(os.environ, {"STACK_ACTOR": "trusted[bot]"}), \
                patch.object(sp.sys, "argv", ["stack_policy.py", *args]), redirect_stdout(io.StringIO()):
            self.last_constructor = constructor
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
        self.assertEqual(visited, [2, 1])
        self.assertEqual(self.api.calls, [])

    def test_label_retry_is_idempotent(self):
        sp.block(self.api, self.child)
        sp.block(self.api, self.child)
        self.assertEqual(sum(method == "POST" for _, method, _ in self.api.calls), 1)

    def event(self, data, *args):
        with tempfile.TemporaryDirectory() as directory:
            event = Path(directory) / "event.json"
            event.write_text(json.dumps(data))
            return self.main("--github-event", str(event), *args)

    def test_workflow_run_association_focuses_only_triggered_pr(self):
        visited = []
        self.detector.detect = lambda p: (visited.append(p.number) or None, [])
        self.assertFalse(self.event({"workflow_run": {"head_sha": self.parent.head, "pull_requests": [{
            "number": 1, "head": {"sha": self.parent.head},
            "base": {"repo": {"url": f"https://api.github.com/repos/{sp.REPO}"}},
        }]}}))
        self.assertEqual(visited, [1])
        self.assertEqual({p.number for p in self.last_source.fetch.call_args.args[0]}, {1, 2})
        self.assertEqual({p.number for p in self.last_constructor.call_args.args[2]}, {1, 2})

    def test_pr_event_focuses_older_target_and_explicit_pr_overrides_it(self):
        visited = []
        self.detector.detect = lambda p: (visited.append(p.number) or None, [])
        self.assertFalse(self.event({"pull_request": {"number": 1}}))
        self.assertEqual(visited, [1])
        visited.clear()
        self.assertFalse(self.event({"pull_request": {"number": 1}}, "--pr", "2"))
        self.assertEqual(visited, [2])

    def test_schedule_and_unselected_manual_dispatch_keep_full_sweep(self):
        for event in ({}, {"inputs": {"pr": "0"}}):
            with self.subTest(event=event):
                visited = []
                self.detector.detect = lambda p: (visited.append(p.number) or None, [])
                self.assertFalse(self.event(event))
                self.assertEqual(visited, [2, 1])

    def test_fork_wake_without_association_matches_current_index(self):
        fork = sp.PR(**{**sp.asdict(self.child), "base": "branch-1", "head_repo": "fork/TauCeti"})
        wake = {"workflow_run": {"pull_requests": [], "head_sha": fork.head,
                                "head_branch": fork.branch,
                                "head_repository": {"full_name": fork.head_repo}}}
        self.assertEqual(sp.event_targets(wake, [self.parent, fork, self.child]), {2})
        for field, value in (("head_sha", "f" * 40), ("head_branch", "other"),
                             ("head_repository", {"full_name": "outsider/TauCeti"})):
            with self.subTest(field=field):
                changed = copy.deepcopy(wake)
                changed["workflow_run"][field] = value
                if field == "head_sha":
                    self.assertEqual(sp.event_targets(changed, [fork]), {2})
                else:
                    with self.assertRaises(sp.Gap):
                        sp.event_targets(changed, [fork])

    def test_incomplete_wake_or_closed_event_never_broadens_to_backlog(self):
        with self.assertRaises(sp.Gap):
            self.event({"workflow_run": {"pull_requests": []}})
        self.assertFalse(self.event({"pull_request": {"number": 99}}))
        self.assertEqual(self.api.calls, [])

    def test_out_of_order_fork_wakes_recompute_current_head(self):
        fork = sp.PR(**{**sp.asdict(self.child), "base": "branch-1", "head_repo": "fork/TauCeti"})
        self.raw[1] = self.record(fork)
        wake = {"workflow_run": {"head_sha": "f" * 40, "head_branch": fork.branch,
                                "head_repository": {"full_name": fork.head_repo}}}
        visited = []
        self.detector.detect = lambda p: (visited.append(p.head) or None, [])
        for old in ("f" * 40, "b" * 40, fork.head):
            wake["workflow_run"]["head_sha"] = old
            self.assertFalse(self.event(wake))
        self.assertEqual(visited, [fork.head] * 3)
        self.raw[1]["head"]["repo"] = None
        with self.assertRaises(sp.Gap):
            self.event(wake)
        self.assertEqual(self.api.calls, [])

    def test_malformed_target_is_not_classified_superseded(self):
        self.raw[1]["head"]["repo"] = None
        with self.assertRaises(sp.Gap):
            self.event({"pull_request": {"number": 2}})

    def test_foreign_or_wrong_head_association_does_not_select_unrelated_pr(self):
        fork = sp.PR(**{**sp.asdict(self.child), "base": "branch-1", "head_repo": "fork/TauCeti"})
        wake = {"workflow_run": {"head_sha": fork.head, "head_branch": fork.branch,
            "head_repository": {"full_name": fork.head_repo}, "pull_requests": [{
                "number": 1, "head": {"sha": fork.head}, "base": {"repo": {"full_name": "other/repo"}},
            }]}}
        self.assertEqual(sp.event_targets(wake, [self.parent, fork]), {2})
        linked = wake["workflow_run"]["pull_requests"][0]
        linked["base"]["repo"]["full_name"] = sp.REPO
        linked["head"]["sha"] = "f" * 40
        self.assertEqual(sp.event_targets(wake, [self.parent, fork]), {2})

    def test_closed_parent_budget_does_not_abort_unrelated_children(self):
        self.raw[1]["body"] = "Dependencies: " + ", ".join(f"#{n}" for n in range(100, 165))
        visited = []
        self.detector.detect = lambda p: (visited.append(p.number) or None, [])
        with patch.object(self.api, "pr", side_effect=sp.Gap("missing prerequisite")) as read:
            self.assertFalse(self.main())
        self.assertEqual(read.call_count, 64)
        self.assertEqual(visited, [2, 1])

    def test_incomplete_index_and_human_label_retain_prior_block(self):
        self.raw[1]["labels"] = [{"name": sp.BLOCK_LABEL}]
        for incomplete in (True, False):
            self.detector.gaps = {1: "source unavailable"} if incomplete else {}
            self.assertFalse(self.main("--apply", "--pr", "2"))
            self.assertFalse(any(method == "DELETE" for _, method, _ in self.api.calls))

    def test_only_latest_policy_owned_label_can_be_removed(self):
        self.raw[1]["labels"] = [{"name": sp.BLOCK_LABEL}]
        self.api.events = [{"id": 1, "event": "labeled", "label": {"name": sp.BLOCK_LABEL},
                            "actor": {"login": "trusted[bot]"}}]
        self.assertFalse(self.main("--apply", "--pr", "2"))
        self.assertEqual(self.api.calls[-1][1], "DELETE")
        self.api.calls.clear()
        self.api.events.append({**self.api.events[0], "id": 2, "actor": {"login": "human"}})
        self.assertFalse(self.main("--apply", "--pr", "2"))
        self.assertEqual(self.api.calls, [])

    def test_global_budget_exhaustion_aborts_sweep(self):
        self.detector.detect = MagicMock(side_effect=sp.BudgetGap("source operation/time budget exhausted"))
        with self.assertRaises(sp.BudgetGap):
            self.main()
        self.assertEqual(self.detector.detect.call_count, 1)

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
        self.assertEqual(visited, [3, 2, 1])
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
        self.assertNotIn("queue", workflow["concurrency"])
        self.assertIn("github.event.pull_request.number", workflow["concurrency"]["group"])
        self.assertIn("head_repository.id", workflow["concurrency"]["group"])
        self.assertIn("head_branch", workflow["concurrency"]["group"])
        self.assertIn("github.run_id", workflow["concurrency"]["group"])
        self.assertEqual(job["concurrency"], {"group": "tauceti-no-stacking",
                                           "queue": "max", "cancel-in-progress": False})
        self.assertFalse(workflow["concurrency"]["cancel-in-progress"])
        self.assertIn("vars.NO_STACK_APPLY == 'true'", job["if"])
        self.assertIn("github.event_name == 'workflow_dispatch'", job["if"])
        self.assertIn("github.ref == 'refs/heads/main'", job["if"])
        checkout = job["steps"][0]["with"]
        self.assertEqual(checkout["ref"], "refs/heads/main")
        self.assertFalse(checkout["persist-credentials"])
        wake = yaml.safe_load((root / ".github/workflows/stack-policy-wake.yml").read_text())
        self.assertEqual(wake["permissions"], {})
        self.assertEqual(wake["jobs"]["wake"]["steps"], [{"run": "true"}])


if __name__ == "__main__":
    unittest.main()
