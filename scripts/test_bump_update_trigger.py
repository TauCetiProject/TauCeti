#!/usr/bin/env python3
"""Pin landing events survive coalesced CI and cannot act on stale/fork results."""

import base64
import json
import unittest
from bump_update_trigger import Evidence, reconcile


class TriggerTests(unittest.TestCase):
    def setUp(self):
        self.head, self.base, self.current = (c * 40 for c in "abc")
        self.run = dict(id=20, event="push", head_branch="main", status="completed",
                        conclusion="success", head_sha=self.head,
                        head_repository={"full_name": "TauCetiProject/TauCeti"})
        self.old = dict(self.run, id=10, head_sha=self.base)
        self.pins = {self.base: "old", self.head: "new", self.current: "new"}
        self.parents = {(self.base, self.head), (self.head, self.current)}

    def check(self, previous=None):
        return reconcile(self.run, [self.old] if previous is None else previous,
                         repo="TauCetiProject/TauCeti", current=self.current,
                         pin_at=self.pins.__getitem__, ancestor=lambda a, b: (a, b) in self.parents)

    def test_changed_pin_in_coalesced_history_reconciles(self):
        self.assertTrue(self.check())

    def test_ordinary_same_pin_ci_is_cheap(self):
        self.pins[self.base] = "new"
        self.assertFalse(self.check())

    def test_delayed_success_cannot_authorize_a_newer_pin(self):
        self.pins[self.current] = "newer"
        self.assertFalse(self.check())

    def test_nonancestor_success_is_ignored(self):
        self.parents.remove((self.head, self.current))
        self.assertFalse(self.check())

    def test_only_successful_canonical_main_push_is_accepted(self):
        for changes in [{"conclusion": "failure"}, {"status": "in_progress"},
                        {"head_branch": "topic"}, {"event": "pull_request"},
                        {"head_repository": {"full_name": "fork/TauCeti"}}]:
            with self.subTest(changes=changes):
                saved = self.run
                self.run = saved | changes
                self.assertFalse(self.check())
                self.run = saved

    def test_cancelled_coalesced_and_current_runs_do_not_hide_pin_change(self):
        self.assertTrue(self.check([self.run, self.old | {"id": 15, "conclusion": "cancelled"}, self.old]))

    def test_a_failed_new_pin_does_not_hide_the_later_success(self):
        failed = dict(self.old, id=15, head_sha=self.head, conclusion="failure")
        self.assertTrue(self.check([failed, self.old]))

    def test_toolchain_changes_are_part_of_the_pin_signal(self):
        self.pins[self.base] = ("mathlib", "old-toolchain")
        self.pins[self.head] = self.pins[self.current] = ("mathlib", "new-toolchain")
        self.assertTrue(self.check())

    def test_first_run_reconciles_once(self):
        self.assertTrue(self.check([]))


class EvidenceTests(unittest.TestCase):
    def test_reads_only_small_pin_files_and_caches_immutable_heads(self):
        calls = []
        commit = "a" * 40
        def api(path):
            calls.append(path)
            value = (json.dumps({"packages": [{"name": "mathlib", "rev": "b" * 40}]})
                     if "lake-manifest" in path else "leanprover/lean4:v4.35.0-rc3\n")
            return {"encoding": "base64", "content": base64.b64encode(value.encode()).decode()}
        evidence = Evidence("owner/repo", api)
        self.assertEqual(evidence.pin_at(commit), ("b" * 40, "leanprover/lean4:v4.35.0-rc3"))
        evidence.pin_at(commit)
        self.assertEqual(len(calls), 2)
        self.assertTrue(all(f"?ref={commit}" in path for path in calls))

    def test_compare_requires_forward_history(self):
        for status in ["identical", "ahead", "behind", "diverged"]:
            evidence = Evidence("owner/repo", lambda path: {"status": status})
            self.assertEqual(evidence.ancestor("a" * 40, "b" * 40), status in {"identical", "ahead"})
        evidence = Evidence("owner/repo", lambda path: self.fail("identical commits need no API call"))
        self.assertTrue(evidence.ancestor("a" * 40, "a" * 40))


if __name__ == "__main__":
    unittest.main()
