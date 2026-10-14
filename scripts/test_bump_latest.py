#!/usr/bin/env python3
"""Selection, fixed targets, and publication recovery without network or credentials."""

import base64
import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import bump_latest as bl

OLD, NEW, TIP = (c * 40 for c in "abc")


def run(target, **kwargs):
    return (
        dict(
            head_sha=target,
            id=42,
            html_url="https://example.org/build/42",
            event="push",
            head_branch="master",
            status="completed",
            conclusion="success",
            head_repository={"full_name": bl.MATHLIB},
        )
        | kwargs
    )


def pr(target=NEW, **kwargs):
    return (
        dict(
            number=1,
            user={"type": "Bot"},
            head={"sha": target, "ref": "bump-mathlib/fix-test", "repo": {"full_name": bl.REPO}},
            base={"ref": "main"},
            labels=[],
        )
        | kwargs
    )


class BumpTests(unittest.TestCase):
    def test_history_order_beats_completion_order_and_deduplicates(self):
        self.assertEqual(
            bl.ordered_runs([run(NEW), run(TIP), run(TIP)], [TIP, NEW]), [run(TIP), run(NEW)]
        )
        for changes in [
            dict(event="workflow_dispatch"),
            dict(head_branch="staging"),
            dict(status="in_progress"),
            dict(conclusion="failure"),
            dict(head_repository={"full_name": "attacker/mathlib"}),
        ]:
            self.assertEqual(bl.ordered_runs([run(TIP, **changes)], [TIP]), [])

    def test_manifest_derivation_matches_the_existing_guard(self):
        fixtures = Path(__file__).with_name("bump_manifest_fixtures")
        base, upstream = (
            json.loads((fixtures / name).read_text()) for name in ["base.json", "mathlib.json"]
        )
        before = copy.deepcopy(base)
        proposed = bl.derive_manifest(base, upstream, NEW)
        self.assertEqual(base, before)
        self.assertEqual(bl.pin(proposed), NEW)
        self.assertEqual(bl.problems(proposed, upstream, base), [])
        self.assertTrue(all(p["inherited"] for p in proposed["packages"] if p["name"] != "mathlib"))

    def test_fixed_target_holds_and_obsolete_closure(self):
        data = {
            "content": base64.b64encode(
                json.dumps({"packages": [{"name": "mathlib", "rev": NEW}]}).encode()
            ).decode()
        }
        with (
            patch.object(bl, "api", return_value=data),
            patch.object(bl, "relationship", return_value="ahead"),
        ):
            self.assertEqual(bl.bump_state(OLD, [pr()]), ([pr()], []))
        with (
            patch.object(bl, "api", return_value=data),
            patch.object(bl, "relationship", return_value="behind"),
        ):
            self.assertEqual(bl.bump_state(TIP, [pr()]), ([], [pr()]))
        held = pr(labels=[{"name": "hold"}])
        with patch.object(bl, "api", side_effect=AssertionError("held target must not be changed")):
            self.assertEqual(bl.bump_state(TIP, [held]), ([held], []))

    def test_divergence_does_not_authorize_obsolete_closure(self):
        with patch.object(bl, "api", return_value={"status": "diverged"}):
            with self.assertRaises(RuntimeError):
                bl.relationship(OLD, NEW)

    def test_partial_cache_only_is_a_fallback(self):
        with tempfile.TemporaryDirectory() as tmp:
            checkout = Path(tmp) / "mathlib"
            checkout.mkdir()
            (checkout / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
            with patch.object(
                bl, "command", side_effect=["", "", "some files were not found in the cache"]
            ) as cmd:
                self.assertFalse(bl.verify_cache(checkout, NEW))
                environment = cmd.call_args.kwargs["env"]
                self.assertNotIn("GH_TOKEN", environment)
                self.assertNotIn("GITHUB_TOKEN", environment)
            with patch.object(bl, "command", side_effect=RuntimeError("network down")):
                with self.assertRaisesRegex(RuntimeError, "network down"):
                    bl.verify_cache(checkout, NEW)
            with patch.object(bl, "command", side_effect=["", "", "downloaded", ""]) as cmd:
                self.assertTrue(bl.verify_cache(checkout, NEW))
                self.assertIn("--rehash", cmd.call_args.args[0])

    def test_selector_skips_missing_cache_but_not_transport_failures(self):
        def cmd(args, **kwargs):
            return "\n".join([TIP, NEW, OLD]) if "rev-list" in args else ""

        with (
            patch.object(bl, "command", side_effect=cmd),
            patch.object(bl, "api", return_value={"workflow_runs": [run(NEW), run(TIP)]}),
        ):
            with patch.object(bl, "verify_cache", side_effect=[False, True]) as probe:
                self.assertEqual(bl.select_target(OLD), run(NEW))
                self.assertEqual([c.args[1] for c in probe.call_args_list], [TIP, NEW])
            with patch.object(bl, "verify_cache", side_effect=RuntimeError("API failure")) as probe:
                with self.assertRaises(RuntimeError):
                    bl.select_target(OLD)
                self.assertEqual(probe.call_count, 1)

    def test_publication_preserves_active_repairs(self):
        with (
            patch.object(bl, "command", return_value=OLD) as cmd,
            patch.object(
                bl.Path,
                "read_text",
                return_value=json.dumps({"packages": [{"name": "mathlib", "rev": OLD}]}),
            ),
            patch.object(bl, "open_bumps", return_value=[pr()]),
            patch.object(bl, "bump_state", return_value=([pr()], [])),
            patch.object(bl, "api", side_effect=AssertionError("no candidate mutation")),
        ):
            bl.publish(NEW, 42)
            self.assertEqual(cmd.call_count, 1)

    def test_closed_pr_is_not_reopened(self):
        with (
            patch.object(bl, "command", return_value=OLD),
            patch.object(
                bl.Path,
                "read_text",
                return_value=json.dumps({"packages": [{"name": "mathlib", "rev": OLD}]}),
            ),
            patch.object(bl, "open_bumps", return_value=[]),
            patch.object(bl, "bump_state", return_value=([], [])),
            patch.object(bl, "relationship", return_value="ahead"),
            patch.object(bl, "api", side_effect=[run(NEW), [{"number": 9, "state": "closed"}]]),
        ):
            bl.publish(NEW, 42)

    def test_new_hold_prevents_obsolete_closure(self):
        held = pr(state="open", labels=[{"name": "hold"}])
        with (
            patch.object(bl, "command", return_value=OLD) as commands,
            patch.object(
                bl.Path,
                "read_text",
                return_value=json.dumps({"packages": [{"name": "mathlib", "rev": TIP}]}),
            ),
            patch.object(bl, "open_bumps", return_value=[pr()]),
            patch.object(bl, "bump_state", side_effect=[([], [pr()]), ([held], [])]),
            patch.object(bl, "api", return_value=held),
        ):
            bl.publish(NEW, 42)
            self.assertFalse(
                any(c.args[0][:3] == ["gh", "pr", "close"] for c in commands.call_args_list)
            )

    def test_existing_repair_branch_is_never_overwritten(self):
        fixtures = Path(__file__).with_name("bump_manifest_fixtures")
        base, upstream = (
            json.loads((fixtures / name).read_text()) for name in ["base.json", "mathlib.json"]
        )
        existing = {
            "content": base64.b64encode(
                json.dumps({"packages": [{"name": "mathlib", "rev": NEW}]}).encode()
            ).decode()
        }

        def cmd(args, **kwargs):
            return (
                OLD
                if args[:3] == ["git", "rev-parse", "HEAD"]
                else (NEW + "\tbranch" if "ls-remote" in args else "")
            )

        with (
            patch.object(bl, "command", side_effect=cmd) as commands,
            patch.object(bl.Path, "read_text", return_value=json.dumps(base)),
            patch.object(bl, "open_bumps", return_value=[]),
            patch.object(bl, "bump_state", return_value=([], [])),
            patch.object(bl, "relationship", return_value="ahead"),
            patch.object(bl, "api", side_effect=[run(NEW), [], existing]),
            patch.object(
                bl,
                "upstream_file",
                side_effect=[json.dumps(upstream), "leanprover/lean4:v4.35.0\n"],
            ),
            patch.object(bl.Path, "write_text"),
        ):
            bl.publish(NEW, 42)
            self.assertFalse(any("push" in c.args[0] for c in commands.call_args_list))
            self.assertTrue(
                any(c.args[0][:3] == ["gh", "pr", "create"] for c in commands.call_args_list)
            )


if __name__ == "__main__":
    unittest.main()
