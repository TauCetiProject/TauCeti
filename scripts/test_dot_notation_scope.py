"""Exercise the trusted workflow's empty dot-notation scope with real Git diffs."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import yaml

import lint_scope_files


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())
STEPS = WORKFLOW["jobs"]["sandboxed-build"]["steps"]
COMMAND = next(step["run"] for step in STEPS
               if step["name"].startswith("Dot-notation namespace lint"))
AUDIT_SCOPE = next(step["run"] for step in STEPS
                   if step["name"] == "Decide the audit scope")


class DotNotationScopeTest(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.project = self.root / "pr"
        self.project.mkdir()
        self.git("init", "--quiet", "--template=")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "user.name", "Fixture")
        self.write("TauCeti/Type.lean", "namespace TauCeti\ndef Foo : Type := Nat\n")
        self.write("TauCeti.lean", "module\n")
        self.base = self.commit()
        gate = self.root / "gate/scripts"
        gate.mkdir(parents=True)
        # CI materializes this helper; local runs may import the pinned shared copy.
        shutil.copyfile(lint_scope_files.__file__, gate / "lint_scope_files.py")
        (gate / "lint-dot-notation.py").write_text(
            "from pathlib import Path\nPath('lint-ran').touch()\nraise SystemExit(7)\n")
        self.modules = self.root / "modules.txt"
        self.modules.write_text("")

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.project, text=True).strip()

    def write(self, path, text):
        dest = self.project / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)

    def commit(self):
        self.git("add", "--all")
        self.git("commit", "--quiet", "--allow-empty", "-m", "fixture")
        return self.git("rev-parse", "HEAD")

    def run_step(self, *, scoped=True, base=None):
        env = {**os.environ, "DOT_BASE": base or self.base,
               "DOT_HEAD": self.commit(),
               "DOT_ONLY_MODULES": str(self.modules) if scoped else ""}
        result = subprocess.run(["bash", "-c", COMMAND], cwd=self.root, env=env,
                                text=True, capture_output=True)
        return result, (self.root / "lint-ran").exists()

    def assert_lint_runs(self, **kwargs):
        result, ran = self.run_step(**kwargs)
        self.assertTrue(ran, result.stdout + result.stderr)
        self.assertEqual(result.returncode, 7, result.stdout + result.stderr)

    def test_infrastructure_only_change_skips_without_mathlib_or_parser(self):
        self.write(".github/workflows/ci.yml", "changed\n")
        result, ran = self.run_step()
        self.assertFalse(ran)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("skipping namespace and ownership scans", result.stdout)

    def test_deleted_type_still_checks_namespace_ownership(self):
        (self.project / "TauCeti/Type.lean").unlink()
        self.assert_lint_runs()

    def test_renamed_type_still_checks_namespace_ownership(self):
        (self.project / "TauCeti/Type.lean").rename(self.project / "TauCeti/Renamed.lean")
        self.assert_lint_runs()

    def test_changed_source_cannot_be_hidden_by_an_empty_module_list(self):
        self.write("TauCeti/Type.lean", "changed\n")
        self.assert_lint_runs()

    def test_root_module_change_keeps_lint(self):
        self.write("TauCeti.lean", "module\npublic import TauCeti.Type\n")
        self.assert_lint_runs()

    def test_unavailable_diff_falls_back_to_lint(self):
        self.assert_lint_runs(base="f" * 40)

    def test_missing_scope_file_does_not_skip(self):
        self.modules.unlink()
        self.assert_lint_runs()

    def test_nonempty_scope_runs_lint(self):
        self.modules.write_text("TauCeti.Type\n")
        self.assert_lint_runs()

    def test_full_scope_runs_lint_even_without_source_changes(self):
        self.assert_lint_runs(scoped=False)

    def test_pins_batches_and_unmatched_sources_cannot_select_empty_scoped_lint(self):
        unmatched = self.root / "unmatched.txt"
        github_env = self.root / "github-env"
        for bump, batch, extra in (("1", "false", ""), ("0", "true", ""),
                                   ("0", "false", "TauCeti.lean\n")):
            with self.subTest(bump=bump, batch=batch, unmatched=extra):
                unmatched.write_text(extra)
                github_env.write_text("")
                env = {**os.environ, "BUMP": bump, "IS_BATCH": batch,
                       "LINT_ONLY_MODULES": str(self.modules),
                       "LINT_SCOPE_DIR": str(self.root), "GITHUB_ENV": str(github_env)}
                command = AUDIT_SCOPE.replace("${{ env.IS_BATCH }}", "${IS_BATCH}")
                result = subprocess.run(["bash", "-c", command], env=env,
                                        text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("DOT_ONLY_MODULES=\n", github_env.read_text())


if __name__ == "__main__":
    unittest.main()
