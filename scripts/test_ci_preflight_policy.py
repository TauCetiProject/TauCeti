"""Production workflow contracts for changed-module PR lint and complete staging checks."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github/workflows/pr-build.yml"

def shell_for(name, workflow=WORKFLOW):
    lines = workflow.read_text().splitlines()
    start = lines.index("      - name: " + name)
    run = next(i for i in range(start, len(lines)) if lines[i] == "        run: |")
    end = run + 1
    while end < len(lines) and (not lines[end] or lines[end].startswith("          ")):
        end += 1
    return "\n".join(line[10:] for line in lines[run + 1:end]) + "\n"


class PreflightScopeTests(unittest.TestCase):
    def test_pr_scope_and_full_gate_fallbacks(self):
        for batch, bump, scoped, unmatched in [
            (False, False, True, ""), (True, False, True, ""),
            (False, True, True, ""), (False, False, False, ""),
            (False, False, True, "web/Main.lean\n"),
            (False, False, True, None),
        ]:
            with self.subTest(batch=batch, bump=bump, scoped=scoped, unmatched=unmatched):
                with tempfile.TemporaryDirectory() as temp:
                    root = Path(temp)
                    modules = root / "modules"
                    modules.write_text("TauCeti.Changed\n")
                    if unmatched is not None:
                        (root / "unmatched.txt").write_text(unmatched)
                    envfile = root / "env"
                    shell = shell_for("Decide the audit scope").replace(
                        "${{ env.IS_BATCH }}", "true" if batch else "false")
                    out = subprocess.run(["bash", "-euo", "pipefail", "-c", shell],
                        text=True, capture_output=True, env={**os.environ,
                        "GITHUB_ENV": str(envfile), "LINT_SCOPE_DIR": str(root),
                        "LINT_ONLY_MODULES": str(modules) if scoped else "",
                        "BUMP": "1" if bump else "0"})
                    self.assertEqual(out.returncode, 0, out.stderr)
                    values = dict(line.split("=", 1) for line in envfile.read_text().splitlines())
                    fast = not batch and not bump and scoped and unmatched == ""
                    self.assertEqual(values["LINT_CHANGED_ONLY"], "1" if fast else "0")
                    self.assertEqual(values["AXIOMS_ONLY_MODULES"], str(modules) if fast else "")
                    self.assertEqual(values["DOT_ONLY_MODULES"], str(modules) if fast else "")
                    self.assertNotIn("LINT_ONLY_MODULES", values)


class DotContextTests(unittest.TestCase):
    def test_main_regenerates_and_publishes_before_candidate_execution(self):
        ci = (ROOT / ".github/workflows/ci.yml").read_text()
        self.assertNotIn("Restore dot-notation parsing context", ci)
        self.assertIn("rm -rf .ci-dot-notation-context", ci)
        self.assertEqual(ci.count("name: Dot-notation namespace lint"), 1)
        self.assertLess(ci.index("Save main's dot-notation parsing context"),
                        ci.index("      - name: Build\n"))
        self.assertIn("if: github.ref_name == github.event.repository.default_branch", ci)

    def test_pr_cache_is_restore_only_and_sandbox_receives_preflight_mode(self):
        text = WORKFLOW.read_text()
        self.assertNotIn("Save main's dot-notation", text)
        self.assertLess(text.index("Restore dot-notation parsing context"),
                        text.index("      - name: Dot-notation namespace lint"))
        self.assertIn('--context-cache ".ci-dot-notation-context/context.json"', text)
        build = shell_for("Build exact candidate under bwrap with workflow-pinned audits, offline")
        self.assertIn('--setenv LINT_CHANGED_ONLY "${LINT_CHANGED_ONLY:-0}"', build)
        self.assertIn('--ro-bind "$LINT_SCOPE_DIR" "$LINT_SCOPE_DIR"', build)


if __name__ == "__main__":
    unittest.main()
