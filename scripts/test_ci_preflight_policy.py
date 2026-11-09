"""Production workflow contracts for changed-module PR lint and complete staging checks."""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github/workflows/pr-build.yml"

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


if __name__ == "__main__":
    unittest.main()
