"""Exercise cache failures followed by a build, and cache-independent bump validation."""

import base64
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from test_bump_manifest import fixture

ROOT = Path(__file__).resolve().parents[1]


class MathlibCacheGetTest(unittest.TestCase):
    def restore_and_build(self, responses):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            project = work / "project"
            project.mkdir()
            mock = work / "lake"
            mock.write_text(
                "#!/usr/bin/env python3\n"
                "import json, os, sys\n"
                "from pathlib import Path\n"
                "with open(os.environ['CALLS'], 'a') as calls:\n"
                "    calls.write(' '.join(sys.argv[1:]) + '\\n')\n"
                "assert Path.cwd() == Path(os.environ['PROJECT'])\n"
                "response = json.loads(os.environ['RESPONSES'])[sys.argv[-1]]\n"
                "print(response[1])\n"
                "sys.exit(response[0])\n"
            )
            mock.chmod(0o755)
            env = dict(os.environ, PATH=f"{work}:{os.environ['PATH']}",
                       SCRIPT=str(ROOT / "scripts/mathlib-cache-get.sh"),
                       PROJECT=str(project), LOG=str(work / "cache.log"),
                       CALLS=str(work / "calls"), RESPONSES=json.dumps(responses))
            result = subprocess.run(
                ["bash", "-e", "-o", "pipefail", "-c",
                 'bash "$SCRIPT" "$PROJECT" "$LOG"; cd "$PROJECT"; lake build'],
                env=env, capture_output=True, text=True,
            )
            return result, (work / "calls").read_text().splitlines(), (work / "cache.log").read_text()

    def test_complete_cache_builds_without_retry(self):
        result, calls, _ = self.restore_and_build({"get": [0, "downloaded"], "build": [0, "built"]})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ["exe cache get", "build"])
        self.assertNotIn("::warning::", result.stdout)

    def test_partial_cache_warns_and_builds_without_retry(self):
        result, calls, _ = self.restore_and_build({
            "get": [0, "Warning: some files were not found in the cache."], "build": [0, "built"]})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ["exe cache get", "build"])
        self.assertIn("::warning::Mathlib cache is incomplete", result.stdout)

    def test_retry_preserves_both_attempts_in_the_log(self):
        result, calls, log = self.restore_and_build({
            "get": [1, "first failed"], "get!": [0, "retry downloaded"], "build": [0, "built"]})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ["exe cache get", "exe cache get!", "build"])
        self.assertIn("first failed", log)
        self.assertIn("retry downloaded", log)

    def test_both_downloads_fail_but_build_still_runs(self):
        result, calls, _ = self.restore_and_build({
            "get": [1, "first failed"], "get!": [1, "retry failed"], "build": [0, "built"]})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ["exe cache get", "exe cache get!", "build"])
        self.assertIn("::warning::Mathlib cache restore failed twice", result.stdout)

    def test_build_failure_after_cache_failure_remains_fatal(self):
        result, calls, _ = self.restore_and_build({
            "get": [1, "first failed"], "get!": [1, "retry failed"], "build": [1, "proof failed"]})
        self.assertEqual(result.returncode, 1)
        self.assertEqual(calls[-1], "build")
        self.assertIn("proof failed", result.stdout)


class CacheIndependentBumpTest(unittest.TestCase):
    def validate(self, forward="ahead", membership="ahead"):
        pr, mathlib, base = fixture()
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            for name, manifest in (("base", base), ("merge-base", base), ("pr", pr)):
                checkout = work / name
                checkout.mkdir()
                (checkout / "lake-manifest.json").write_text(json.dumps(manifest))
                (checkout / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc1\n")
                (checkout / "lakefile.toml").write_text('name = "TauCeti"\n')
            mock = work / "gh"
            mock.write_text(
                "#!/usr/bin/env python3\n"
                "import os, sys\n"
                "endpoint = sys.argv[2]\n"
                "if '/compare/' in endpoint:\n"
                "    print(os.environ['MEMBERSHIP' if endpoint.endswith('...master') else 'FORWARD'])\n"
                "elif '/contents/lake-manifest.json?' in endpoint:\n"
                "    print(os.environ['MANIFEST'])\n"
                "elif '/contents/lean-toolchain?' in endpoint:\n"
                "    print(os.environ['TOOLCHAIN'])\n"
                "else:\n"
                "    sys.exit('upstream CI and cache metadata are unavailable')\n"
            )
            mock.chmod(0o755)
            encode = lambda value: base64.b64encode(value.encode()).decode()
            env = dict(os.environ, PATH=f"{work}:{os.environ['PATH']}",
                       FORWARD=forward, MEMBERSHIP=membership,
                       MANIFEST=encode(json.dumps(mathlib)),
                       TOOLCHAIN=encode("leanprover/lean4:v4.34.0-rc1"))
            return subprocess.run(
                ["bash", str(ROOT / "scripts/check-bump.sh"),
                 str(work / "base"), str(work / "merge-base"), str(work / "pr")],
                env=env, capture_output=True, text=True,
            )

    def test_forward_bump_passes_without_cache_or_upstream_ci_metadata(self):
        result = self.validate()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_backward_bump_still_fails(self):
        result = self.validate(forward="behind")
        self.assertEqual(result.returncode, 1)
        self.assertIn("not a forward move", result.stdout)

    def test_commit_outside_trusted_branch_still_fails(self):
        result = self.validate(membership="diverged")
        self.assertEqual(result.returncode, 1)
        self.assertIn("not on branch", result.stdout)


if __name__ == "__main__":
    unittest.main()
