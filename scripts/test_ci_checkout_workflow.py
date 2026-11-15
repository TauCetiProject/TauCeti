"""The project workflow must retain stable objects for every offline Git reader."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
STEPS = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())["jobs"]["sandboxed-build"]["steps"]


class SourceCheckouts(unittest.TestCase):
    def test_complete_source_fetch_preserves_the_identity_boundary(self):
        fetch = next(step for step in STEPS if step.get("id") == "source_fetch")
        resolver = next(i for i, step in enumerate(STEPS) if "ci_git.py resolve" in step.get("run", ""))
        self.assertLess(resolver, STEPS.index(fetch))
        self.assertGreaterEqual(fetch["timeout-minutes"], 70)
        self.assertIn("exec python3 gate/scripts/ci_checkout.py fetch", fetch["run"])
        self.assertIn('--github-env "$GITHUB_ENV"', fetch["run"])
        self.assertNotIn("$(python3", fetch["run"])
        for name, output in (("HEAD", "sha"), ("BASE", "base_sha"), ("MERGEBASE", "mergebase")):
            self.assertEqual(fetch["env"]["SOURCE_" + name], "${{ steps.pr.outputs." + output + " }}")
        materializations = [step for step in STEPS if "ci_checkout.py materialize" in step.get("run", "")]
        self.assertEqual(len(materializations), 3)
        for step in materializations:
            self.assertLess(STEPS.index(fetch), STEPS.index(step))
            self.assertNotIn("uses", step)
        report = next(step["run"] for step in STEPS if step.get("id") == "report")
        self.assertLess(report.index("steps.source_fetch.outcome"), report.index('elif [ "$identity_ok" != 1 ]'))

    def test_all_git_sandboxes_mount_objects_in_ordinary_and_frozen_modes(self):
        build = next(step["run"] for step in STEPS if step.get("id") == "build")
        probes = [step["run"] for step in STEPS if "probe_mounts=(" in step.get("run", "")]
        self.assertEqual(len(probes), 1)
        for frozen in ("true", "false"):
            for text, name, end in [
                (build, "object_mounts", "progress_observer=()"),
                *((probe, "probe_mounts", "env -i /usr/bin/bwrap") for probe in probes),
            ]:
                with self.subTest(frozen=frozen, mounts=name), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    for path in (".ci-source.git/objects", "pr-raw-head/.git/objects", "base/.git/objects"):
                        (root / path).mkdir(parents=True)
                    start = text.index(name + "=(")
                    snippet = text[start:text.index(end, start)].replace("${{ env.IS_BATCH }}", frozen)
                    snippet += f'\nprintf "%s\\0" "${{{name}[@]}}"\n'
                    result = subprocess.run(
                        ["bash", "-euo", "pipefail", "-c", snippet], cwd=root,
                        env={**os.environ, "CI_SOURCE_OBJECTS": str(root / ".ci-source.git/objects"),
                             "BASE_SHIM_REGISTRY": "", "BASE_SHIM_ROOT": ""},
                        capture_output=True, check=True,
                    )
                    arguments = result.stdout.decode().split("\0")[:-1]
                    self.assertEqual(arguments[:3], ["--ro-bind", str(root / ".ci-source.git/objects"),
                                                     str(root / ".ci-source.git/objects")])
                    self.assertEqual(len(arguments), 3 if frozen == "true" else 9)


if __name__ == "__main__":
    unittest.main()
