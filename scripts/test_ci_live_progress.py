"""Progress grants stay outside every post-build candidate execution namespace."""
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[1]


class ProgressIsolation(unittest.TestCase):
    def test_reporter_wraps_resource_observer_and_clean_sandbox(self):
        job = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())["jobs"]["sandboxed-build"]
        self.assertEqual(job["permissions"]["id-token"], "write")
        body = next(s["run"] for s in job["steps"] if s.get("id") == "build")
        self.assertIn('"${progress_observer[@]}" python3 gate/scripts/ci_host_resources.py', body)
        self.assertIn("env -i /usr/bin/bwrap", body)
        self.assertIn("--unshare-pid --unshare-net", body)
        self.assertNotIn("--setenv ACTIONS_ID_TOKEN", body)

    def test_post_build_probe_cannot_reach_host_grants(self):
        job = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())["jobs"]["sandboxed-build"]
        body = next(s["run"] for s in job["steps"] if s.get("id") == "shim_expiry")
        self.assertIn("env -i /usr/bin/bwrap", body)
        self.assertIn("--unshare-pid --unshare-net", body)
        self.assertIn("--remount-ro /", body)
        self.assertNotIn("--setenv ACTIONS_ID_TOKEN", body)


if __name__ == "__main__":
    unittest.main()
