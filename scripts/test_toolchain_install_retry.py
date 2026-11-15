"""Exercise both production retry blocks with failing installer processes."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
PIN = "leanprover/lean4:v4.36.0-rc1"


class InstallRetry(unittest.TestCase):
    def blocks(self):
        action = yaml.safe_load((ROOT / ".github/actions/restore-lean-toolchain/action.yml").read_text())
        publisher = yaml.safe_load((ROOT / ".github/workflows/publish-lake-cache.yml").read_text())
        commands = [action["runs"]["steps"][-1]["run"], next(
            step["run"] for step in publisher["jobs"]["publish"]["steps"]
            if step.get("id") == "toolchain")]
        for command in commands:
            start = command.index("for toolchain_attempt")
            end = command.index("done", start) + len("done")
            # Substitute only the executable location; leave the actual loop and
            # release argument expressions intact. Never modify the real elan home.
            yield command[start:end].replace('"$HOME/.elan/bin/elan"', "elan")

    def run_block(self, block, failures):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean-toolchain").write_text(PIN + "\n")
            installer = root / "elan"
            installer.write_text(
                '#!/usr/bin/env bash\nset -eu\n'
                'printf "%s\\n" "$*" >> "$RETRY_TEST_LOG"\n'
                'count=$(wc -l < "$RETRY_TEST_LOG")\n'
                'if [ "$count" -le "$RETRY_TEST_FAILURES" ]; then exit 67; fi\n')
            sleeper = root / "sleep"
            sleeper.write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "$RETRY_TEST_DELAYS"\n')
            for executable in [installer, sleeper]:
                executable.chmod(0o755)
            log, delays = root / "installs", root / "delays"
            result = subprocess.run(
                ["bash", "-euc", block + '\nprintf "finished\\n"'],
                env={**os.environ, "PATH": str(root) + os.pathsep + os.environ["PATH"],
                     "TOOLCHAIN": PIN, "PROJECT": str(root), "RETRY_TEST_LOG": str(log),
                     "RETRY_TEST_DELAYS": str(delays), "RETRY_TEST_FAILURES": str(failures)},
                capture_output=True, text=True)
            return result, log.read_text().splitlines(), delays.read_text().splitlines() if delays.exists() else []

    def test_success_has_no_retry_or_delay(self):
        for block in self.blocks():
            with self.subTest(block=block):
                result, installs, delays = self.run_block(block, 0)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(installs, ["toolchain install " + PIN])
                self.assertEqual(delays, [])

    def test_transient_failures_retry_same_pin_and_then_continue(self):
        for block in self.blocks():
            for failures in [1, 2]:
                with self.subTest(block=block, failures=failures):
                    result, installs, delays = self.run_block(block, failures)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertIn("finished", result.stdout)
                    self.assertEqual(installs, ["toolchain install " + PIN] * (failures + 1))
                    self.assertEqual(delays, ["5", "10"][:failures])

    def test_exhaustion_preserves_failure_and_blocks_following_commands(self):
        for block in self.blocks():
            with self.subTest(block=block):
                result, installs, delays = self.run_block(block, 10)
                self.assertEqual(result.returncode, 67)
                self.assertNotIn("finished", result.stdout)
                self.assertEqual(installs, ["toolchain install " + PIN] * 3)
                self.assertEqual(delays, ["5", "10"])


if __name__ == "__main__":
    unittest.main()
