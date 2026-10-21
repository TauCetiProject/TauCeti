"""Run the production head-resolution shell against failing GitHub responses."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
HEAD, BASE, MERGEBASE = (letter * 40 for letter in "abc")
ERROR = '{\n  "message": "API rate limit exceeded",\n  "status": "403"\n}\n'


class HeadResolution(unittest.TestCase):
    def resolve(self, base=(BASE, 0), compare=(MERGEBASE, 0), batch=False):
        workflow = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())
        command = next(step["run"] for step in workflow["jobs"]["sandboxed-build"]["steps"]
                       if step.get("id") == "pr")
        values = {
            "github.event_name": "merge_group" if batch else "pull_request_target",
            "github.repository": "TauCetiProject/TauCeti",
            "github.event.pull_request.number": "19245",
            "github.event.pull_request.head.sha": HEAD,
            "github.event.pull_request.head.repo.full_name": "example/TauCeti",
            "github.event.pull_request.base.ref": "main",
            "github.event.pull_request.user.login": "example",
            "github.event.merge_group.head_sha": HEAD,
            "github.event.merge_group.base_sha": BASE,
            "env.IS_BATCH": "true" if batch else "false",
        }
        command = re.sub(r"\$\{\{\s*(.*?)\s*\}\}", lambda m: values.get(m[1], ""), command)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stub = root / "gh"
            stub.write_text(f"#!{sys.executable}\n" + '''import json, os, sys
from pathlib import Path
args = sys.argv[1:]
with Path(os.environ["RESOLUTION_TEST_CALLS"]).open("a") as log:
    log.write(json.dumps(args) + "\\n")
response = "BASE" if "/commits/" in args[1] else "COMPARE"
sys.stdout.write(os.environ["RESOLUTION_TEST_" + response])
sys.exit(int(os.environ["RESOLUTION_TEST_" + response + "_STATUS"]))
''')
            stub.chmod(0o755)
            output, env_file, calls = (root / name for name in ["output", "env", "calls"])
            result = subprocess.run(["bash", "-euc", command + '\nprintf "continued\\n"'],
                env={**os.environ, "PATH": str(root) + os.pathsep + os.environ["PATH"],
                     "GITHUB_OUTPUT": str(output), "GITHUB_ENV": str(env_file),
                     "RESOLUTION_TEST_CALLS": str(calls),
                     "RESOLUTION_TEST_BASE": base[0], "RESOLUTION_TEST_BASE_STATUS": str(base[1]),
                     "RESOLUTION_TEST_COMPARE": compare[0], "RESOLUTION_TEST_COMPARE_STATUS": str(compare[1])},
                capture_output=True, text=True)
            output_text = output.read_text()
            self.assertTrue(all("=" in line for line in output_text.splitlines()), output_text)
            outputs = dict(line.split("=", 1) for line in output_text.splitlines())
            settings = dict(line.split("=", 1) for line in env_file.read_text().splitlines())
            requests = [json.loads(line) for line in calls.read_text().splitlines()]
            return result, outputs, settings, requests

    def assert_infrastructure_failure(self, result, outputs, settings):
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn("continued", result.stdout)
        self.assertEqual(outputs["sha"], HEAD)
        self.assertEqual(outputs["status_sha"], HEAD)
        self.assertEqual(outputs["num"], "19245")
        self.assertEqual(settings["INFRA"], "1")
        self.assertEqual(settings["MERGEBASE_EXACT"], "0")
        self.assertNotIn("mergebase", outputs)

    def test_success_records_exact_captured_identity(self):
        result, outputs, settings, requests = self.resolve()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(outputs["base_sha"], BASE)
        self.assertEqual(outputs["mergebase"], MERGEBASE)
        self.assertEqual(outputs["status_sha"], HEAD)
        self.assertEqual(settings["MERGEBASE_EXACT"], "1")
        self.assertNotIn("INFRA", settings)
        self.assertEqual(len(requests), 2)
        self.assertIn(f"/compare/{BASE}...example:{HEAD}", requests[1][1])

    def test_failed_or_malformed_base_skips_dependent_compare(self):
        for response in [(ERROR, 1), (BASE, 1), (ERROR, 0), ("null", 0), ("b" * 39, 0)]:
            with self.subTest(response=response):
                result, outputs, settings, requests = self.resolve(base=response)
                self.assert_infrastructure_failure(result, outputs, settings)
                self.assertNotIn("base_sha", outputs)
                self.assertEqual(len(requests), 1)
                self.assertIn("/commits/main", requests[0][1])

    def test_failed_or_malformed_merge_base_never_becomes_an_exact_sha(self):
        for response in [(ERROR, 1), (MERGEBASE, 1), (ERROR, 0), ("null", 0), ("", 0)]:
            with self.subTest(response=response):
                result, outputs, settings, requests = self.resolve(compare=response)
                self.assert_infrastructure_failure(result, outputs, settings)
                self.assertEqual(outputs["base_sha"], BASE)
                self.assertEqual(len(requests), 2)

    def test_merge_group_keeps_its_immutable_base_without_resolving_main(self):
        result, outputs, settings, requests = self.resolve(batch=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(outputs["base_sha"], BASE)
        self.assertEqual(outputs["status_sha"], HEAD)
        self.assertEqual(settings["MERGEBASE_EXACT"], "1")
        self.assertEqual(len(requests), 1)
        self.assertIn(f"/compare/{BASE}...TauCetiProject:{HEAD}", requests[0][1])

    def test_failed_resolution_still_reports_failure_on_the_known_head(self):
        _, outputs, settings, _ = self.resolve(base=(ERROR, 1))
        workflow = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())
        command = next(step["run"] for step in workflow["jobs"]["sandboxed-build"]["steps"]
                       if step.get("id") == "report")
        values = {"github.repository": "TauCetiProject/TauCeti", "env.IS_BATCH": "false"}
        values.update({"steps.pr.outputs." + key: value for key, value in outputs.items()})
        values.update({"env." + key: value for key, value in settings.items()})
        command = re.sub(r"\$\{\{\s*(.*?)\s*\}\}", lambda m: values.get(m[1], ""), command)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stub = root / "gh"
            stub.write_text(f"#!{sys.executable}\n" + '''import json, os, sys
from pathlib import Path
with Path(os.environ["REPORT_TEST_CALLS"]).open("a") as log:
    log.write(json.dumps(sys.argv[1:]) + "\\n")
print("{}" if "POST" in sys.argv else os.environ["REPORT_TEST_HEAD"] + " main")
''')
            stub.chmod(0o755)
            calls = root / "calls"
            result = subprocess.run(["bash", "-euc", command], cwd=root,
                env={**os.environ, "PATH": str(root) + os.pathsep + os.environ["PATH"],
                     "GITHUB_OUTPUT": str(root / "output"), "REPORT_TEST_CALLS": str(calls),
                     "REPORT_TEST_HEAD": HEAD}, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn("tested-integration", result.stderr)
            posts = [json.loads(line) for line in calls.read_text().splitlines() if '"POST"' in line]
            self.assertEqual(len(posts), 3)
            for post in posts:
                self.assertIn("repos/TauCetiProject/TauCeti/statuses/" + HEAD, post)
                self.assertIn("state=failure", post)
            self.assertEqual({next(arg for arg in post if arg.startswith("context=")) for post in posts},
                             {"context=build", "context=scope", "context=bump-guard"})


if __name__ == "__main__":
    unittest.main()
