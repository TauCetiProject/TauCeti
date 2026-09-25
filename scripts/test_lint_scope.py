"""Tests for scripts/lint-scope.sh, with a fake `gh` that serves canned API responses."""

import json
import os
import pathlib
import stat
import subprocess
import tempfile
import textwrap
import unittest

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "lint-scope.sh"
SHA_A, SHA_B = "a" * 40, "b" * 40

FAKE_GH = textwrap.dedent('''\
    #!/usr/bin/env python3
    import json, os, subprocess, sys
    responses = json.load(open(os.environ["FAKE_GH_RESPONSES"]))
    args = sys.argv[1:]
    assert args[0] == "api", args
    path = next(a for a in args[1:] if not a.startswith("-") and a != args[args.index("--jq") + 1]
                ) if "--jq" in args else next(a for a in args[1:] if not a.startswith("-"))
    path = path.split("?")[0]
    if path not in responses:
        sys.exit(f"fake gh: no response for {path}")
    data = json.dumps(responses[path])
    if "--jq" in args:
        data = subprocess.run(["jq", "-r", args[args.index("--jq") + 1]], input=data,
                              capture_output=True, text=True, check=True).stdout
    sys.stdout.write(data)
''')


def pr(head_ref="feature", labels=()):
    return {"head": {"ref": head_ref}, "labels": [{"name": n} for n in labels]}


def f(status, filename):
    return {"status": status, "filename": filename}


class LintScopeTest(unittest.TestCase):
    def run_scope(self, env, responses):
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            gh = d / "bin" / "gh"
            gh.parent.mkdir()
            gh.write_text(FAKE_GH)
            gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
            (d / "responses.json").write_text(json.dumps(responses))
            github_env = d / "github_env"
            full_env = dict(os.environ, PATH=f"{gh.parent}:{os.environ['PATH']}",
                            FAKE_GH_RESPONSES=str(d / "responses.json"),
                            GITHUB_ENV=str(github_env), GH_TOKEN="x", REPO="o/r", **env)
            out = subprocess.run(["bash", str(SCRIPT), str(d / "scope")], env=full_env,
                                 capture_output=True, text=True)
            self.assertEqual(out.returncode, 0, out.stderr)
            setting = github_env.read_text().strip()
            self.assertTrue(setting.startswith("LINT_ONLY_MODULES="), setting)
            if setting == "LINT_ONLY_MODULES=":
                return None
            return pathlib.Path(setting.split("=", 1)[1]).read_text().split()

    def test_pull_request_lints_changed_tauceti_modules(self):
        modules = self.run_scope(
            {"EVENT": "pull_request_target", "NUM": "12"},
            {"repos/o/r/pulls/12/files": [f("modified", "TauCeti/A/B.lean"),
                                          f("added", "TauCeti/C.lean"),
                                          f("renamed", "TauCeti/D'.lean"),
                                          f("removed", "TauCeti/Gone.lean"),
                                          f("modified", "README.md"),
                                          f("modified", "TauCeti/notes.md")],
             "repos/o/r/pulls/12": pr()})
        self.assertEqual(modules, ["TauCeti.A.B", "TauCeti.C", "TauCeti.D'"])

    def test_no_tauceti_change_lints_nothing(self):
        self.assertEqual(self.run_scope(
            {"EVENT": "pull_request_target", "NUM": "12"},
            {"repos/o/r/pulls/12/files": [f("modified", "lake-manifest.json")],
             "repos/o/r/pulls/12": pr()}), [])

    def test_full_lint_label_and_repair_branch_lint_everything(self):
        files = {"repos/o/r/pulls/12/files": [f("modified", "TauCeti/A.lean")]}
        for info in (pr(labels=["roadmap/none", "full-lint"]), pr(head_ref="lint-repair/main")):
            with self.subTest(info=info):
                self.assertIsNone(self.run_scope(
                    {"EVENT": "pull_request_target", "NUM": "12"},
                    dict(files, **{"repos/o/r/pulls/12": info})))

    def test_merge_group_reads_prs_from_squash_titles(self):
        compare = {"commits": [{"commit": {"message": "feat: x (#7)\n\nbody"}},
                               {"commit": {"message": "fix: y (#8)"}}],
                   "files": [f("modified", "TauCeti/X.lean")]}
        responses = {f"repos/o/r/compare/{SHA_A}...{SHA_B}": compare,
                     "repos/o/r/pulls/7": pr(), "repos/o/r/pulls/8": pr()}
        env = {"EVENT": "merge_group", "BASE": SHA_A, "HEAD": SHA_B}
        self.assertEqual(self.run_scope(env, responses), ["TauCeti.X"])
        responses["repos/o/r/pulls/8"] = pr(labels=["full-lint"])
        self.assertIsNone(self.run_scope(env, responses))

    def test_unattributable_commits_lint_everything(self):
        compare = {"commits": [{"commit": {"message": "feat: x (#7)"}},
                               {"commit": {"message": "Merge branch main"}}],
                   "files": [f("modified", "TauCeti/X.lean")]}
        self.assertIsNone(self.run_scope(
            {"EVENT": "push", "BASE": SHA_A, "HEAD": SHA_B},
            {f"repos/o/r/compare/{SHA_A}...{SHA_B}": compare, "repos/o/r/pulls/7": pr()}))

    def test_missing_base_lints_everything(self):
        self.assertIsNone(self.run_scope({"EVENT": "push", "BASE": "0" * 40, "HEAD": SHA_B}, {}))


class PrBuildWiringTest(unittest.TestCase):
    def test_scope_is_decided_before_the_sandbox_and_mounted_read_only(self):
        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "pr-build.yml").read_text())
        (job,) = [j for j in wf["jobs"].values()
                  if any("Build exact candidate under bwrap" in s.get("name", "")
                         for s in j.get("steps", []))]
        names = [s.get("name", "") for s in job["steps"]]
        scope = names.index("Decide the environment-lint scope")
        sandbox = next(i for i, n in enumerate(names) if "Build exact candidate under bwrap" in n)
        self.assertLess(scope, sandbox)
        run = job["steps"][sandbox]["run"]
        self.assertIn('--ro-bind "$LINT_SCOPE_DIR" "$LINT_SCOPE_DIR"', run)
        self.assertIn('--setenv LINT_ONLY_MODULES "${LINT_ONLY_MODULES:-}"', run)


if __name__ == "__main__":
    unittest.main()
