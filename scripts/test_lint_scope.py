"""Scope policy tests using real Git objects and canned GitHub metadata."""

import json
import os
import pathlib
import shlex
import shutil
import stat
import subprocess
import sys
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
    if "_error" in responses[path]:
        sys.exit(responses[path]["_error"])
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
    def run_scope(self, env, responses, *, files=None, prepare=None, unmatched=False, policy=False,
                  initial_files=None):
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            checkout = d / "candidate"
            checkout.mkdir()
            def git(*args):
                return subprocess.check_output(["git", "-C", str(checkout), *args],
                                               stderr=subprocess.PIPE, text=True).strip()
            git("init", "-q")
            git("config", "user.name", "Scope test")
            git("config", "user.email", "scope@example.invalid")
            if files is None:
                files = next((c.get("files", []) for k, c in responses.items()
                              if "/compare/" in k), [])
            def write(name, contents):
                path = checkout / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(contents)
            for name, contents in (initial_files or {}).items():
                write(name, contents)
            for index, entry in enumerate(files):
                if entry["status"] in ("modified", "removed"):
                    write(entry["filename"], "old\n")
                elif entry["status"] == "renamed":
                    write(entry.get("previous_filename", f"TauCeti/OldName{index}.lean"), "old\n")
            git("add", ".")
            git("commit", "-qm", "base", "--allow-empty")
            base = git("rev-parse", "HEAD")
            for index, entry in enumerate(files):
                if entry["status"] == "removed":
                    (checkout / entry["filename"]).unlink()
                else:
                    write(entry["filename"], "new\n")
                if entry["status"] == "renamed":
                    (checkout / entry.get("previous_filename", f"TauCeti/OldName{index}.lean")).unlink()
            git("add", ".")
            git("commit", "-qm", "head", "--allow-empty")
            head = git("rev-parse", "HEAD")
            # Snapshot endpoints before any simulated force-push/base movement.
            responses = {key.replace(SHA_A, base).replace(SHA_B, head):
                         ({**value, "merge_base_commit": {"sha": base}}
                          if "/compare/" in key else value)
                         for key, value in responses.items()}
            env = {key: (value.replace(SHA_A, base).replace(SHA_B, head))
                   for key, value in env.items()}
            if prepare:
                prepare(checkout, git, base, head, env, responses)
            gh = d / "bin" / "gh"
            gh.parent.mkdir()
            gh.write_text(FAKE_GH)
            gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
            # A trusted runner Git wrapper records each child's actual environment.
            # This checks isolation directly instead of relying only on flags in source.
            git_wrapper = gh.parent / "git"
            git_wrapper.write_text(
                f"#!{sys.executable}\nimport json, os, sys\n"
                f"with open({str(d / 'git-env.jsonl')!r}, 'a') as output:\n"
                "    output.write(json.dumps(dict(os.environ)) + '\\n')\n"
                f"os.execv({shutil.which('git')!r}, ['git', *sys.argv[1:]])\n")
            git_wrapper.chmod(0o755)
            (d / "responses.json").write_text(json.dumps(responses))
            github_env = d / "github_env"
            full_env = {**os.environ, "PATH": f"{gh.parent}:{os.environ['PATH']}",
                        "FAKE_GH_RESPONSES": str(d / "responses.json"),
                        "GITHUB_ENV": str(github_env), "GH_TOKEN": "x", "REPO": "o/r",
                        "SCOPE_REPO": str(checkout), **env}
            command = ["bash", str(SCRIPT), str(d / "scope")]
            if policy:
                wf = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())
                run = next(s["run"] for s in wf["jobs"]["sandboxed-build"]["steps"]
                           if s.get("name", "").startswith("Scope guard"))
                run = run[:run.index("# Whether THIS")]
                event = env.get("EVENT", "repository_dispatch")
                run = (run.replace("${{ env.IS_BATCH }}", "true" if event in self.BATCH_EVENTS else "false")
                          .replace("${{ github.event_name }}", event)
                          .replace("${{ github.repository }}", "o/r")
                          .replace("${{ steps.pr.outputs.num }}", "12"))
                (d / "gate").symlink_to(ROOT, target_is_directory=True)
                (d / "pr").symlink_to(checkout, target_is_directory=True)
                full_env.update({"MERGEBASE_EXACT": "1", "SCOPE_BASE": base, "SCOPE_HEAD": head,
                                 "PR_HEAD_REF": "", "PR_HEAD_REPO": "", "PR_USER": "", **env})
                command = ["bash", "-euo", "pipefail", "-c", run]
                github_env.touch()
            out = subprocess.run(command, env=full_env, cwd=d, capture_output=True, text=True)
            self.assertEqual(out.returncode, 0, out.stderr)
            self.assertFalse((d / "executed").exists(), "candidate Git helper ran")
            if (d / "git-env.jsonl").exists():
                for line in (d / "git-env.jsonl").read_text().splitlines():
                    git_env = json.loads(line)
                    self.assertNotIn("GH_TOKEN", git_env)
                    self.assertNotIn("GIT_CONFIG_COUNT", git_env)
                    self.assertNotIn("GIT_EXTERNAL_DIFF", git_env)
            if policy:
                return github_env.read_text(), out.stdout
            setting = github_env.read_text().strip()
            self.assertTrue(setting.startswith("LINT_ONLY_MODULES="), setting)
            if setting == "LINT_ONLY_MODULES=":
                return None
            if unmatched:
                return (d / "scope" / "unmatched.txt").read_text().splitlines()
            return pathlib.Path(setting.split("=", 1)[1]).read_text().split()

    PR_ENV = {"EVENT": "pull_request_target", "NUM": "12", "BASE": SHA_A, "HEAD": SHA_B,
              "HEAD_REPO": "fork/r"}
    PR_COMPARE = f"repos/o/r/compare/{SHA_A}...fork:{SHA_B}"

    def test_pull_request_lints_changed_tauceti_modules(self):
        # The scope comes from comparing the exact commits being built, across the fork.
        modules = self.run_scope(
            self.PR_ENV,
            {self.PR_COMPARE: {"files": [f("modified", "TauCeti/A/B.lean"),
                                         f("added", "TauCeti/C.lean"),
                                         f("renamed", "TauCeti/D'.lean"),
                                         f("removed", "TauCeti/Gone.lean"),
                                         f("modified", "README.md"),
                                         f("modified", "TauCeti/notes.md")]},
             "repos/o/r/pulls/12": pr()})
        self.assertEqual(modules, ["TauCeti.A.B", "TauCeti.C", "TauCeti.D'"])

    def test_no_tauceti_change_lints_nothing(self):
        self.assertEqual(self.run_scope(
            self.PR_ENV,
            {self.PR_COMPARE: {"files": [f("modified", "lake-manifest.json")]},
             "repos/o/r/pulls/12": pr()}), [])

    def test_pull_request_without_commits_lints_everything(self):
        for missing in ("BASE", "HEAD", "HEAD_REPO"):
            with self.subTest(missing=missing):
                self.assertIsNone(self.run_scope(dict(self.PR_ENV, **{missing: ""}), {}))

    def test_more_than_300_files_use_the_complete_local_diff(self):
        files = [f("added", f"TauCeti/M{i}.lean") for i in range(350)]
        files += [f("added", "Other/α.lean"), f("added", "TauCeti.lean")]
        responses = {self.PR_COMPARE: {"files": files[:300]}, "repos/o/r/pulls/12": pr()}
        self.assertEqual(self.run_scope(self.PR_ENV, responses, files=files),
                         sorted(f"TauCeti.M{i}" for i in range(350)))
        self.assertEqual(self.run_scope(self.PR_ENV, responses, files=files, unmatched=True),
                         ["Other/α.lean", "TauCeti.lean"])

    def test_local_diff_is_authoritative_even_when_api_files_disagree(self):
        self.assertEqual(self.run_scope(
            self.PR_ENV,
            {self.PR_COMPARE: {"files": [f("added", "TauCeti/Wrong.lean")]},
             "repos/o/r/pulls/12": pr()}, files=[f("added", "TauCeti/Actual.lean")]),
                         ["TauCeti.Actual"])

    def test_full_lint_label_and_repair_branch_lint_everything(self):
        files = {self.PR_COMPARE: {"files": [f("modified", "TauCeti/A.lean")]}}
        for info in (pr(labels=["roadmap/none", "full-lint"]), pr(head_ref="lint-repair/main")):
            with self.subTest(info=info):
                self.assertIsNone(self.run_scope(
                    self.PR_ENV, dict(files, **{"repos/o/r/pulls/12": info})))

    BATCH_EVENTS = ("merge_group", "repository_dispatch", "push")

    def test_batches_read_prs_from_squash_titles(self):
        compare = {"total_commits": 2, "commits": [{"commit": {"message": "feat: x (#7)\n\nbody"}},
                               {"commit": {"message": "fix: y (#8)"}}],
                   "files": [f("modified", "TauCeti/X.lean")]}
        for event in self.BATCH_EVENTS:
            for info in (pr(), pr(labels=["full-lint"]), pr(head_ref="lint-repair/main")):
                with self.subTest(event=event, info=info):
                    responses = {f"repos/o/r/compare/{SHA_A}...{SHA_B}": compare,
                                 "repos/o/r/pulls/7": pr(), "repos/o/r/pulls/8": info}
                    modules = self.run_scope({"EVENT": event, "BASE": SHA_A, "HEAD": SHA_B},
                                             responses)
                    self.assertEqual(modules, ["TauCeti.X"] if info == pr() else None)

    def test_unattributable_or_duplicate_batch_commits_lint_everything(self):
        for event in self.BATCH_EVENTS:
            for message in ("Merge branch main", "another commit (#7)"):
                with self.subTest(event=event, message=message):
                    compare = {"total_commits": 2, "commits": [{"commit": {"message": "feat: x (#7)"}},
                                           {"commit": {"message": message}}],
                               "files": [f("modified", "TauCeti/X.lean")]}
                    self.assertIsNone(self.run_scope(
                        {"EVENT": event, "BASE": SHA_A, "HEAD": SHA_B},
                        {f"repos/o/r/compare/{SHA_A}...{SHA_B}": compare}))

    def test_truncated_or_missing_batch_commit_count_lints_everything(self):
        for event in self.BATCH_EVENTS:
            for count in (None, 251):
                with self.subTest(event=event, count=count):
                    compare = {"total_commits": count,
                               "commits": [{"commit": {"message": "feat: x (#7)"}}],
                               "files": [f("modified", "TauCeti/X.lean")]}
                    self.assertIsNone(self.run_scope(
                        {"EVENT": event, "BASE": SHA_A, "HEAD": SHA_B},
                        {f"repos/o/r/compare/{SHA_A}...{SHA_B}": compare}))

    def test_batch_compare_cap_does_not_limit_local_files(self):
        compare = {"total_commits": 1, "commits": [{"commit": {"message": "feat: x (#7)"}}],
                   "files": [f("modified", f"TauCeti/M{i}.lean") for i in range(300)]}
        for event in self.BATCH_EVENTS:
            with self.subTest(event=event):
                self.assertEqual(self.run_scope(
                    {"EVENT": event, "BASE": SHA_A, "HEAD": SHA_B},
                    {f"repos/o/r/compare/{SHA_A}...{SHA_B}": compare,
                     "repos/o/r/pulls/7": pr()},
                    files=[f("added", f"TauCeti/M{i}.lean") for i in range(350)]),
                                 sorted(f"TauCeti.M{i}" for i in range(350)))

    def test_compare_api_failure_lints_everything(self):
        # Reproduce the bors failure: GitHub can reject compare metadata before the
        # complete local diff is read. An API outage must widen scope, not abort CI.
        error = {"_error": "gh: too many files changed (HTTP 422)"}
        for event in ("pull_request_target", "workflow_dispatch", *self.BATCH_EVENTS):
            with self.subTest(event=event):
                env = dict(self.PR_ENV, EVENT=event)
                endpoint = (self.PR_COMPARE if event not in self.BATCH_EVENTS else
                            f"repos/o/r/compare/{SHA_A}...{SHA_B}")
                self.assertIsNone(self.run_scope(
                    env, {endpoint: error}, files=[f("added", "TauCeti/A.lean")]))

    def test_unavailable_pr_lint_policy_lints_everything(self):
        # Without label/branch metadata we cannot rule out a full-lint request.
        compare = {"total_commits": 1,
                   "commits": [{"commit": {"message": "feat: x (#12)"}}]}
        for event in ("pull_request_target", "workflow_dispatch", *self.BATCH_EVENTS):
            with self.subTest(event=event):
                env = dict(self.PR_ENV, EVENT=event)
                endpoint = (self.PR_COMPARE if event not in self.BATCH_EVENTS else
                            f"repos/o/r/compare/{SHA_A}...{SHA_B}")
                self.assertIsNone(self.run_scope(
                    env, {endpoint: compare, "repos/o/r/pulls/12": {"_error": "HTTP 503"}},
                    files=[f("added", "TauCeti/A.lean")]))

    def test_moving_refs_worktree_and_live_pr_metadata_do_not_change_scope(self):
        def move(checkout, git, base, head, env, responses):
            (checkout / "TauCeti" / "Later.lean").write_text("later\n")
            git("add", ".")
            git("commit", "-qm", "later PR head")
            git("update-ref", "refs/heads/main", git("rev-parse", "HEAD"))
            responses["repos/o/r/pulls/12"]["head"]["sha"] = git("rev-parse", "HEAD")
        self.assertEqual(self.run_scope(self.PR_ENV,
                         {self.PR_COMPARE: {"files": []}, "repos/o/r/pulls/12": pr()},
                         files=[f("added", "TauCeti/Tested.lean")], prepare=move),
                         ["TauCeti.Tested"])

    def test_diverged_pr_uses_exact_merge_base_not_base_tip(self):
        def diverge(checkout, git, base, head, env, responses):
            git("checkout", "--detach", base)
            (checkout / "TauCeti/Shared.lean").write_text("unrelated main change\n")
            git("add", ".")
            git("commit", "-qm", "base advanced")
            tip = git("rev-parse", "HEAD")
            key = next(k for k in responses if "/compare/" in k)
            responses[key.replace(base, tip)] = responses.pop(key)
            env["BASE"] = tip
        self.assertEqual(self.run_scope(self.PR_ENV,
                         {self.PR_COMPARE: {"files": []}, "repos/o/r/pulls/12": pr()},
                         files=[f("added", "TauCeti/Tested.lean")], prepare=diverge,
                         initial_files={"TauCeti/Shared.lean": "unchanged at tested head\n"}),
                         ["TauCeti.Tested"])

    def test_missing_objects_or_merge_base_fall_back_to_full_lint(self):
        for problem in ("missing-checkout", "missing-object", "missing-merge-base"):
            def break_diff(checkout, git, base, head, env, responses):
                compare = next(v for k, v in responses.items() if "/compare/" in k)
                if problem == "missing-checkout":
                    env["SCOPE_REPO"] = str(checkout / "absent")
                elif problem == "missing-object":
                    compare["merge_base_commit"]["sha"] = "0" * 40
                else:
                    compare.pop("merge_base_commit")
            with self.subTest(problem=problem):
                self.assertIsNone(self.run_scope(self.PR_ENV,
                    {self.PR_COMPARE: {"files": []}, "repos/o/r/pulls/12": pr()},
                    prepare=break_diff))

    def test_unusual_filenames_are_not_lost_or_interpreted_as_modules(self):
        files = [f("added", name) for name in
                 ("TauCeti/A.lean", "TauCeti/α.lean", "Other/tab\tname.lean",
                  "Other/line\nbreak.lean")]
        responses = {self.PR_COMPARE: {"files": []}, "repos/o/r/pulls/12": pr()}
        self.assertEqual(self.run_scope(self.PR_ENV, responses, files=files), ["TauCeti.A"])
        paths = self.run_scope(self.PR_ENV, responses, files=files, unmatched=True)
        self.assertIn("Other/tab\tname.lean", paths)
        self.assertIn("TauCeti/α.lean", paths)
        self.assertTrue(paths)  # forces the axiom/dot audit fallback

    def test_candidate_and_inherited_git_configuration_cannot_influence_diff_or_leak_credentials(self):
        def poison(checkout, git, base, head, env, responses):
            marker = checkout.parent / "executed"
            command = f"touch {shlex.quote(str(marker))}"
            git("config", "diff.external", command)
            git("config", "diff.evil.textconv", command)
            git("config", "core.hooksPath", str(checkout / "hooks"))
            (checkout / ".gitattributes").write_text("*.lean diff=evil\n")
            git("add", ".gitattributes")
            git("commit", "-qm", "hostile attributes")
            # Commit attributes in the tested tree too, not only the working tree.
            new_head = git("rev-parse", "HEAD")
            key = next(k for k in responses if "/compare/" in k)
            responses[key.replace(head, new_head)] = responses.pop(key)
            env.update(HEAD=new_head, GIT_EXTERNAL_DIFF=command,
                       GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="diff.external",
                       GIT_CONFIG_VALUE_0=command)
            # A replacement ref must not replace the immutable tested tree.
            git("replace", new_head, base)
        self.assertEqual(self.run_scope(self.PR_ENV,
                         {self.PR_COMPARE: {"files": []}, "repos/o/r/pulls/12": pr()},
                         files=[f("added", "TauCeti/Tested.lean")], prepare=poison),
                         ["TauCeti.Tested"])

    def test_batch_scope_guard_handles_large_batches_and_hidden_human_paths(self):
        files = [f("added", f"TauCeti/M{i}.lean") for i in range(350)]
        settings, output = self.run_scope({}, {}, files=files, policy=True)
        self.assertEqual(settings, "")
        self.assertIn("TauCeti/M349.lean", output)
        # Include removals too: deleting trusted tooling still needs human review.
        files += [f("removed", "scripts/zzz.py")]
        settings, output = self.run_scope({}, {}, files=files, policy=True)
        self.assertIn("OUT_OF_SCOPE=1", settings)
        self.assertIn("scripts/zzz.py", output)

    def test_batch_scope_guard_fails_closed_for_newline_filenames(self):
        settings, _ = self.run_scope({}, {}, files=[f("added", "TauCeti/A\nB.lean")], policy=True)
        self.assertIn("INFRA=1", settings)

    def test_scope_guard_catches_renames_out_of_human_paths_for_prs_and_batches(self):
        files = [{**f("renamed", "TauCeti/Moved.lean"), "previous_filename": "scripts/check.sh"},
                 {**f("renamed", "TauCeti/MovedAgain.lean"), "previous_filename": "scripts/check2.sh"}]
        for event in (*self.BATCH_EVENTS[:2], "pull_request_target", "workflow_dispatch"):
            with self.subTest(event=event):
                settings, output = self.run_scope({"EVENT": event}, {}, files=files, policy=True)
                self.assertIn("OUT_OF_SCOPE=1", settings)
                self.assertIn("scripts/check.sh", output)
                self.assertIn("scripts/check2.sh", output)

    def test_policy_requires_exact_pr_merge_base_but_not_a_redundant_batch_lookup(self):
        files = [f("added", "TauCeti/A.lean")]
        for event in (*self.BATCH_EVENTS[:2], "pull_request_target", "workflow_dispatch"):
            with self.subTest(event=event):
                settings, _ = self.run_scope({"EVENT": event, "MERGEBASE_EXACT": ""}, {},
                                             files=files, policy=True)
                self.assertEqual("INFRA=1" in settings, event not in self.BATCH_EVENTS)

    def test_policy_fails_closed_when_objects_are_missing(self):
        settings, _ = self.run_scope({"SCOPE_HEAD": "0" * 40}, {},
                                     files=[f("added", "TauCeti/A.lean")], policy=True)
        self.assertIn("INFRA=1", settings)

    def test_missing_base_lints_everything(self):
        self.assertIsNone(self.run_scope({"EVENT": "push", "BASE": "0" * 40, "HEAD": SHA_B}, {}))


class PrBuildWiringTest(unittest.TestCase):
    def test_postmerge_scope_has_complete_git_history(self):
        wf = yaml.safe_load((ROOT / ".github/workflows/ci.yml").read_text())
        job = next(job for job in wf["jobs"].values() if any(
            step.get("name") == "Decide the environment-lint scope" for step in job["steps"]))
        checkout = next(step for step in job["steps"]
                        if step.get("uses", "").startswith("actions/checkout@"))
        self.assertEqual(checkout["with"]["fetch-depth"], 0)
        scope = next(step for step in job["steps"]
                     if step.get("name") == "Decide the environment-lint scope")
        self.assertEqual(scope["env"]["SCOPE_REPO"], ".")

    def test_scope_is_decided_before_the_sandbox_and_mounted_read_only(self):
        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "pr-build.yml").read_text())
        (job,) = [j for j in wf["jobs"].values()
                  if any("Build exact candidate under bwrap" in s.get("name", "")
                         for s in j.get("steps", []))]
        names = [s.get("name", "") for s in job["steps"]]
        scope = names.index("Decide the environment-lint scope")
        guard = next(i for i, name in enumerate(names) if name.startswith("Scope guard"))
        self.assertLess(names.index("Checkout workflow-pinned trusted build tooling"), guard)
        self.assertLess(names.index("Checkout the exact candidate head (untrusted contents, no credentials)"), guard)
        scope_step = job["steps"][scope]
        self.assertEqual(scope_step["env"]["SCOPE_REPO"], "pr")
        sandbox = next(i for i, n in enumerate(names) if "Build exact candidate under bwrap" in n)
        self.assertLess(scope, sandbox)
        run = job["steps"][sandbox]["run"]
        self.assertIn('--ro-bind "$LINT_SCOPE_DIR" "$LINT_SCOPE_DIR"', run)
        self.assertIn('--setenv LINT_ONLY_MODULES "${LINT_ONLY_MODULES:-}"', run)

    def test_batch_audits_stay_whole_library_with_scoped_environment_lint(self):
        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "pr-build.yml").read_text())
        self.assertIn("github.event_name == 'repository_dispatch'", wf["env"]["IS_BATCH"])
        self.assertIn("github.event_name == 'merge_group'", wf["env"]["IS_BATCH"])
        job = wf["jobs"]["sandboxed-build"]
        run = next(s["run"] for s in job["steps"] if s.get("name") == "Decide the audit scope")
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            (d / "modules.txt").write_text("TauCeti.X\n")
            (d / "unmatched.txt").write_text("")
            github_env = d / "env"
            out = subprocess.run(
                ["bash", "-c", run.replace("${{ env.IS_BATCH }}", "true")],
                env={**os.environ, "GITHUB_ENV": str(github_env), "LINT_SCOPE_DIR": str(d),
                     "LINT_ONLY_MODULES": str(d / "modules.txt"), "BUMP": "0"},
                capture_output=True, text=True)
            self.assertEqual(out.returncode, 0, out.stderr)
            self.assertEqual(github_env.read_text(), "AXIOMS_ONLY_MODULES=\nDOT_ONLY_MODULES=\n")

    def repair_exemption(self, event, files, env=None, api=None):
        """Run pr-build's empty-repair-PR exemption, extracted from the Scope guard step, with a fake
        `gh` that prints `api` (or fails when it is None). Returns (repair_pr, routed_to_human)."""
        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "pr-build.yml").read_text())
        (job,) = [j for j in wf["jobs"].values()
                  if any("Build exact candidate under bwrap" in s.get("name", "")
                         for s in j.get("steps", []))]
        run = next(s["run"] for s in job["steps"] if s.get("name", "").startswith("Scope guard"))
        start = run.index("repair_pr=0")
        end = run.index('elif [ -n "$files" ]; then', start)
        block = run[start:end] + "fi\necho \"repair_pr=$repair_pr\"\n"
        block = (block.replace("${{ github.event_name }}", event)
                      .replace("${{ github.repository }}", "o/r")
                      .replace("${{ steps.pr.outputs.num }}", "12"))
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            gh = d / "gh"
            gh.write_text("#!/usr/bin/env bash\n" + ("exit 1\n" if api is None else
                                                    f"printf '%s\\n' {shlex.quote(api)}\n"))
            gh.chmod(0o755)
            github_env = d / "github_env"
            github_env.write_text("")
            out = subprocess.run(
                ["bash", "-c", f"set -uo pipefail\nfiles={shlex.quote(files)}\n{block}"],
                env={**os.environ, "PATH": f"{d}:{os.environ['PATH']}", "GITHUB_ENV": str(github_env),
                     "PR_HEAD_REF": "", "PR_HEAD_REPO": "", "PR_USER": "", **(env or {})},
                capture_output=True, text=True)
            self.assertEqual(out.returncode, 0, out.stderr)
            return ("repair_pr=1" in out.stdout, "INFRA=1" in github_env.read_text())

    BOT = "tauceti-review-bot[bot]"

    def test_dispatched_empty_repair_pr_is_built(self):
        self.assertEqual(self.repair_exemption(
            "workflow_dispatch", "", api=f"lint-repair/main\to/r\t{self.BOT}"), (True, False))

    def test_pull_request_empty_repair_pr_is_built(self):
        env = {"PR_HEAD_REF": "lint-repair/main", "PR_HEAD_REPO": "o/r", "PR_USER": self.BOT}
        self.assertEqual(self.repair_exemption("pull_request_target", "", env=env), (True, False))

    def test_other_dispatched_empty_prs_go_to_a_human(self):
        for api in (f"feature\to/r\t{self.BOT}", f"lint-repair/main\tfork/r\t{self.BOT}",
                    "lint-repair/main\to/r\tsomeone", ""):
            with self.subTest(api=api):
                self.assertEqual(self.repair_exemption("workflow_dispatch", "", api=api),
                                 (False, True))

    def test_api_failure_goes_to_a_human(self):
        self.assertEqual(self.repair_exemption("workflow_dispatch", "", api=None), (False, True))

    def test_nonempty_diff_is_not_exempted(self):
        self.assertEqual(self.repair_exemption(
            "workflow_dispatch", "TauCeti/A.lean", api=f"lint-repair/main\to/r\t{self.BOT}"),
            (False, False))

    def test_only_the_full_lint_label_rebuilds(self):
        # pr-build does not run on label changes; a separate workflow dispatches it for full-lint.
        pr_build = yaml.safe_load((ROOT / ".github" / "workflows" / "pr-build.yml").read_text())
        self.assertNotIn("labeled", pr_build[True]["pull_request_target"]["types"])
        self.assertIn("workflow_dispatch", pr_build[True])
        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "full-lint-label.yml").read_text())
        self.assertEqual(wf[True]["pull_request_target"]["types"], ["labeled"])
        (job,) = wf["jobs"].values()
        self.assertEqual(job["if"], "${{ github.event.label.name == 'full-lint' }}")
        self.assertIn("gh workflow run pr-build.yml", job["steps"][0]["run"])

if __name__ == "__main__":
    unittest.main()
