"""Bounded real-Git regressions for dispatch-time integration and trust boundaries."""
import base64
import copy
import json
import os
import re
import sys
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import yaml
import prepare_pr_integration as integration

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = yaml.safe_load((ROOT / '.github/workflows/pr-build.yml').read_text())
STEPS = WORKFLOW['jobs']['sandboxed-build']['steps']


class IntegrationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / 'history'
        self.repo.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.name', 'fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.write('lakefile.toml', 'name = "TauCeti"\n')
        self.write('lean-toolchain', 'leanprover/lean4:v4.35.0-rc3\n')
        self.write('lake-manifest.json', json.dumps({'packages': [{'name': 'mathlib', 'rev': '3b531c35df33d6bbe64b4e87dec056211d3a5676'}]}) + '\n')
        self.write('TauCeti.lean', '')
        self.write('TauCeti/Common.lean', 'common\n')
        self.write('TauCeti/Delete.lean', 'delete\n')
        self.write('TauCeti/Rename.lean', 'rename\n')
        self.ancestor = self.commit('ancestor')
        self.git('checkout', '-q', '-b', 'author')
        self.write('TauCeti/KnuthCorrespondence.lean', 'import Mathlib.Data.Prod.Lex\n')
        self.head = self.commit('PR')
        self.git('checkout', '-q', '-b', 'main-fixture', self.ancestor)
        self.write('lean-toolchain', 'leanprover/lean4:v4.35.0\n')
        self.write('lake-manifest.json', json.dumps({'packages': [{'name': 'mathlib', 'rev': '074063781836922cb02701cd12943c9f51731afa'}]}) + '\n')
        self.write('TauCeti/Common.lean', 'main change\n')
        self.write('TauCeti/AddedOnMain.lean', 'new on main\n')
        self.git('rm', '-q', 'TauCeti/Delete.lean')
        self.git('mv', 'TauCeti/Rename.lean', 'TauCeti/RenamedOnMain.lean')
        self.base = self.commit('new main pins and sources')

    def git(self, *args, cwd=None, **kwargs):
        return subprocess.check_output(['git', *args], cwd=cwd or self.repo, text=True, **kwargs).strip()

    def write(self, path, text):
        target = self.repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def commit(self, message):
        self.git('add', '-A')
        self.git('commit', '-qm', message)
        return self.git('rev-parse', 'HEAD')

    def checkouts(self, head=None, base=None, suffix=''):
        candidate, policy = self.root / ('pr' + suffix), self.root / ('base' + suffix)
        for path, revision in ((candidate, head or self.head), (policy, base or self.base)):
            self.git('-c', 'advice.detachedHead=false', 'clone', '-q', '--no-local', str(self.repo), str(path))
            self.git('checkout', '-q', '--detach', revision, cwd=path)
        return candidate, policy

    def prepare(self, head=None, base=None, suffix='', mode='pr-integration', **kwargs):
        candidate, policy = self.checkouts(head, base, suffix)
        record = integration.prepare(candidate, policy, head or self.head, base or self.base, mode, **kwargs)
        return record, candidate

    def test_old_pin_green_head_fails_same_dispatch_integrated_build(self):
        # Bounded compiler surrogate models the observed removed-import failure;
        # the fixture performs real Git assembly, not an extra workflow or run.
        def build(path):
            old_import = 'Mathlib.Data.Prod.Lex' in (path / 'TauCeti/KnuthCorrespondence.lean').read_text()
            stable = (path / 'lean-toolchain').read_text().strip().endswith(':v4.35.0')
            return not (old_import and stable)
        candidate, policy = self.checkouts()
        self.assertTrue(build(candidate))
        record = integration.prepare(candidate, policy, self.head, self.base, 'pr-integration')
        self.assertFalse(build(candidate))
        self.assertEqual(self.git('rev-parse', 'author'), self.head)  # no branch mutation
        self.assertEqual((candidate / 'TauCeti/Common.lean').read_text(), 'main change\n')
        self.assertTrue((candidate / 'TauCeti/AddedOnMain.lean').exists())
        self.assertFalse((candidate / 'TauCeti/Delete.lean').exists())
        self.assertFalse((candidate / 'TauCeti/Rename.lean').exists())
        self.assertTrue((candidate / 'TauCeti/RenamedOnMain.lean').exists())
        self.assertEqual(self.git('rev-parse', 'HEAD', cwd=candidate), record['tested_sha'])
        self.assertEqual(self.git('rev-parse', 'HEAD^{tree}', cwd=candidate), record['tested_tree'])
        self.assertEqual(self.git('show', '-s', '--format=%P', 'HEAD', cwd=candidate), f'{self.base} {self.head}')

    def test_existing_workflow_preparation_and_sandbox_build_catch_deprecation(self):
        candidate, policy = self.checkouts()
        (self.root / 'gate').symlink_to(ROOT)
        output, environment = self.root / 'output', self.root / 'environment'
        assembly = next(s for s in STEPS if s.get('id') == 'integration')
        env = dict(os.environ, RAW_HEAD=self.head, CAPTURED_BASE=self.base,
                   CANDIDATE_MODE='pr-integration', GITHUB_OUTPUT=str(output),
                   GITHUB_ENV=str(environment), GITHUB_STEP_SUMMARY=str(self.root / 'summary'),
                   RUNNER_TEMP=str(self.root), BUMP='0', BUMP_VALIDATED='0')
        result = subprocess.run(['bash', '-euo', 'pipefail', '-c', assembly['run']],
                                cwd=self.root, env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        identity = json.loads((self.root / 'tested-integration.json').read_text())
        self.assertIn('tested_sha=' + identity['tested_sha'], output.read_text())
        # Exercise the actual sandbox body and its --iofail build call with a
        # bounded Lake surrogate. No compiler download or extra workflow occurs.
        bin_dir = self.root / 'bin'
        bin_dir.mkdir()
        lake = bin_dir / 'lake'
        lake.write_text(f'#!{sys.executable}\n' + """import pathlib, sys
assert sys.argv[1:] == ['build', '--iofail'], sys.argv
stable = pathlib.Path('lean-toolchain').read_text().strip().endswith(':v4.35.0')
old = 'Mathlib.Data.Prod.Lex' in pathlib.Path('TauCeti/KnuthCorrespondence.lean').read_text()
if stable and old:
    print('warning: deprecated Mathlib.Data.Prod.Lex; use Mathlib.Order.Prod.Lex.Basic')
    sys.exit(1)
""")
        lake.chmod(0o755)
        (bin_dir / 'lean').write_text('#!/bin/sh\nexit 0\n')
        (bin_dir / 'lean').chmod(0o755)
        watchdog = self.root / 'watchdog'
        watchdog.mkdir()
        (watchdog / 'bin').symlink_to(bin_dir)
        env.update(PATH=str(bin_dir) + os.pathsep + os.environ['PATH'],
                   TAUCETI_TRUSTED_SCRIPTS=str(ROOT / 'scripts'),
                   WATCHDOG_TOOLCHAIN=str(watchdog), LINT_DRIVER_EXE=str(bin_dir / 'lean'),
                   IS_BATCH='false')
        raw = candidate.with_name(candidate.name + '-raw-head')
        raw_build = subprocess.run([str(lake), 'build', '--iofail'], cwd=raw, env=env)
        self.assertEqual(raw_build.returncode, 0)
        integrated_build = subprocess.run(['bash', str(ROOT / 'scripts/sandbox-build.sh')],
                                          cwd=candidate, env=env, capture_output=True, text=True)
        self.assertNotEqual(integrated_build.returncode, 0)
        self.assertIn('deprecated Mathlib.Data.Prod.Lex', integrated_build.stdout)
        self.assertEqual(self.git('rev-parse', 'author'), self.head)

    def test_deterministic_and_captured_main_does_not_become_global_barrier(self):
        first, _ = self.prepare()
        self.write('later-main', 'advance while run active')
        self.commit('advance')
        second, _ = self.prepare(suffix='2')
        self.assertEqual(first, second)
        self.assertEqual(second['base_sha'], self.base)
        self.assertNotEqual(second['base_sha'], self.git('rev-parse', 'main-fixture'))

    def test_author_add_delete_rename_survive(self):
        self.git('checkout', '-q', 'author')
        self.git('rm', '-q', 'TauCeti/Delete.lean')
        self.git('mv', 'TauCeti/Rename.lean', 'TauCeti/AuthorRename.lean')
        head = self.commit('author rename/delete')
        # Use a base with only an unrelated addition for a clean rename fixture.
        self.git('checkout', '-q', '--detach', self.ancestor)
        self.write('TauCeti/Main.lean', 'main')
        base = self.commit('main addition')
        _, candidate = self.prepare(head=head, base=base)
        self.assertTrue((candidate / 'TauCeti/AuthorRename.lean').exists())
        self.assertFalse((candidate / 'TauCeti/Delete.lean').exists())
        self.assertTrue((candidate / 'TauCeti/Main.lean').exists())

    def test_conflict_explicit_and_raw_checkout_unchanged(self):
        self.git('checkout', '-q', 'author')
        self.write('TauCeti/Common.lean', 'author change\n')
        head = self.commit('conflict')
        candidate, policy = self.checkouts(head)
        with self.assertRaisesRegex(integration.IntegrationConflict, 'not stacking evidence'):
            integration.prepare(candidate, policy, head, self.base, 'pr-integration')
        self.assertEqual(self.git('rev-parse', 'HEAD', cwd=candidate), head)

    def test_validated_bump_preserves_complete_head_pin_pair(self):
        self.git('checkout', '-q', 'author')
        self.write('lean-toolchain', 'leanprover/lean4:v4.36.0\n')
        self.write('lake-manifest.json', 'validated next Mathlib\n')
        head = self.commit('forward bump')
        with self.assertRaisesRegex(ValueError, 'lacks trusted'):
            self.prepare(head=head, pins_changed=True)
        record, candidate = self.prepare(head=head, suffix='valid', pins_changed=True, bump_validated=True)
        self.assertEqual(record['pin_resolution'], 'validated-head-pins')
        for path in integration.PINS:
            self.assertEqual((candidate / path).read_text(), self.git('show', f'{head}:{path}') + '\n')
        # Validator authority is not a waiver for unrelated source conflicts.
        self.write('TauCeti/Common.lean', 'conflict\n')
        head = self.commit('also conflicts')
        with self.assertRaises(integration.IntegrationConflict):
            self.prepare(head=head, suffix='conflict', pins_changed=True, bump_validated=True)

    def test_existing_forward_bump_validator_authorizes_the_integrated_pair(self):
        fixtures = ROOT / 'scripts/bump_manifest_fixtures'
        old = json.loads((fixtures / 'base.json').read_text())
        proposed = json.loads((fixtures / 'pr.json').read_text())
        self.git('checkout', '-q', '--detach', self.ancestor)
        self.write('lake-manifest.json', json.dumps(old))
        self.write('lean-toolchain', 'leanprover/lean4:v4.34.0-rc2\n')
        ancestor = self.commit('trusted bump ancestor')
        self.write('lake-manifest.json', json.dumps(proposed))
        head = self.commit('proposed forward bump')
        self.git('checkout', '-q', '--detach', ancestor)
        old['packages'][0]['rev'] = 'b' * 40
        self.write('lake-manifest.json', json.dumps(old))
        base = self.commit('intermediate main bump')
        self.git('update-ref', 'refs/heads/bump-head', head)
        self.git('update-ref', 'refs/heads/bump-base', base)
        candidate, policy = self.checkouts(head, base)
        historical = self.root / 'mergebase'
        self.git('clone', '-q', '--no-local', str(self.repo), str(historical))
        self.git('checkout', '-q', '--detach', ancestor, cwd=historical)
        fake = self.root / 'bin'
        fake.mkdir()
        gh = fake / 'gh'
        upstream = (fixtures / 'mathlib.json').read_bytes()
        gh.write_text(f'#!{sys.executable}\n' + f"""import sys
path = sys.argv[2]
if '/compare/' in path:
    print('ahead')
elif '/actions/workflows/' in path:
    print('1')
elif '/contents/lake-manifest.json' in path:
    print({base64.b64encode(upstream).decode()!r})
elif '/contents/lean-toolchain' in path:
    print({base64.b64encode(b'leanprover/lean4:v4.34.0-rc2').decode()!r})
else:
    sys.exit('unexpected API request: ' + path)
""")
        gh.chmod(0o755)
        env = dict(os.environ, PATH=str(fake) + os.pathsep + os.environ['PATH'])
        check = subprocess.run(['bash', str(ROOT / 'scripts/check-bump.sh'),
                                str(policy), str(historical), str(candidate)],
                               env=env, capture_output=True, text=True)
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
        record = integration.prepare(candidate, policy, head, base, 'pr-integration',
                                     pins_changed=True, bump_validated=check.returncode == 0)
        self.assertEqual(json.loads((candidate / 'lake-manifest.json').read_text()), proposed)
        self.assertEqual(record['pin_resolution'], 'validated-head-pins')
        # A malicious package edit is still rejected by the same validator.
        proposed['packages'][0]['url'] = 'https://github.invalid/attacker/mathlib'
        (candidate / 'lake-manifest.json').write_text(json.dumps(proposed))
        check = subprocess.run(['bash', str(ROOT / 'scripts/check-bump.sh'),
                                str(policy), str(historical), str(candidate)],
                               env=env, capture_output=True, text=True)
        self.assertNotEqual(check.returncode, 0)
        self.assertIn('url changed', check.stdout)

    def test_custom_merge_driver_cannot_execute_to_hide_conflicts(self):
        self.git('checkout', '-q', 'author')
        self.write('.gitattributes', 'TauCeti/Common.lean merge=evil\n')
        self.write('TauCeti/Common.lean', 'author conflict\n')
        head = self.commit('candidate merge attributes')
        candidate, policy = self.checkouts(head)
        canary = self.root / 'executed'
        self.git('config', 'merge.evil.driver', 'touch ' + str(canary), cwd=candidate)
        with self.assertRaises(integration.IntegrationConflict):
            integration.prepare(candidate, policy, head, self.base, 'pr-integration')
        self.assertFalse(canary.exists())

    def test_candidate_lakefile_cannot_execute_or_hide_integration_content(self):
        self.git('checkout', '-q', 'author')
        self.write('lakefile.lean', 'malicious config\n')
        self.write('scripts/untrusted.sh', 'do not run\n')
        head = self.commit('candidate infrastructure')
        with self.assertRaisesRegex(ValueError, 'lakefile.lean'):
            self.prepare(head=head)
        self.git('rm', '-q', 'lakefile.lean')
        head = self.commit('only candidate script')
        _, candidate = self.prepare(head=head, suffix='script')
        self.assertEqual((candidate / 'scripts/untrusted.sh').read_text(), 'do not run\n')

    def test_main_lakefile_change_is_inherited(self):
        self.write('lakefile.toml', 'trusted new main config\n')
        base = self.commit('main config')
        _, candidate = self.prepare(base=base)
        self.assertEqual((candidate / 'lakefile.toml').read_text(), 'trusted new main config\n')

    def test_git_config_hooks_filters_and_replacements_cannot_run(self):
        self.git('checkout', '-q', 'author')
        self.write('.gitattributes', '* filter=evil\n')
        head = self.commit('candidate filter attributes')
        candidate, policy = self.checkouts(head)
        canary = self.root / 'executed'
        hook = self.root / 'hook'
        hook.write_text(f'#!/bin/sh\ntouch {canary}\n')
        hook.chmod(0o755)
        self.git('config', 'core.hooksPath', str(self.root), cwd=candidate)
        (self.root / 'post-checkout').symlink_to(hook)
        self.git('config', 'filter.evil.smudge', str(hook), cwd=candidate)
        self.git('config', 'merge.evil.driver', str(hook), cwd=candidate)
        self.git('replace', head, self.base, cwd=candidate)
        with patch.dict(os.environ, GIT_CONFIG_COUNT='1', GIT_CONFIG_KEY_0='core.hooksPath', GIT_CONFIG_VALUE_0=str(self.root)):
            record = integration.prepare(candidate, policy, head, self.base, 'pr-integration')
        self.assertFalse(canary.exists())
        self.assertEqual(record['head_sha'], head)
        self.assertTrue((candidate / 'TauCeti/KnuthCorrespondence.lean').exists())

    def test_frozen_bors_and_native_merge_group_candidates_stay_exact(self):
        # A real frozen candidate is already assembled and descends from B.
        self.git('merge', '--no-edit', self.head)
        frozen = self.git('rev-parse', 'HEAD')
        for suffix in ('bors', 'merge-group'):
            candidate, policy = self.checkouts(frozen, suffix=suffix)
            before = self.git('rev-parse', 'HEAD^{tree}', cwd=candidate)
            record = integration.prepare(candidate, policy, frozen, self.base, 'frozen-candidate')
            self.assertEqual(record['tested_sha'], frozen)
            self.assertEqual(record['tested_tree'], before)
            self.assertFalse(candidate.with_name(candidate.name + '-raw-head').exists())

    def test_missing_malformed_or_wrong_dispatch_identity_rejected(self):
        record, _ = self.prepare()
        for key in ('head_sha', 'base_sha', 'tested_sha', 'tested_tree', 'mode', 'schema', 'pin_resolution'):
            changed = copy.deepcopy(record)
            del changed[key]
            with self.subTest(key=key), self.assertRaises(ValueError):
                integration.verify(changed, self.head, self.base, 'pr-integration')
        for head, base in (('bad', self.base), (self.head, ''), ('a' * 40, self.base), (self.head, 'b' * 40)):
            with self.assertRaises(ValueError):
                integration.verify(record, head, base, 'pr-integration')
        candidate, policy = self.checkouts(suffix='moved')
        with self.assertRaisesRegex(ValueError, 'checkout does not match'):
            integration.prepare(candidate, policy, self.base, self.base, 'pr-integration')


class StatusBinding(unittest.TestCase):
    def report(self, *, moved=False, retarget=False, missing=False, malformed=False, wrong_output=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'gate').symlink_to(ROOT)
            head, base, tested, tree = ('a' * 40, 'b' * 40, 'c' * 40, 'd' * 40)
            record = dict(schema=1, mode='pr-integration', head_sha=head, base_sha=base,
                          tested_sha=tested, tested_tree=tree, pin_resolution='merged')
            identity = root / 'tested-integration.json'
            if not missing:
                identity.write_text('broken JSON' if malformed else json.dumps(record))
            fake = root / 'bin'
            fake.mkdir()
            gh = fake / 'gh'
            current = ('e' * 40 if moved else head) + (' other' if retarget else ' main')
            gh.write_text(f'#!{sys.executable}\n' + r"""import json, os, sys
if sys.argv[1:3] == ['api', '-X']:
    with open(os.environ['POSTS'], 'a') as output:
        output.write(json.dumps(sys.argv[1:]) + '\n')
else:
    print(os.environ['CURRENT'])
""")
            gh.chmod(0o755)
            report = next(s['run'] for s in STEPS if s.get('id') == 'report')
            values = {'env.IS_BATCH': 'false', 'env.PINS_KNOWN': '1', 'env.SCOPE_OK': '1',
                      'steps.pr.outputs.sha': head, 'steps.pr.outputs.status_sha': head,
                      'steps.pr.outputs.base_ref': 'main', 'steps.pr.outputs.num': '42',
                      'steps.build.outcome': 'success', 'github.repository': 'o/r',
                      'github.server_url': 'https://github.invalid', 'github.run_id': '9'}
            script = re.sub(r'\$\{\{ (.*?) \}\}', lambda m: values.get(m[1], ''), report)
            env = dict(os.environ, PATH=str(fake) + os.pathsep + os.environ['PATH'],
                       RUNNER_TEMP=str(root), RAW_HEAD=head, CAPTURED_BASE=base,
                       CANDIDATE_MODE='pr-integration', TESTED_SHA='f' * 40 if wrong_output else tested,
                       TESTED_TREE=tree, CURRENT=current, POSTS=str(root / 'posts'),
                       GITHUB_OUTPUT=str(root / 'output'))
            result = subprocess.run(['bash', '-euo', 'pipefail', '-c', script],
                                    cwd=root, env=env, capture_output=True, text=True)
            posts = [json.loads(line) for line in (root / 'posts').read_text().splitlines()]
            status = {}
            for post in posts:
                self.assertIn('repos/o/r/statuses/' + head, post)
                fields = dict(arg.split('=', 1) for arg in post if '=' in arg)
                status[fields['context']] = fields
            return result, status

    def test_green_binds_raw_status_to_captured_base_and_tested_commit(self):
        result, posts = self.report()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(posts['build']['state'], 'success')
        self.assertIn('B=' + 'b' * 12, posts['build']['description'])
        self.assertIn('T=' + 'c' * 12, posts['build']['description'])
        self.assertEqual(posts['scope']['state'], 'success')
        self.assertEqual(posts['bump-guard']['state'], 'success')

    def test_head_changes_retarget_and_identity_failures_cannot_post_green(self):
        for options in (dict(moved=True), dict(retarget=True), dict(missing=True),
                        dict(malformed=True), dict(wrong_output=True)):
            with self.subTest(options=options):
                result, posts = self.report(**options)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(posts['build']['state'], 'failure')


class WorkflowContract(unittest.TestCase):
    def test_integration_after_raw_authorization_before_setup_and_second_normalization(self):
        names = [s['name'] for s in STEPS if 'name' in s]
        assembly = next(s for s in STEPS if s.get('id') == 'integration')
        at = names.index(assembly['name'])
        self.assertLess(names.index('Validate the Lake-pin bump before building'), at)
        self.assertLess(names.index('Attest exact-head Lake configuration before executing Lake'), at)
        self.assertLess(at, names.index('Fetch Mathlib with the (bump-validated) config (network, no token; no PR code)'))
        self.assertIn('rm -rf pr/.lake', assembly['run'])
        self.assertIn("'frozen-candidate' || 'pr-integration'", assembly['env']['CANDIDATE_MODE'])
        self.assertIn('gate/scripts/', assembly['run'])

    def test_report_fails_closed_and_status_remains_on_raw_head(self):
        report = next(s for s in STEPS if s.get('id') == 'report')
        self.assertIn('prepare_pr_integration.py verify', report['run'])
        self.assertIn('[ "$identity_ok" != 1 ]', report['run'])
        self.assertIn('statuses/${{ steps.pr.outputs.status_sha }}', report['run'])
        self.assertIn('integration B=${CAPTURED_BASE:0:12} T=${TESTED_SHA:0:12}', report['run'])
        self.assertIn('head_moved=1', report['run'])
        self.assertNotIn('exact-head sandboxed build and workflow-pinned audits passed', report['run'])

    def test_no_new_trigger_or_pr_cache_producer_and_pinned_sandbox_stays(self):
        triggers = WORKFLOW.get('on', WORKFLOW.get(True))
        self.assertEqual(set(triggers), {'pull_request_target', 'merge_group', 'repository_dispatch', 'workflow_dispatch'})
        stage = next(s for s in STEPS if s.get('id') == 'cache_stage')
        self.assertIn("env.IS_BATCH == 'true'", stage['if'])
        build = next(s for s in STEPS if s.get('id') == 'build')
        for boundary in ('env -i /usr/bin/bwrap', '--unshare-net', '--remount-ro /',
                         '--ro-bind "$PWD/gate"', 'gate/scripts/sandbox-build.sh'):
            self.assertIn(boundary, build['run'])
        self.assertNotIn('LAKE_CACHE_KEY', build['run'])
        self.assertIn('finalize-merge-group-build', WORKFLOW['jobs'])


if __name__ == '__main__':
    import unittest.mock
    unittest.main()
