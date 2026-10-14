"""Human scope approval: exact revisions, complete batches, and unchanged guards."""
import copy
import pathlib
import os
import re
import subprocess
import unittest

import yaml

import bors_scope_approval as policy

HEAD, BASE, STAGING, SECOND = (c * 40 for c in 'abcd')
ROOT = pathlib.Path(__file__).resolve().parent.parent


def approval(pr=1, head=HEAD, base=BASE, actor_id=1001):
    return dict(pr=pr, actor_id=actor_id, head_sha=head, merge_base_sha=base)


def observation():
    return dict(schema='tauceti-bors.observation/v1', repo=policy.REPO, base='main',
                scope_approvals=[approval()], requested_batch=dict(id=12, state='running',
                base='main', base_sha=BASE, head_sha=STAGING,
                members=[dict(pr=1, head_sha=HEAD), dict(pr=2, head_sha=SECOND)]))


class ScopeApprovalTests(unittest.TestCase):
    def setUp(self):
        self.data = observation()
        self.prs = {
            1: dict(number=1, state='open', draft=False, head=dict(sha=HEAD),
                    base=dict(ref='main', sha=BASE), changed_files=1),
            2: dict(number=2, state='open', draft=False, head=dict(sha=SECOND),
                    base=dict(ref='main', sha=BASE), changed_files=1),
        }
        self.admins = [dict(id=1001, permissions=dict(admin=True))]
        self.files = {1: [dict(filename='scripts/test.sh', status='modified')],
                      2: [dict(filename='TauCeti/Example.lean', status='modified')]}

    def api(self, path):
        if path.startswith('/user/'):
            actor = int(path.split('/')[-1])
            return dict(id=actor, login=f'actor-{actor}')
        if path.startswith('collaborators/'):
            actor = int(path.split('/')[1].split('-')[-1])
            is_admin = any(a['id'] == actor for a in self.admins)
            return dict(user=dict(id=actor), permission='admin' if is_admin else 'write')
        if path.startswith('compare/'):
            return dict(merge_base_commit=dict(sha=BASE))
        parts = path.split('/')
        pr = int(parts[1])
        if len(parts) == 2:
            return copy.deepcopy(self.prs[pr])
        return copy.deepcopy(self.files[pr])

    def batch(self):
        return policy.verify(self.data, STAGING, BASE, batch_id=12, combined_paths=['scripts/test.sh', 'TauCeti/Example.lean'], api=self.api)

    def test_exact_pr_and_mixed_batch_are_approved(self):
        self.assertTrue(policy.verify(self.data, HEAD, BASE, pr=1, api=self.api))
        self.assertTrue(self.batch())

    def test_authority_follows_current_repository_admin_role(self):
        self.admins = [dict(id=1002, permissions=dict(admin=True))]
        self.assertFalse(self.batch())
        self.data['scope_approvals'] = [approval(actor_id=1002)]
        self.assertTrue(policy.verify(self.data, HEAD, BASE, pr=1, api=self.api))
        self.assertTrue(self.batch())
        self.admins = []
        self.assertFalse(self.batch())

    def test_different_admins_can_approve_restricted_members_of_one_batch(self):
        self.admins.append(dict(id=1002, permissions=dict(admin=True)))
        self.files[2] = [dict(filename='scripts/other.sh', status='added')]
        self.data['scope_approvals'] = [approval(), approval(2, SECOND, actor_id=1002)]
        self.assertTrue(policy.verify(self.data, STAGING, BASE, batch_id=12,
            combined_paths=['scripts/test.sh', 'scripts/other.sh'], api=self.api))

    def test_untrusted_accounts_and_claimed_names_do_not_grant_approval(self):
        for actor_id in [999, '1001', None, True]:
            with self.subTest(actor_id=actor_id):
                self.data['scope_approvals'] = [approval(actor_id=actor_id)]
                self.assertFalse(policy.verify(self.data, HEAD, BASE, pr=1, api=self.api))
                self.assertFalse(self.batch())
        self.data['scope_approvals'] = [dict(approval(actor_id=999), reviewer='admin')]
        self.assertFalse(self.batch())
        self.data['scope_approvals'] = [approval(), approval()]
        self.assertFalse(self.batch())

    def test_missing_or_malformed_roles_fail_closed(self):
        for result in [None, dict(user=None, permission='admin'),
                       dict(user=[], permission='admin'),
                       dict(user=dict(id=999), permission='admin')]:
            def api(path):
                return result if path.startswith('collaborators/') else self.api(path)
            with self.assertRaises(ValueError):
                self.batch_with_api(api)
        def unavailable(path):
            raise subprocess.CalledProcessError(403, 'gh')
        with self.assertRaises(subprocess.CalledProcessError):
            policy.verify(self.data, HEAD, BASE, pr=1, api=unavailable)

    def batch_with_api(self, api):
        return policy.verify(self.data, STAGING, BASE, batch_id=12,
            combined_paths=['scripts/test.sh', 'TauCeti/Example.lean'], api=api)

    def test_renamed_account_is_resolved_from_stable_id(self):
        def api(path):
            if path == '/user/1001':
                return dict(id=1001, login='new-name')
            if path == 'collaborators/new-name/permission':
                return dict(user=dict(id=1001), permission='admin')
            return self.api(path)
        self.assertTrue(self.batch_with_api(api))

    def test_wrong_actor_or_invalid_login_cannot_resolve_authority(self):
        for user in [None, dict(id=999, login='actor-1001'),
                     dict(id=1001, login='../admin'), dict(id=1001, login=None)]:
            def api(path):
                return user if path.startswith('/user/') else self.api(path)
            with self.subTest(user=user), self.assertRaises(ValueError):
                self.batch_with_api(api)

    def test_effective_permission_is_used_without_listing_collaborators(self):
        def api(path):
            self.assertNotIn('collaborators?', path)
            return self.api(path)
        self.assertTrue(self.batch_with_api(api))

    def test_only_actual_maintainer_and_exact_diff_count(self):
        for change in [dict(actor_id=999), dict(head_sha=SECOND), dict(merge_base_sha=SECOND), dict(pr=2)]:
            with self.subTest(change=change):
                self.data = observation()
                self.data['scope_approvals'][0].update(change)
                self.assertFalse(self.batch())
        self.data['scope_approvals'] = []
        self.assertFalse(self.batch())

    def test_live_push_retarget_draft_close_and_base_change(self):
        for field, value in [('head', dict(sha=SECOND)), ('base', dict(ref='other', sha=BASE)),
                             ('draft', True), ('state', 'closed')]:
            with self.subTest(field=field):
                prior = copy.deepcopy(self.prs[1])
                self.prs[1][field] = value
                with self.assertRaises(ValueError):
                    self.batch()
                self.prs[1] = prior
        self.assertFalse(policy.verify(self.data, HEAD, SECOND, pr=1, api=self.api))

    def test_batch_head_base_state_and_membership_must_match(self):
        for change in [dict(id=99), dict(head_sha=SECOND), dict(base_sha=SECOND),
                       dict(state='canceled'), dict(base='pilot'), dict(members=[]),
                       dict(members=[dict(pr=1, head_sha=HEAD)] * 2),
                       dict(members=[dict(pr=1, head_sha=None)])]:
            with self.subTest(change=change):
                self.data = observation()
                self.data['requested_batch'].update(change)
                self.assertFalse(self.batch())

    def test_other_pr_cannot_smuggle_restricted_paths(self):
        self.files[2] = [dict(filename='scripts/evil.sh', status='added')]
        self.assertFalse(self.batch())
        self.data['scope_approvals'].append(approval(2, SECOND))
        self.assertTrue(self.batch())

    def test_rename_sources_and_deletions_need_approval(self):
        for entry in [dict(filename='TauCeti/Example.lean', status='renamed', previous_filename='scripts/old'),
                      dict(filename='.github/old.yml', status='removed')]:
            self.files[2] = [entry]
            self.assertFalse(self.batch())
        self.files[2] = [dict(filename='TauCeti/Example.lean', status='renamed')]
        with self.assertRaises(ValueError):
            self.batch()

    def test_combined_restricted_paths_must_be_covered_by_an_approved_diff(self):
        self.assertFalse(policy.verify(self.data, STAGING, BASE, batch_id=12,
            combined_paths=['scripts/renamed-by-merge.sh'], api=self.api))
        self.assertFalse(policy.verify(self.data, STAGING, BASE, batch_id=12, api=self.api))

    def test_multiple_file_pages_are_complete(self):
        entries = [dict(filename=f'TauCeti/File{i}.lean', status='added') for i in range(101)]
        self.prs[2]['changed_files'] = len(entries)
        def api(path):
            if path.startswith('pulls/2/files?'):
                page = int(path.split('page=')[-1])
                return entries[(page - 1) * 100:page * 100]
            return self.api(path)
        self.assertTrue(policy.verify(self.data, STAGING, BASE, batch_id=12, combined_paths=['scripts/test.sh', 'TauCeti/Example.lean'], api=api))
        entries[-1] = dict(filename='scripts/extra.sh', status='added')
        self.assertFalse(policy.verify(self.data, STAGING, BASE, batch_id=12, combined_paths=['scripts/test.sh', 'TauCeti/Example.lean'], api=api))

    def test_incomplete_or_duplicate_file_lists_fail_closed(self):
        for count in [0, 2, 3001, None]:
            self.prs[2]['changed_files'] = count
            with self.assertRaises(ValueError):
                self.batch()
        self.prs[2]['changed_files'] = 2
        self.files[2] *= 2
        with self.assertRaises(ValueError):
            self.batch()

    def test_push_during_file_listing_is_rejected(self):
        def api(path):
            result = self.api(path)
            if '/files?' in path:
                self.prs[2]['head']['sha'] = HEAD
            return result
        with self.assertRaises(ValueError):
            policy.verify(self.data, STAGING, BASE, batch_id=12, combined_paths=['scripts/test.sh', 'TauCeti/Example.lean'], api=api)

    def test_old_or_wrong_bors_observations_are_rejected(self):
        for change in [dict(repo='fork/TauCeti'), dict(schema='old'), dict(base='pilot'),
                       dict(scope_approvals=None)]:
            self.data = observation()
            self.data.update(change)
            self.assertFalse(self.batch())


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.workflow = yaml.safe_load((ROOT / '.github/workflows/pr-build-jobs.yml').read_text())
        self.steps = self.workflow['jobs']['sandboxed-build']['steps']
        self.report = next(s['run'] for s in self.steps if s.get('id') == 'report')

    def verdict(self, **guards):
        start = self.report.index('if [ "${{ env.SCOPE_OK }}"')
        end = self.report.index('post_status scope "$sc_state" "$sc_desc"', start)
        script = self.report[start:end]
        values = dict(SCOPE_OK='1', OUT_OF_SCOPE='1')
        values.update(guards)
        script = re.sub(r'\$\{\{ env\.([A-Z_]+) \}\}', lambda m: values.get(m[1], ''), script)
        result = subprocess.run(['bash', '-c', 'python3() { return 0; }; ' + script +
                                 '\nprintf "%s" "$sc_state"'], capture_output=True, text=True,
                                env={**os.environ, 'IS_BATCH': 'false', 'TESTED_SCOPE_HEAD': HEAD,
                                     'TESTED_SCOPE_BASE': BASE, 'SCOPE_PR': '1'})
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def test_human_approval_only_waives_paths(self):
        self.assertEqual(self.verdict(), 'success')
        for guard in ['BUMP_BAD', 'INFRA', 'TOO_LARGE', 'DIFF_UNKNOWN', 'NEWFILE_TOO_LONG']:
            with self.subTest(guard=guard):
                self.assertEqual(self.verdict(**{guard: '1'}), 'failure')
        self.assertEqual(self.verdict(SCOPE_OK=''), 'failure')

    def test_all_workflow_shell_steps_parse(self):
        for job in self.workflow['jobs'].values():
            for step in job.get('steps', []):
                if 'run' in step:
                    script = re.sub(r'\$\{\{.*?\}\}', 'placeholder', step['run'])
                    result = subprocess.run(['bash', '-n'], input=script, text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, step.get('name', '') + result.stderr)

    def test_path_approval_does_not_skip_shim_guards(self):
        for step in self.steps:
            if step.get('id') in {'shim_coverage', 'shim_expiry'}:
                self.assertNotIn('OUT_OF_SCOPE', step['if'])

    def test_pr_approval_dispatch_is_not_a_batch(self):
        self.assertIn("github.event.action == 'tauceti-bors-staging'", self.workflow['env']['IS_BATCH'])
        self.assertIn('tauceti-bors-pr-approved', str(self.workflow))
        entrypoint = yaml.safe_load((ROOT / '.github/workflows/pr-build.yml').read_text())
        self.assertIn('github.event.client_payload.pr', entrypoint['concurrency']['group'])


if __name__ == '__main__':
    unittest.main()
