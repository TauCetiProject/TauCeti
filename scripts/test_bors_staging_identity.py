"""Fixtures for the staging concurrency expression in pr-build.yml."""
import re
from pathlib import Path
from types import SimpleNamespace as NS
import unittest

import yaml

WORKFLOW = yaml.safe_load((Path(__file__).resolve().parents[1] /
                          '.github/workflows/pr-build.yml').read_text())
PAYLOAD = dict(batch_id=12, head_sha='a' * 40, base_sha='b' * 40, base_ref='main')


def group(*, event='repository_dispatch', action='tauceti-bors-staging',
          run=1, repo=1, payload=None, pr='', manual=''):
    github = NS(event_name=event, run_id=run, repository_id=repo, event=NS(
        action=action, client_payload=NS(**(PAYLOAD if payload is None else payload), pr=pr),
        pull_request=NS(number=pr if event == 'pull_request_target' else ''),
        merge_group=NS(head_sha='c' * 40 if event == 'merge_group' else '')))
    expression = WORKFLOW['concurrency']['group'].split('${{', 1)[1].removesuffix('}}')
    expression = re.sub(r'\s+', ' ', expression).replace('&&', ' and ').replace('||', ' or ')
    return 'pr-build-' + str(eval(expression.strip(), {'__builtins__': {},
        'github': github, 'inputs': NS(pr=manual), 'format': lambda s, *args: s.format(*args)}))


class ConcurrencyTests(unittest.TestCase):
    def test_same_candidate_supersedes_across_runs(self):
        self.assertEqual(group(), group(run=2))
        self.assertIs(WORKFLOW['concurrency']['cancel-in-progress'], True)

    def test_distinct_candidates_repositories_and_bases_are_isolated(self):
        for changes in [dict(batch_id=13), dict(head_sha='d' * 40),
                        dict(base_sha='e' * 40), dict(base_ref='pilot')]:
            with self.subTest(changes=changes):
                self.assertNotEqual(group().lower(), group(payload={**PAYLOAD, **changes}).lower())
        self.assertNotEqual(group(), group(repo=2))
        # Even case-only branch differences have distinct bors batch IDs.
        self.assertNotEqual(group().lower(), group(payload={**PAYLOAD, 'base_ref': 'Main', 'batch_id': 13}).lower())

    def test_missing_fields_fall_back_to_independent_run_keys(self):
        for field in PAYLOAD:
            for value in ['', None, False, 0]:
                with self.subTest(field=field, value=value):
                    data = {**PAYLOAD, field: value}
                    self.assertEqual(group(payload=data), 'pr-build-bors-staging-run-1')
                    self.assertEqual(group(payload=data, run=2), 'pr-build-bors-staging-run-2')

    def test_other_event_keys_are_unchanged(self):
        for arguments, expected in [
            (dict(event='pull_request_target', pr=123), '123'),
            (dict(event='workflow_dispatch', manual='123'), '123'),
            (dict(action='tauceti-bors-pr-approved', pr=123), '123'),
            (dict(event='merge_group'), 'c' * 40),
        ]:
            with self.subTest(arguments=arguments):
                self.assertEqual(group(**arguments), 'pr-build-' + expected)


if __name__ == '__main__':
    unittest.main()
