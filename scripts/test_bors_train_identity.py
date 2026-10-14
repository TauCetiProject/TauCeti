"""Exercise the workflow's actual trusted identity resolver without network I/O."""
import contextlib
import copy
import io
import json
import os
from pathlib import Path
from unittest import mock
import unittest

import yaml

WORKFLOW = yaml.safe_load((Path(__file__).resolve().parents[1] /
                          '.github/workflows/pr-build.yml').read_text())
STEP = next(s for s in WORKFLOW['jobs']['sandboxed-build']['steps'] if s.get('id') == 'pr')
RESOLVER = STEP['run'].split("<<'PY_IDENTITY'\n", 1)[1].split('\nPY_IDENTITY', 1)[0]
BATCH = dict(id=7, base='main', state='running', head_sha='a' * 40, base_sha='b' * 40)
OBSERVATION = dict(schema='tauceti-bors.observation/v1', repo='TauCetiProject/TauCeti',
                   requested_batch=BATCH)


def resolve(observation):
    output = io.StringIO()
    env = dict(BORS_BATCH_ID='7', BORS_BASE_REF='main', BORS_HEAD_SHA='a' * 40, BORS_BASE_SHA='b' * 40)
    with mock.patch.dict(os.environ, env), contextlib.redirect_stdout(output):
        with mock.patch('urllib.request.urlopen') as request:
            request.return_value.__enter__.return_value.read.return_value = json.dumps(observation).encode()
            exec(compile(RESOLVER, '<workflow resolver>', 'exec'), {})
            assert request.call_args.args[0].full_url == ('https://bors.taucetiproject.org/repositories/1/'
                                                 'active-batches?base=main&batch_id=7')
            assert request.call_args.args[0].get_header('User-agent') == 'TauCetiTrainIdentity/1.0'
            assert request.call_args.args[0].get_header('Cache-control') == 'no-cache'
    return output.getvalue().strip()


class TrainIdentityTests(unittest.TestCase):
    def test_legacy_serial_dispatch_uses_staging(self):
        self.assertEqual(resolve(OBSERVATION), 'staging')

    def test_two_generations_have_distinct_immutable_refs(self):
        for cid, generation in [(10, 1), (11, 1), (10, 2)]:
            data = copy.deepcopy(OBSERVATION)
            ref = f'staging-candidate-{cid}-{generation}'
            data['requested_batch']['train'] = dict(candidate_id=cid, generation=generation, staging_ref=ref)
            self.assertEqual(resolve(data), ref)

    def test_stale_or_mismatched_batch_rejected(self):
        for field, value in [('id', 8), ('base', 'pilot'), ('state', 'canceled'),
                             ('state', 'ok'), ('head_sha', 'c' * 40), ('base_sha', 'd' * 40)]:
            with self.subTest(field=field, value=value):
                data = copy.deepcopy(OBSERVATION)
                data['requested_batch'][field] = value
                with self.assertRaises(SystemExit):
                    resolve(data)
        for field, value in [('schema', 'other'), ('repo', 'other/repo'), ('requested_batch', None)]:
            data = copy.deepcopy(OBSERVATION)
            data[field] = value
            with self.assertRaises(SystemExit):
                resolve(data)

    def test_refs_are_derived_from_positive_integer_generations(self):
        for cid, generation, ref in [(True, 1, 'staging-candidate-True-1'),
                (1, 0, 'staging-candidate-1-0'), (1, 1, 'main'),
                ('1', 1, 'staging-candidate-1-1'), (1, -1, 'staging-candidate-1--1')]:
            data = copy.deepcopy(OBSERVATION)
            data['requested_batch']['train'] = dict(candidate_id=cid, generation=generation, staging_ref=ref)
            with self.assertRaises(SystemExit):
                resolve(data)

    def test_producer_and_concurrency_gates_remain(self):
        self.assertIn('bors-staging-{0}-{1}-{2}-{3}-{4}', WORKFLOW['concurrency']['group'])
        self.assertTrue(WORKFLOW['concurrency']['cancel-in-progress'])
        self.assertIn('STAGING_REF', STEP['run'])
        self.assertIn('compare/$BASE_REF...$SHA', STEP['run'])


if __name__ == '__main__':
    unittest.main()
