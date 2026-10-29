"""Exercise the workflow's actual trusted identity resolver without network I/O."""
import copy
import json
from pathlib import Path
from unittest import mock
import unittest

import yaml
import bors_observation as authority
from bors_train_identity import candidate_ref

WORKFLOW = yaml.safe_load((Path(__file__).resolve().parents[1] /
                          '.github/workflows/pr-build.yml').read_text())
STEP = next(s for s in WORKFLOW['jobs']['sandboxed-build']['steps'] if s.get('id') == 'pr')
BATCH = dict(id=7, base='main', state='running', head_sha='a' * 40, base_sha='b' * 40)
OBSERVATION = dict(schema='tauceti-bors.observation/v1', repo='TauCetiProject/TauCeti', base='main',
                   requested_batch=BATCH)


def resolve(data):
    return candidate_ref(data, 'a' * 40, 'b' * 40, batch_id=7)


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
                with self.assertRaises(ValueError):
                    resolve(data)
        for field, value in [('schema', 'other'), ('repo', 'other/repo'), ('requested_batch', None)]:
            data = copy.deepcopy(OBSERVATION)
            data[field] = value
            with self.assertRaises(ValueError):
                resolve(data)

    def test_refs_are_derived_from_positive_integer_generations(self):
        for cid, generation, ref in [(True, 1, 'staging-candidate-True-1'),
                (1, 0, 'staging-candidate-1-0'), (1, 1, 'main'),
                ('1', 1, 'staging-candidate-1-1'), (1, -1, 'staging-candidate-1--1')]:
            data = copy.deepcopy(OBSERVATION)
            data['requested_batch']['train'] = dict(candidate_id=cid, generation=generation, staging_ref=ref)
            with self.assertRaises(ValueError):
                resolve(data)

    def test_shared_fetch_is_bounded_scoped_and_named(self):
        with mock.patch('bors_observation.urllib.request.urlopen') as request:
            response = request.return_value.__enter__.return_value
            response.read.return_value = json.dumps(OBSERVATION).encode()
            self.assertEqual(authority.observation(7), OBSERVATION)
            argument = request.call_args.args[0]
            self.assertEqual(argument.full_url, authority.OBSERVATION_ROOT + '?base=main&batch_id=7')
            self.assertEqual(argument.get_header('User-agent'), 'TauCetiBorsObservation/1.0')
            self.assertEqual(argument.get_header('Cache-control'), 'no-cache')
            response.read.assert_called_with(authority.MAX_BYTES + 1)
            response.read.return_value = b'x' * (authority.MAX_BYTES + 1)
            with self.assertRaises(ValueError):
                authority.observation(7)

    def test_trusted_checkout_precedes_resolution_and_shared_validation_is_reused(self):
        steps = WORKFLOW['jobs']['sandboxed-build']['steps']
        checkout = next(i for i, s in enumerate(steps) if s.get('with', {}).get('path') == 'gate')
        resolver = next(i for i, s in enumerate(steps) if s.get('id') == 'pr')
        self.assertLess(checkout, resolver)
        self.assertEqual(steps[checkout]['with']['ref'], '${{ github.workflow_sha }}')
        self.assertIs(steps[checkout]['with']['persist-credentials'], False)
        self.assertIn('python3 gate/scripts/bors_train_identity.py', STEP['run'])
        self.assertNotIn('PY_IDENTITY', STEP['run'])

    def test_producer_and_concurrency_gates_remain(self):
        self.assertIn('bors-staging-{0}-{1}-{2}-{3}-{4}', WORKFLOW['concurrency']['group'])
        self.assertTrue(WORKFLOW['concurrency']['cancel-in-progress'])
        self.assertIn('STAGING_REF', STEP['run'])
        self.assertIn('if ! identity=$(python3 gate/scripts/ci_git.py resolve', STEP['run'])
        self.assertIn('--head "$SHA" --base-ref "$BASE_REF"', STEP['run'])
        self.assertIn('identity_args+=(--staging-ref "$STAGING_REF")', STEP['run'])


if __name__ == '__main__':
    unittest.main()
