"""Exercise the workflow's checkpoint restoration with unavailable GitHub reads."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import yaml

ROOT = Path(__file__).resolve().parent.parent


class RestoreTests(unittest.TestCase):
    def restore(self, scenario, preexisting=False):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            executable = work / 'gh'
            executable.write_text(f'#!{sys.executable}\n' + r'''
import json,os,sys
from pathlib import Path
args=sys.argv[1:]
root=Path(os.environ['RUNNER_TEMP'])
with (root/'calls.jsonl').open('a') as f:f.write(json.dumps(args)+'\n')
scenario=os.environ['RESTORE_FIXTURE']
if args[0]=='api':
    if 'actions/artifacts?' in args[1]:
        if scenario=='index-error':sys.exit(1)
        print('200\n100')
    else:
        if scenario=='producer-error':sys.exit(1)
        print('false' if scenario=='untrusted-first' and args[1].endswith('/200') else 'true')
elif args[:2]==['run','download']:
    out=Path(args[args.index('-D')+1]);out.mkdir(parents=True,exist_ok=True)
    (out/'state.json').write_text('{partial' if scenario=='download-error' else '{"fixture":"trusted"}')
    if scenario=='download-error':sys.exit(1)
else:sys.exit(2)
''')
            executable.chmod(0o700)
            state = work/'stack-policy-in/state.json'
            if preexisting:
                state.parent.mkdir()
                state.write_text('{"fixture":"stale-local-file"}')
            workflow = yaml.safe_load((ROOT/'.github/workflows/stack-policy.yml').read_text())
            script = next(s['run'] for s in workflow['jobs']['enforce']['steps']
                          if s.get('name') == 'Restore latest trusted batch progress')
            result = subprocess.run(['bash','-c',script],text=True,capture_output=True,
                env={**os.environ,'PATH':str(work)+os.pathsep+os.environ['PATH'],
                     'REPO':'TauCetiProject/TauCeti','RUNNER_TEMP':str(work),'RESTORE_FIXTURE':scenario})
            calls=[json.loads(s) for s in (work/'calls.jsonl').read_text().splitlines()]
            return result, state.read_text() if state.exists() else None, calls

    def test_index_failure_requests_cold_recovery_and_discards_stale_local_state(self):
        result,state,calls=self.restore('index-error',preexisting=True)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertIsNone(state)
        self.assertIn('all current open PRs',result.stdout)

    def test_producer_read_failure_never_downloads_unverified_state(self):
        result,state,calls=self.restore('producer-error')
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertIsNone(state)
        self.assertFalse(any(c[:2]==['run','download'] for c in calls))

    def test_failed_download_discards_partial_file_for_full_recovery(self):
        result,state,calls=self.restore('download-error')
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertIsNone(state)
        self.assertIn('all current open PRs',result.stdout)

    def test_untrusted_checkpoint_is_skipped_and_trusted_checkpoint_preserved(self):
        result,state,calls=self.restore('untrusted-first')
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertEqual(json.loads(state),{'fixture':'trusted'})
        self.assertEqual([c[2] for c in calls if c[:2]==['run','download']],['100'])


if __name__=='__main__':
    unittest.main()
