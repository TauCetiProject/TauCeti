"""Frozen full-cache transport canary: private caches, stock Lake, no publication."""
import argparse,collections,datetime as dt,hashlib,json,math,os,platform,pwd,re,shutil,signal,subprocess,time,traceback
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--provider',required=True);args=ap.parse_args()
HERE=Path(__file__).resolve().parent;SPEC=json.loads((HERE/'cache-frozen-input.json').read_text());WORK=args.work.resolve();WORK.mkdir(parents=True,exist_ok=False);OUT=WORK/'results';OUT.mkdir();PROJECT=WORK/'project';PROJECT.mkdir()
RESULT={'schema':1,'provider':args.provider,'frozen_input':SPEC,'started_at':dt.datetime.now(dt.timezone.utc).isoformat(),'trials':[],'phases':[],'status':'running'}
def save():
 f=OUT/'result.tmp';f.write_text(json.dumps(RESULT,indent=2)+'\n');f.replace(OUT/'result.json')
def emit(v):print('CACHE_FULL_CANARY '+json.dumps(v),flush=True)
def digest(path):
 with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def invoke(cmd,name,env,cwd=PROJECT,timeout=900,check=True):
 start=time.monotonic();log=OUT/(name+'.log');timed=False
 with log.open('w') as f:
  child=subprocess.Popen([str(a) for a in cmd],cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  try:child.wait(timeout=timeout)
  except subprocess.TimeoutExpired:
   timed=True;os.killpg(child.pid,signal.SIGTERM)
   try:child.wait(timeout=10)
   except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait()
 row={'phase':name,'seconds':time.monotonic()-start,'exit':child.returncode,'censored':timed};RESULT['phases'].append(row);save();emit(row)
 if check and (timed or child.returncode):raise RuntimeError(name+': '+log.read_text(errors='replace')[-1600:])
 return row
def cache_identity(cache):
 # Cryptographic cross-arm comparison supplements native Lake's artifact hash validation.
 result={}
 for name in ('artifacts','outputs','revisions'):
  h=hashlib.sha256();files=0;size=0
  for f in sorted((cache/name).rglob('*')):
   if not f.is_file() or f.name.endswith('.tmp'):continue
   h.update(str(f.relative_to(cache/name)).encode()+b'\0'+bytes.fromhex(digest(f)));files+=1;size+=f.stat().st_size
  result[name]={'sha256':h.hexdigest(),'files':files,'bytes':size}
 return result
try:
 uid=os.getuid();assert uid!=0,'Run as the unprivileged CI user';user=pwd.getpwuid(uid)
 env={'HOME':str(Path.home()),'USER':user.pw_name,'LOGNAME':user.pw_name,'PATH':str(Path.home()/'.elan/bin')+':/usr/local/bin:/usr/bin:/bin','LANG':'C.UTF-8','GIT_CONFIG_GLOBAL':'/dev/null','GIT_CONFIG_NOSYSTEM':'1','GIT_TERMINAL_PROMPT':'0','ELAN_TOOLCHAIN':SPEC['toolchain'],'RAYON_NUM_THREADS':'16','LEAN_NUM_THREADS':'8','MATHLIB_CACHE_DIR':str(WORK/'mathlib-cache'),'LAKE_CACHE_DIR':str(WORK/'unused-cache'),'LAKE_ARTIFACT_CACHE':'false','LAKE_RESTORE_ARTIFACTS':'false'}
 real_curl=shutil.which('curl',path='/usr/bin:/bin');assert real_curl
 RESULT.update(uid=uid,machine=platform.node(),cpu_count=os.cpu_count(),curl_version=subprocess.check_output([real_curl,'--version'],text=True),curl_binary_sha256=digest(Path(real_curl)),virtualization=subprocess.run(['systemd-detect-virt'],capture_output=True,text=True).stdout.strip())
 if args.provider=='fleet-vm':assert RESULT['virtualization']=='kvm',RESULT['virtualization']
 save()
 invoke(['git','init','.'],'git-init',env);invoke(['git','remote','add','origin','https://github.com/TauCetiProject/TauCeti.git'],'git-origin',env);invoke(['git','fetch','--depth=1','origin',SPEC['revision']],'git-fetch',env,timeout=240);invoke(['git','checkout','--detach','FETCH_HEAD'],'git-checkout',env)
 assert (PROJECT/'lean-toolchain').read_text().strip()==SPEC['toolchain']
 RESULT['config_sha256']={name:digest(PROJECT/name) for name in ('lakefile.toml','lake-manifest.json','lean-toolchain')}
 invoke(['lean','--version'],'lean-version',env)
 invoke(['lake','exe','cache','get'],'mathlib-prepare',env,timeout=720)
 # The project and all executed package configuration are immutable trusted main.
 config=WORK/'cache.toml';config.write_text('cache.defaultService = "tauceti-public"\n[[cache.service]]\nname = "tauceti-public"\nkind = "s3"\nartifactEndpoint = "https://cache.taucetiproject.org/artifacts"\nrevisionEndpoint = "https://cache.taucetiproject.org/revisions"\n')
 env.update(LAKE_CONFIG=str(config),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true')
 invoke(['sudo','-n','unshare','--net','--','true'],'offline-namespace-probe',env)
 wrapper=HERE/'curl_observer.py';wrapper.chmod(0o755)
 initial=None
 for number,arm in enumerate(SPEC['sequence']):
  name=f'{number}-{arm}';cache=WORK/'trial-cache';build=PROJECT/'.lake/build'
  if cache.exists():shutil.rmtree(cache)
  if build.exists():shutil.rmtree(build)
  fetchenv=dict(env,LAKE_CACHE_DIR=str(cache),CURL=str(wrapper),TC_TRANSPORT_ARM=arm,TC_REAL_CURL=real_curl,TC_CURL_METRICS=str(OUT/(name+'-curl.jsonl')),TC_CURL_CALLS=str(OUT/(name+'-calls.jsonl')))
  trial={'index':number,'arm':arm,'cache_initially_empty':not cache.exists(),'attempts':[]};RESULT['trials'].append(trial);save();fetchstart=time.monotonic()
  for attempt in range(1,4):
   before=sum(1 for f in (cache/'artifacts').glob('*.ltar'))
   row=invoke(['lake','cache','get','--service','tauceti-public','--repo','TauCetiProject/TauCeti','--rev='+SPEC['revision']],name+f'-fetch-{attempt}',fetchenv,timeout=SPEC['diagnostic_attempt_watchdog_s'],check=False)
   row['existing_verified_artifacts_before']=before;trial['attempts'].append(row);save()
   if row['exit']==0 and not row['censored']:break
   if attempt<3:time.sleep(2)
  trial['fetch_seconds']=time.monotonic()-fetchstart;trial['fetch_success']=row['exit']==0 and not row['censored'];save()
  if not trial['fetch_success']:raise RuntimeError('No clean full cache after bounded trial attempts: '+name)
  revisions=list((cache/'revisions').rglob(SPEC['revision']+'.jsonl'));assert len(revisions)==1,revisions
  assert digest(revisions[0])==SPEC['map_sha256'],'published map changed'
  start=time.monotonic();identity=cache_identity(cache);trial['identity']=identity;trial['identity_validation_s']=time.monotonic()-start
  assert identity['artifacts']['files']>=26000,identity
  if initial is None:initial=identity
  else:assert identity==initial,(name,'different selected artifacts/outputs')
  metrics=[]
  for line in (OUT/(name+'-curl.jsonl')).read_text().splitlines():
   v=json.loads(line)
   if '/artifacts/' in (v.get('url_effective') or ''):metrics.append(v)
  timings=sorted(v['time_total'] for v in metrics if v.get('time_total') is not None)
  trial['transport']={'completed_transfer_records':len(metrics),'downloaded_bytes':sum(v.get('size_download') or 0 for v in metrics),'exit_codes':dict(collections.Counter(str(v.get('exitcode')) for v in metrics)),'http_versions':dict(collections.Counter(str(v.get('http_version')) for v in metrics)),'connections':sum(v.get('num_connects') or 0 for v in metrics),'median_transfer_s':__import__('statistics').median(timings) if timings else None,'p95_transfer_s':timings[max(0,math.ceil(.95*len(timings))-1)] if timings else None,'max_transfer_s':max(timings) if timings else None};save()
  # Native restore/build against each fresh root cache; network namespace rules out hidden refetches.
  buildenv=dict(env,LAKE_CACHE_DIR=str(cache));offline=['sudo','-n','unshare','--net','--','/usr/sbin/runuser','-u',user.pw_name,'--','env','-i',*[f'{k}={v}' for k,v in buildenv.items()],'lake','build','--iofail']
  b=invoke(offline,name+'-native-build',env,timeout=720);trial['native_build_seconds']=b['seconds'];trial['native_build_exit']=b['exit'];trial['combined_seconds']=trial['fetch_seconds']+b['seconds'];trial['native_offline_build_passed']=True;save();emit({'trial_complete':name,'fetch_s':trial['fetch_seconds'],'native_build_s':b['seconds'],'transport':trial['transport']})
 RESULT['status']='complete';RESULT['finished_at']=dt.datetime.now(dt.timezone.utc).isoformat();save();emit({'status':'complete','result':str(OUT/'result.json')})
except BaseException as error:
 RESULT['status']='failed';RESULT['error']=repr(error);RESULT['traceback']=traceback.format_exc();save();emit({'status':'failed','error':repr(error)});raise
finally:
 # Keep bounded diagnostics; private caches/source/build outputs have no future readers.
 for owned in (WORK/'project',WORK/'trial-cache',WORK/'mathlib-cache',WORK/'unused-cache'):
  if owned.exists():shutil.rmtree(owned,ignore_errors=True)
