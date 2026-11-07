#!/usr/bin/env python3
"""Observe native curl JSON without changing the JSON stream Lake consumes."""
import json,os,subprocess,sys,time
from pathlib import Path
arm=os.environ['TC_TRANSPORT_ARM'];extra=[]
if arm in ('bounds','http1_bounds'):
 extra=['--connect-timeout','10','--speed-limit','1024','--speed-time','30','--max-time','90','--retry-max-time','120']
if arm=='http1_bounds':extra.insert(0,'--http1.1')
assert arm in ('current','bounds','http1_bounds')
start=time.monotonic();rows=0
child=subprocess.Popen([os.environ['TC_REAL_CURL'],*extra,*sys.argv[1:]],stderr=subprocess.PIPE)
with Path(os.environ['TC_CURL_METRICS']).open('a',buffering=1) as metrics:
 for raw in child.stderr:
  # Preserve native curl's stream byte-for-byte for Lake's own verification/reporting.
  sys.stderr.buffer.write(raw);sys.stderr.buffer.flush()
  try:
   value=json.loads(raw)
   if not isinstance(value,dict):continue
   record={k:value.get(k) for k in ('url_effective','http_code','http_version','exitcode','errormsg','size_download','time_total','time_starttransfer','time_connect','time_appconnect','num_connects','num_retries','remote_ip')}
   record['wrapper_pid']=os.getpid();metrics.write(json.dumps(record,separators=(',',':'))+'\n');rows+=1
  except (ValueError,TypeError):pass
rc=child.wait()
with Path(os.environ['TC_CURL_CALLS']).open('a') as f:f.write(json.dumps({'pid':os.getpid(),'arm':arm,'seconds':time.monotonic()-start,'exit':rc,'records':rows,'extra':extra})+'\n')
sys.exit(rc)
