"""Bounded anonymous cache reads, isolated from Lake and production workspaces."""
import collections,json,math,statistics,subprocess,time
from pathlib import Path
P=Path('cache-probe-output');P.mkdir(exist_ok=True)
urls=json.loads(Path('cache-probe-urls.json').read_text())
assert len(urls)==32 and all(u.startswith('https://cache.taucetiproject.org/artifacts/TauCetiProject/TauCeti/') and u.endswith('.art') for u in urls)
version=subprocess.check_output(['curl','--version'],text=True)
results=[]
# ABBA order; 50-way curl concurrency matches stock curl's default parallel cap.
for index,mode in enumerate(('--http2','--http1.1','--http1.1','--http2')):
 cfg=P/f'{index}.conf'
 cfg.write_text(''.join(f'url = "{u}"\noutput = "/dev/null"\n' for u in urls*128))
 cmd=['curl',mode,'--parallel','--parallel-max','50','--location','--silent','--show-error','--connect-timeout','8','--max-time','20','--retry','0','--write-out','%{json}\n','--config',str(cfg)]
 started=time.monotonic();q=subprocess.run(cmd,capture_output=True,text=True,timeout=150)
 transfers=[]
 for line in q.stdout.splitlines():
  v=json.loads(line)
  transfers.append({k:v.get(k) for k in ('url_effective','http_code','exitcode','http_version','time_total','time_starttransfer','time_connect','size_download','num_connects','errormsg','remote_ip')})
 assert len(transfers)==4096,len(transfers)
 record={'mode':mode,'exit':q.returncode,'elapsed_s':time.monotonic()-started,'stderr':q.stderr[:16000],'transfers':transfers}
 (P/f'{index}-transfers.json').write_text(json.dumps(record)+'\n')
 timings=sorted(r['time_total'] for r in transfers)
 summary={'mode':mode,'elapsed_s':record['elapsed_s'],'transfer_count':len(transfers),'bytes':sum(v['size_download'] for v in transfers),'http_codes':dict(collections.Counter(v['http_code'] for v in transfers)),'exit_codes':dict(collections.Counter(v['exitcode'] for v in transfers)),'median_transfer_s':statistics.median(timings),'p99_transfer_s':timings[math.ceil(.99*len(timings))-1],'max_transfer_s':max(timings),'connections':sum(v['num_connects'] for v in transfers)}
 results.append(summary);print(json.dumps(summary),flush=True)
(P/'result.json').write_text(json.dumps({'curl_version':version,'diagnostic_limits':'No retries; 8-second connect timeout and 20-second per-transfer timeout. Production remains unchanged; this does not reproduce unbounded default timeout behavior. Repeated object sample, not full Lake cache reconstruction.','cases':results},indent=2)+'\n')
