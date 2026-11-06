/* Exercise the native operations page against bounded prepared snapshots: queue
 * and job pagination, identity joins, live refresh, failures, privacy and mobile
 * layout. Render only the CI modules so mathematical front-page examples are
 * not test dependencies; keep the landing page distinct to catch base-URL bugs.
 */
import { chromium } from 'playwright';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { gunzipSync } from 'node:zlib';
import { createServer } from 'node:http';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
const web = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const output = fs.mkdtempSync(path.join(os.tmpdir(), 'tauceti-operations-site-'));
for (const args of [['build','Site.CI','Site.Theme'], ['env','lean','--run','tests/Operations.lean','--output',output]]) {
  const result=spawnSync('lake',args,{cwd:web,stdio:'inherit'});
  if(result.status!==0) { fs.rmSync(output,{recursive:true,force:true}); process.exit(result.status||1); }
}
// The landing page must not duplicate CI: otherwise <base>-relative fragment
// links can navigate off /ci/ while this fixture still appears to work.
fs.writeFileSync(path.join(output,'index.html'),'<!doctype html><title>Landing fixture</title><p>No CI dashboard here.</p>');
const server=createServer((request,response)=>{
  let relative=decodeURIComponent(new URL(request.url,'http://localhost').pathname);
  let local=path.join(output,relative);
  if(!local.startsWith(output+path.sep)) { response.writeHead(403).end(); return; }
  try {
    if(fs.statSync(local).isDirectory())local=path.join(local,'index.html');
    const type=local.endsWith('.js')?'text/javascript':local.endsWith('.css')?'text/css':local.endsWith('.html')?'text/html':'application/octet-stream';
    response.writeHead(200,{'Content-Type':type});fs.createReadStream(local).pipe(response);
  } catch {response.writeHead(404).end();}
});
await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
const url='http://127.0.0.1:'+server.address().port;
process.on('exit',()=>{server.close();fs.rmSync(output,{recursive:true,force:true});});
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
const fixture=JSON.parse(gunzipSync(fs.readFileSync(path.join(web,'tests/fixtures/operations.json.gz'))));
const browser=await chromium.launch({headless:true});
const page=await browser.newPage({viewport:{width:1360,height:1000}});
const errors=[];page.on('pageerror',e=>errors.push(String(e)));
await page.clock.install({time:fixture.clock});
await page.route('https://ci-data.taucetiproject.org/**', route=>{
 const path=new URL(route.request().url()).pathname;
 const body=fixture.objects['public'+path];
 return route.fulfill({status:body?200:404,contentType:'application/json',headers:{'access-control-allow-origin':'*'},body:body||'{}'});
});
const initialJobsManifest=JSON.parse(fixture.objects['public/v1/operations/manifest.json']);
const jobsFixtureKey='public'+initialJobsManifest.domains.jobs.url;
const jobsFixture=JSON.parse(fixture.objects[jobsFixtureKey]);
jobsFixture.recent_completed={builds:{limit:150,returned:150,truncated:true},other:{limit:50,returned:50,truncated:true}};
fixture.objects[jobsFixtureKey]=JSON.stringify(jobsFixture);
await page.goto(url+'/ci/#queue?batch=1');
await page.getByRole('heading',{name:'Batch 1 · head',exact:true}).waitFor();
assert.equal(await page.locator('.ops-table tbody tr').count(),100);
assert.equal(await page.locator('.ops-table img').count(),0);
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('<img src=x onerror=alert(1)>'));
await page.getByRole('button',{name:'Next',exact:true}).click();
assert.ok((await page.locator('.ops-pager:visible').innerText()).includes('101–200 of 1200'));
await page.locator('.ops-waiting summary').click();
await page.locator('.ops-inputs li').first().waitFor();
assert.equal(await page.locator('.ops-inputs li').count(),100);
await page.locator('.ops-waiting').getByRole('button',{name:'Next',exact:true}).click();
assert.equal(await page.locator('.ops-inputs li').count(),20);
await page.locator('.ops-waiting summary').click();
await page.getByRole('link',{name:'Runners',exact:true}).click();
await page.getByRole('heading',{name:'yael',exact:true}).waitFor();
assert.equal(new URL(page.url()).pathname,'/ci/');
assert.equal(await page.locator('.ops-job').count(),100);
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('Recent completed builds: 150 shown from a window of up to 150; additional results omitted.'));
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('Other completed jobs: 50 shown from a window of up to 50; additional results omitted.'));

assert.ok((await page.locator('[data-ops-view]').innerText()).includes('Host yael · slot 1'));
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('CI ceiling 1 jobs · classes pr, staging'));
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('finished 8 · failed 1 · outcomes unconfirmed 2'));
await page.getByLabel('Assigned host', {exact:true}).selectOption('yael');
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('Host yael · slot 1'));
await page.getByLabel('Assigned host', {exact:true}).selectOption('all');
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('600 running'));
if(process.env.OPERATIONS_SCREENSHOTS) await page.screenshot({path:path.join(process.env.OPERATIONS_SCREENSHOTS,'runners-desktop.png'),fullPage:false});
await page.getByRole('link',{name:'Queue',exact:true}).click();
await page.getByRole('heading',{name:'Batch 1 · head',exact:true}).waitFor();
await page.getByRole('searchbox').fill('101');
await page.getByRole('button',{name:'Find PR',exact:true}).click();
await page.getByRole('heading',{name:'PR #101',exact:true}).waitFor();
await page.getByRole('searchbox').fill('20000');
await page.getByRole('button',{name:'Find PR',exact:true}).click();
await page.getByRole('heading',{name:'PR #20000',exact:true}).waitFor();
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('Agents may not edit this contribution. Source fixes must come from the pull request.'));
await page.getByRole('link',{name:'History',exact:true}).first().click();
await page.getByRole('heading',{name:'Last 24 hours',exact:true}).waitFor();
await page.getByRole('heading',{name:'Pilot exit criteria',exact:true}).waitFor();
await page.locator('.ops-history-chart').waitFor();
const initialManifest=JSON.parse(fixture.objects['public/v1/operations/manifest.json']);
const historyRoot=JSON.parse(fixture.objects['public'+initialManifest.domains.host_history.url]);
const firstHistoryHost=historyRoot.hosts[0], secondHistoryHost=historyRoot.hosts[1];
await page.route('https://ci-data.taucetiproject.org'+secondHistoryHost.pages[0].url,route=>route.fulfill({status:503,body:'{}',headers:{'access-control-allow-origin':'*'}}));
await page.getByLabel('Host',{exact:true}).selectOption(secondHistoryHost.machine_id);
await page.getByText("Host history unavailable; only this host's last successful samples are retained.",{exact:true}).waitFor();
assert.equal(await page.locator('.ops-history-chart').count(),0);
await page.getByLabel('Host',{exact:true}).selectOption(firstHistoryHost.machine_id);
await page.locator('.ops-history-chart').waitFor();
await page.setViewportSize({width:390,height:844});
await page.getByRole('link',{name:'Runners',exact:true}).click();
await page.getByRole('heading',{name:'Observed runner pools',exact:true}).waitFor();
assert.ok(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth));
await page.getByRole('link',{name:'Queue',exact:true}).click();
await page.getByRole('heading',{name:'Batch 1 · head',exact:true}).waitFor();
assert.ok(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth));
if(process.env.OPERATIONS_SCREENSHOTS) await page.screenshot({path:path.join(process.env.OPERATIONS_SCREENSHOTS,'queue-mobile.png'),fullPage:false});
// Each stale source remains distinct from a healthy publisher and other domains.
const manifestKey='public/v1/operations/manifest.json';
function replaceDomain(kind, mutate) {
  const manifest=JSON.parse(fixture.objects[manifestKey]);
  const old=manifest.domains[kind];
  const value=JSON.parse(fixture.objects['public'+old.url]);
  mutate(value);
  const serialized=JSON.stringify(value), hash=createHash('sha256').update(serialized).digest('hex');
  old.url='/v1/operations/objects/'+manifest.scope+'/'+hash+'.json';old.observed_at=value.observed_at;
  fixture.objects['public'+old.url]=serialized;
  manifest.generated_at=new Date(fixture.clock+20000).toISOString();
  fixture.objects[manifestKey]=JSON.stringify(manifest);
}
replaceDomain('queue',q=>{q.observed_at=new Date(fixture.clock-120000).toISOString();});
await page.clock.fastForward(20000);
await page.waitForFunction(()=>document.querySelector('.ops-source')?.textContent.includes('queue · delayed'));
assert.equal(await page.locator('.ops-table tbody tr').count(),100);
// A pending job snapshot cannot hold either the summary or open batch detail
// behind its request. The new event is bound through fresh immutable detail/index refs.
replaceDomain('queue',q=>{
  q.observed_at=new Date(fixture.clock+35000).toISOString();
  function store(value) {
    const body=JSON.stringify(value), hash=createHash('sha256').update(body).digest('hex');
    const ref={url:'/v1/operations/objects/'+JSON.parse(fixture.objects[manifestKey]).scope+'/'+hash+'.json'};
    fixture.objects['public'+ref.url]=body;return ref;
  }
  const shard=JSON.parse(fixture.objects['public'+q.batch_shards[1].url]);
  const batch=shard.batches.find(b=>b.id==='1');
  const detail=JSON.parse(fixture.objects['public'+batch.detail.url]);
  detail.event_pages.push(store({schema:'tauceti.operations.events/v1',records:[{at:new Date(fixture.clock+35000).toISOString(),kind:'publication_before_jobs_ready'}]}));
  const task={id:'21',kind:'rebase_conflict',state:'open',created_at:new Date(fixture.clock-90000).toISOString(),resolved_at:null,progress:{coverage:'observed',state:'sources_ready',observed_at:new Date(fixture.clock-90000).toISOString(),providers:[],models:[],cost:{recorded_usd:0,recorded_attempts:0,unknown_attempts:0},build:{stage:'preparation',completed_tasks:58742,total_tasks:60357,sampled_at:new Date(fixture.clock+35000).toISOString(),log_updated_at:new Date(fixture.clock+35000).toISOString(),last_progress_at:null}}};
  detail.task_pages.push(store({schema:'tauceti.operations.tasks/v1',records:[task]}));
  q.batches.find(b=>b.id==='1').active_tasks=[task];
  batch.detail=store(detail);q.batches.find(b=>b.id==='1').detail=batch.detail;q.batch_shards[1]=store(shard);
});
replaceDomain('jobs',j=>{j.received_at=new Date(fixture.clock+35000).toISOString();});
const pendingJobs=JSON.parse(fixture.objects[manifestKey]).domains.jobs.url;
let releaseJobs;
const jobsGate=new Promise(resolve=>{releaseJobs=resolve;});
await page.route('https://ci-data.taucetiproject.org'+pendingJobs,async route=>{
  await jobsGate;
  return route.fulfill({status:200,contentType:'application/json',headers:{'access-control-allow-origin':'*'},body:fixture.objects['public'+pendingJobs]});
});
try {
  await page.clock.fastForward(15000);
  await page.waitForFunction(()=>document.querySelector('.ops-source')?.textContent.includes('queue · observed'),{},{timeout:3000});
  await page.getByText(/publication_before_jobs_ready/).waitFor({timeout:3000});
  await page.getByText(/Reported preparation build tasks 58742 \/ 60357/).first().waitFor({timeout:3000});
  assert.ok((await page.locator('[data-ops-view]').innerText()).includes('count increase unobserved (first sample or reset)'));
} finally { releaseJobs(); }
replaceDomain('hosts',h=>{h.hosts[0].connected=false;h.hosts[0].observed_at=new Date(fixture.clock-120000).toISOString();});
await page.getByRole('link',{name:'Runners',exact:true}).click();
await page.clock.fastForward(20000);
await page.waitForFunction(()=>document.querySelector('.ops-host')?.textContent.includes('disconnected'));
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('600 running'));
assert.ok((await page.locator('.ops-host').innerText()).includes('delayed'));
await page.getByRole('link',{name:'Queue',exact:true}).click();
await page.getByRole('heading',{name:'Batch 1 · head',exact:true}).waitFor();
await page.getByRole('searchbox').fill('20000');
await page.getByRole('button',{name:'Find PR',exact:true}).click();
await page.getByRole('heading',{name:'PR #20000',exact:true}).waitFor();
replaceDomain('queue',q=>{
  const ref=q.pr_shards[20000%64], shard=JSON.parse(fixture.objects['public'+ref.url]);
  shard.prs['TauCetiProject/TauCeti#20000'].inputs[0].state='reserved';
  const body=JSON.stringify(shard), hash=createHash('sha256').update(body).digest('hex');
  ref.url=ref.url.slice(0,ref.url.lastIndexOf('/')+1)+hash+'.json';
  fixture.objects['public'+ref.url]=body;
});
await page.clock.fastForward(20000);
await page.getByText('Next event: insertion into the reserved batch.',{exact:true}).waitFor();
// A publisher disconnect retains facts and visibly ages, without false zeros.
await page.route('https://ci-data.taucetiproject.org/v1/operations/manifest.json',route=>route.fulfill({status:503,body:'{}',headers:{'access-control-allow-origin':'*'}}));
await page.clock.fastForward(30000);
await page.getByText(/fetch failed; last successful observations retained/).waitFor();
assert.equal(await page.locator('.ops-table tbody tr').count(),100);
// A changed public scope cannot reuse an old host's cached samples, even when
// the same permanent ID remains selected and its new detail pages fail.
await page.unroute('https://ci-data.taucetiproject.org/v1/operations/manifest.json');
await page.getByRole('link',{name:'History',exact:true}).first().click();
await page.locator('.ops-history-chart').waitFor();
const oldQueue=JSON.parse(fixture.objects['public'+JSON.parse(fixture.objects[manifestKey]).domains.queue.url]);
const successor=oldQueue.batches.find(b=>b.id==='2');
let releaseBatch, batchStarted;
const batchGate=new Promise(resolve=>{releaseBatch=resolve;});
const batchRequested=new Promise(resolve=>{batchStarted=resolve;});
await page.route('https://ci-data.taucetiproject.org'+successor.detail.url,async route=>{
  batchStarted();await batchGate;
  return route.fulfill({status:200,contentType:'application/json',headers:{'access-control-allow-origin':'*'},body:fixture.objects['public'+successor.detail.url]});
});
await page.getByRole('link',{name:'Queue',exact:true}).click();
await page.getByLabel('Batch',{exact:true}).selectOption('2');
await batchRequested;
await page.getByRole('link',{name:'History',exact:true}).first().click();
await page.locator('.ops-history-chart').waitFor();
const nextScope='b'.repeat(64), nextHistory=structuredClone(historyRoot);
nextHistory.hosts=[structuredClone(firstHistoryHost)];
nextHistory.hosts[0].pages.forEach(ref=>{ref.url=ref.url.replace(initialManifest.scope,nextScope);});
const nextBody=JSON.stringify(nextHistory), nextURL='/v1/operations/objects/'+nextScope+'/'+createHash('sha256').update(nextBody).digest('hex')+'.json';
fixture.objects['public'+nextURL]=nextBody;
function scopedObject(value) {
  const body=JSON.stringify(value), url='/v1/operations/objects/'+nextScope+'/'+createHash('sha256').update(body).digest('hex')+'.json';
  fixture.objects['public'+url]=body;return {url};
}
const emptyBatch=scopedObject({schema:'tauceti.operations.batches/v1',batches:[]}), emptyPR=scopedObject({schema:'tauceti.operations.prs/v1',prs:{}});
const nextQueue={...oldQueue,batches:[],claims:[],workers:[],counts:{batches:0,members:0,waiting:0},batch_shards:Array(64).fill(emptyBatch),pr_shards:Array(64).fill(emptyPR),waiting_pages:[]};
fixture.objects[manifestKey]=JSON.stringify({schema:initialManifest.schema,scope:nextScope,generated_at:new Date(await page.evaluate(()=>Date.now())).toISOString(),domains:{host_history:{url:nextURL,observed_at:nextHistory.observed_at,coverage:'recorded_samples_only'},queue:{...scopedObject(nextQueue),observed_at:nextQueue.observed_at,coverage:'observed'}}});
await page.evaluate(()=>document.dispatchEvent(new Event('visibilitychange')));
await page.getByText('Host history is unavailable or loading for this host.',{exact:true}).waitFor();
assert.equal(await page.locator('.ops-history-chart').count(),0);
releaseBatch();
await page.waitForTimeout(500);
await page.getByRole('link',{name:'Queue',exact:true}).click();
await page.getByText('No head in the last observed queue snapshot.',{exact:true}).waitFor();
assert.equal(await page.getByRole('heading',{name:'Batch 2 · open',exact:true}).count(),0);
assert.deepEqual(errors,[]);
console.log('browser: pagination, PR search, runner join, history, escaping, mobile and independent observer failures passed');
await browser.close();
await new Promise(resolve=>server.close(resolve));
