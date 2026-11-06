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
await page.goto(url+'/ci/#queue?batch=1');
await page.getByRole('heading',{name:'Batch 1 · head',exact:true}).waitFor();
assert.equal(await page.locator('.ops-table tbody tr').count(),100);
assert.equal(await page.locator('.ops-table img').count(),0);
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('<img src=x onerror=alert(1)>'));
await page.getByRole('button',{name:'Next',exact:true}).click();
assert.ok((await page.locator('.ops-pager').innerText()).includes('101–200 of 1200'));
await page.getByRole('link',{name:'Runners',exact:true}).click();
await page.getByRole('heading',{name:'yael',exact:true}).waitFor();
assert.equal(await page.locator('.ops-job').count(),100);
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
await page.getByRole('link',{name:'History',exact:true}).first().click();
await page.getByRole('heading',{name:'Last 24 hours',exact:true}).waitFor();
await page.getByRole('heading',{name:'Pilot exit criteria',exact:true}).waitFor();
await page.setViewportSize({width:390,height:844});
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
replaceDomain('hosts',h=>{h.hosts[0].connected=false;h.hosts[0].observed_at=new Date(fixture.clock-120000).toISOString();});
await page.getByRole('link',{name:'Runners',exact:true}).click();
await page.clock.fastForward(20000);
await page.waitForFunction(()=>document.querySelector('.ops-host')?.textContent.includes('disconnected'));
assert.ok((await page.locator('[data-ops-view]').innerText()).includes('600 running'));
assert.ok((await page.locator('.ops-host').innerText()).includes('delayed'));
await page.getByRole('link',{name:'Queue',exact:true}).click();
await page.getByRole('heading',{name:'Batch 1 · head',exact:true}).waitFor();
// A publisher disconnect retains facts and visibly ages, without false zeros.
await page.route('https://ci-data.taucetiproject.org/v1/operations/manifest.json',route=>route.fulfill({status:503,body:'{}',headers:{'access-control-allow-origin':'*'}}));
await page.clock.fastForward(30000);
await page.getByText(/fetch failed; last successful observations retained/).waitFor();
assert.equal(await page.locator('.ops-table tbody tr').count(),100);
assert.deepEqual(errors,[]);
console.log('browser: pagination, PR search, runner join, history, escaping, mobile and independent observer failures passed');
await browser.close();
await new Promise(resolve=>server.close(resolve));
