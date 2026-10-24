import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import vm from "node:vm";
const source = readFileSync(
  new URL("../web/static_files/ci-live.js", import.meta.url),
  "utf8",
);
class Element {
  constructor() {
    this.dataset = {};
    this.children = [];
    this.textContent = "";
  }
  append(...nodes) {
    this.children.push(...nodes);
  }
  get textContent() {
    return this.text + this.children.map((node) => node.textContent).join("");
  }
  set textContent(value) {
    this.text = String(value);
    this.children = [];
  }
  replaceChildren() {
    this.text = "";
    this.children = [];
  }
}
async function browser(responses, images = [], failImage = false, date = Date) {
  const elements = Object.fromEntries(
    ["status", "counts", "backlog"].map((n) => [
      "[data-ci-" + n + "]",
      new Element(),
    ]),
  );
  const root = new Element();
  root.querySelector = (q) => elements[q];
  const document = {
    hidden: false,
    baseURI: "https://taucetiproject.org/ci/",
    querySelector: () => root,
    querySelectorAll: () => images,
    createElement: () => new Element(),
    addEventListener: (n, f) => (document.listener = f),
  };
  const requests = [],
    timers = [];
  vm.runInNewContext(source, {
    document,
    URL,
    Image: class {
      set src(value) {
        if (failImage) this.onerror();
        else this.onload();
      }
    },
    Date: date,
    Set,
    Promise,
    AbortSignal,
    clearTimeout: () => {},
    setTimeout: (f) => {
      timers.push(f);
      return timers.length;
    },
    fetch: async (url, opts) => {
      requests.push({ url, opts });
      const r = responses.shift();
      if (r instanceof Error) throw r;
      return r;
    },
  });
  await new Promise((r) => setImmediate(r));
  return { elements, root, document, requests, timers };
}
test("shadow reports retain fallbacks and hidden pages stop polling", async () => {
  const b = await browser([
    Response.json({ schema: "tauceti-ci.manifest/v1", mode: "shadow" }),
  ]);
  assert.match(b.elements["[data-ci-status]"].textContent, /validated/);
  assert.equal(
    b.requests[0].url,
    "https://ci-data.taucetiproject.org/v1/ci/manifest.json",
  );
  b.document.hidden = true;
  b.timers[0]();
  await new Promise((r) => setImmediate(r));
  assert.equal(b.requests.length, 1);
});
test("failed refresh retains the successful snapshot and labels its age", async () => {
  const manifest = {
    schema: "tauceti-ci.manifest/v1",
    mode: "live",
    current: {
      as_of: new Date().toISOString(),
      running: { github: 2 },
      queued: { namespace: 1 },
    },
    groups: {},
    assets: {},
  };
  const b = await browser([
    Response.json(manifest, { headers: { etag: "revision" } }),
    new Error("offline"),
  ]);
  assert.match(b.elements["[data-ci-counts]"].textContent, /2 running/);
  b.timers[0]();
  await new Promise((r) => setImmediate(r));
  assert.match(b.elements["[data-ci-counts]"].textContent, /2 running/);
  assert.match(
    b.elements["[data-ci-status]"].textContent,
    /Updates paused.*last updated/,
  );
  assert.equal(b.requests[1].opts.headers["If-None-Match"], "revision");
});
test("current activity presents runner counts without exposing raw run records", async () => {
  const manifest = {
    schema: "tauceti-ci.manifest/v1",
    mode: "live",
    current: {
      computed_at: new Date().toISOString(),
      as_of: new Date(Date.now() - 20 * 60 * 1000).toISOString(),
      running: { github: 12, namespace: 9, eastanglia: 2, leanfro: 1, "self-hosted": 1 },
      queued: { github: 2 },
      builds: [{ repo: "TauCetiProject/TauCeti", run: "39201955793", attempt: 1, status: "in_progress" }],
      ready_to_merge: { count: 4, complete: true, at: new Date().toISOString() },
    },
  };
  const b = await browser([Response.json(manifest)]);
  const cells = b.elements["[data-ci-counts]"].children;
  assert.deepEqual(cells.map((cell) => cell.dataset.runner), ["github", "namespace", "eastanglia", "leanfro", "self-hosted"]);
  assert.match(cells[0].textContent, /GitHub-hosted12 running 2 waiting/);
  assert.match(cells[1].textContent, /Namespace9 running 0 waiting/);
  assert.match(cells[2].textContent, /eastanglia2 running 0 waiting/);
  assert.match(cells[3].textContent, /leanfro1 running 0 waiting/);
  assert.match(cells[4].textContent, /Other self-hosted1 running/);
  assert.match(b.elements["[data-ci-status]"].textContent, /^Updated just now$/);
  assert.equal(b.root.dataset.stale, "false");
  assert.equal(b.elements["[data-ci-backlog]"].textContent, "4 pull requests ready to merge.");
  assert.doesNotMatch(cells.map((cell) => cell.textContent).join(""), /39201955793|attempt|in_progress/);
  assert.ok(b.requests.every((request) => request.url.startsWith("https://ci-data.taucetiproject.org/")));
});
test("fresh publication does not conceal incomplete inventory or stale merge counts", async () => {
  const b = await browser([Response.json({
    schema: "tauceti-ci.manifest/v1", mode: "live",
    current: {
      computed_at: new Date().toISOString(),
      as_of: new Date(Date.now() - 31 * 60 * 1000).toISOString(),
      running: { github: 1 },
      ready_to_merge: { count: 4, complete: true, at: new Date(Date.now() - 31 * 60 * 1000).toISOString() },
    },
  })]);
  assert.match(b.elements["[data-ci-status]"].textContent, /Counts may be incomplete/);
  assert.equal(b.root.dataset.stale, "true");
  assert.equal(b.elements["[data-ci-backlog]"].hidden, true);
});
test("unchanged charts keep readable age labels current without marking fleet bins as daily data", async () => {
  let clock = Date.now();
  class Clock extends Date { static now() { return clock; } }
  const figure = new Element();
  figure.querySelector = () => figure.children.find((node) => node.dataset.ciChartAge !== undefined);
  const image = { src: "https://ci-data.taucetiproject.org/v1/ci/assets/abcdef/ci-fleet-72h.svg", closest: () => figure };
  const timestamp = new Date(clock).toISOString();
  const b = await browser([
    Response.json({
      schema: "tauceti-ci.manifest/v1", mode: "live",
      current: { computed_at: timestamp, as_of: timestamp },
      groups: { fleet: { status: "updated", published_at: timestamp } },
      assets: { "ci-fleet-72h.svg": { url: "/v1/ci/assets/abcdef/ci-fleet-72h.svg" } },
    }),
    new Response(null, { status: 304 }),
  ], [image], false, Clock);
  assert.equal(figure.children[0].textContent, "Updated just now.");
  clock += 2 * 60 * 1000;
  b.timers[0]();
  await new Promise((resolve) => setImmediate(resolve));
  assert.equal(figure.children[0].textContent, "Updated 2 minutes ago.");
});
test("a failed chart download retains its previous image", async () => {
  const image = {
    src: "https://taucetiproject.org/static/ci-build-duration.svg",
    closest: () => null,
  };
  const manifest = {
    schema: "tauceti-ci.manifest/v1",
    mode: "live",
    current: { as_of: new Date().toISOString() },
    groups: { daily: { status: "updated" } },
    assets: {
      "ci-build-duration.svg": {
        url: "/v1/ci/assets/abcdef/ci-build-duration.svg",
      },
    },
  };
  await browser([Response.json(manifest)], [image], true);
  assert.equal(
    image.src,
    "https://taucetiproject.org/static/ci-build-duration.svg",
  );
});
