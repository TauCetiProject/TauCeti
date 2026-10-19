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
  replaceChildren() {
    this.children = [];
  }
}
async function browser(responses, images = [], failImage = false) {
  const elements = Object.fromEntries(
    ["status", "counts", "builds", "freshness"].map((n) => [
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
    Date,
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
    /Last successful snapshot/,
  );
  assert.equal(b.requests[1].opts.headers["If-None-Match"], "revision");
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
