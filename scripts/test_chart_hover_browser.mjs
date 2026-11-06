// Run with Playwright installed, e.g. PLAYWRIGHT_MODULE=/tmp/browser/node_modules/playwright/index.mjs node --test scripts/test_chart_hover_browser.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createServer } from "node:http";
const { chromium } = await import(process.env.PLAYWRIGHT_MODULE || "playwright");

const plot = {
  bounds: [72, 60, 800, 348], x: [72, 472, 872],
  labels: ["2026-01-01", "2026-01-02", "2026-01-03"],
  series: [
    {label: "Lines of Lean", unit: "LOC", values: [100, 110, 125]},
    {label: "LOC since yesterday", signed: true, unit: "LOC", values: [null, 10, 15]},
    {label: "7-day moving average", unit: "LOC/day", digits: 1, values: [null, null, 2.5]},
    {label: "Relative to Mathlib", unit: "× Mathlib", digits: 2, values: [2, 2.2, 2.5]},
    {label: "<img src=x onerror=alert(1)>", values: [0, 0, 0]},
  ],
  note: "Mathlib baseline: 50 LOC at pinned aaaaaaaaaaaa (fixed for all dates)."
};
const xml = (value) => value.replaceAll("&", "&amp;").replaceAll("<", "&lt;");
const svg = (plots) => `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 900 460">
<metadata id="chart-hover">${xml(JSON.stringify(plots))}</metadata><polyline points="72,380 472,340 872,280" stroke="orange" fill="none"/></svg>`;

test("statistics tooltips work with mouse, keyboard, panels, touch and static fallbacks", async () => {
  const script = readFileSync(new URL("../web/static_files/chart-hover.js", import.meta.url));
  const css = readFileSync(new URL("../web/static_files/style.css", import.meta.url));
  const server = createServer((request, response) => {
    const path = new URL(request.url, "http://localhost").pathname;
    if (path === "/chart-hover.js") { response.setHeader("Content-Type", "text/javascript"); response.end(script); }
    else if (path === "/style.css") { response.setHeader("Content-Type", "text/css"); response.end(css); }
    else if (path === "/chart.svg" || path === "/panels.svg") {
      response.setHeader("Content-Type", "image/svg+xml");
      response.end(svg(path === "/chart.svg" ? [plot] : [plot, {...plot, bounds: [72, 420, 800, 20]}]));
    } else if (path === "/fallback.svg") {
      response.setHeader("Content-Type", "image/svg+xml");
      response.end('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 900 50"/>');
    } else if (path === "/broken.svg") {
      response.setHeader("Content-Type", "image/svg+xml");
      response.end('<svg xmlns="http://www.w3.org/2000/svg"><metadata id="chart-hover">invalid</metadata></svg>');
    } else {
      response.setHeader("Content-Type", "text/html");
      response.end(`<!doctype html><meta name="viewport" content="width=device-width,initial-scale=1">
        <link rel="stylesheet" href="/style.css"><script src="/chart-hover.js" defer></script>
        <main style="max-width:1100px;margin:auto">
        ${["chart", "panels", "fallback", "broken"].map((id) => `<img id="${id}" class="loc-graph chart-hover" src="/${id}.svg" alt="${id}">`).join("")}</main>`);
    }
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  let browser;
  try {
    browser = await chromium.launch({headless: true});
    const page = await browser.newPage({viewport: {width: 1200, height: 900}});
    const errors = [];
    page.on("pageerror", (error) => errors.push(error.message));
    const url = `http://127.0.0.1:${server.address().port}/`;
    await page.goto(url);
    await page.waitForSelector("#chart[tabindex]");
    const image = page.locator("#chart");
    const box = await image.boundingBox();
    await page.mouse.move(box.x + box.width * 870/900, box.y + box.height * 280/460);
    const tip = page.locator(".chart-tooltip:visible");
    assert.match(await tip.innerText(), /2026-01-03 \(UTC\)/);
    assert.match(await tip.innerText(), /125 LOC/);
    assert.match(await tip.innerText(), /\+15 LOC/);
    assert.match(await tip.innerText(), /2.5 LOC\/day/);
    assert.match(await tip.innerText(), /2.5 × Mathlib/);
    assert.equal(await tip.locator("img").count(), 0); // Labels remain text.
    const tipBox = await tip.boundingBox();
    assert.ok(tipBox.x >= 0 && tipBox.x + tipBox.width <= 1200);
    await image.focus();
    await page.keyboard.press("ArrowLeft");
    assert.match(await tip.innerText(), /2026-01-02/);
    await page.keyboard.press("Home");
    assert.match(await tip.innerText(), /Not available/);
    await page.keyboard.press("End");
    assert.match(await tip.innerText(), /125 LOC/);
    await page.keyboard.press("Escape");
    assert.equal(await page.locator(".chart-tooltip:visible").count(), 0);
    await page.mouse.move(0, 0);
    await page.locator("#panels").focus();
    await page.keyboard.press("ArrowDown");
    assert.ok(await page.locator("#panels").evaluate((img) => parseFloat(img.parentElement.querySelector(".chart-hover-guide").style.top) > 90));
    await page.keyboard.press("Escape");
    assert.equal(await page.locator("#fallback[tabindex], #broken[tabindex]").count(), 0);
    assert.deepEqual(errors, []);

    const mobile = await browser.newPage({viewport: {width: 390, height: 844}, isMobile: true, hasTouch: true});
    await mobile.goto(url);
    await mobile.waitForSelector("#chart[tabindex]");
    const mobileBox = await mobile.locator("#chart").boundingBox();
    await mobile.touchscreen.tap(mobileBox.x + mobileBox.width * 472/900, mobileBox.y + mobileBox.height * 300/460);
    const mobileTip = mobile.locator(".chart-tooltip:visible");
    assert.match(await mobileTip.innerText(), /2026-01-02/); // Tap focus must preserve the chosen point.
    const mobileTipBox = await mobileTip.boundingBox();
    assert.ok(mobileTipBox.x >= 0 && mobileTipBox.x + mobileTipBox.width <= 390);
    await mobile.touchscreen.tap(2, 2);
    assert.equal(await mobile.locator(".chart-tooltip:visible").count(), 0);
  } finally {
    await browser?.close();
    await new Promise((resolve) => server.close(resolve));
  }
});
