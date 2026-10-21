/* Public reports only: this module never calls GitHub or carries credentials. */
(function () {
  "use strict";
  var root = document.querySelector("[data-ci-live]");
  if (!root) return;
  var origin = "https://ci-data.taucetiproject.org";
  var endpoint = origin + "/v1/ci/manifest.json";
  var etag,
    timer,
    pending = false,
    last;
  var status = root.querySelector("[data-ci-status]");
  var counts = root.querySelector("[data-ci-counts]");
  var backlog = root.querySelector("[data-ci-backlog]");
  function age(value) {
    var seconds = Math.max(0, (Date.now() - Date.parse(value)) / 1000);
    if (!Number.isFinite(seconds)) return "at an unknown time";
    if (seconds < 60) return "just now";
    var amount = Math.floor(seconds / 60), unit = "minute";
    if (seconds >= 3600) {
      amount = Math.floor(seconds / 3600);
      unit = "hour";
    }
    if (seconds >= 86400) {
      amount = Math.floor(seconds / 86400);
      unit = "day";
    }
    return amount + " " + unit + (amount === 1 ? "" : "s") + " ago";
  }
  function group(file) {
    if (file.indexOf("ci-fleet-") === 0) return "fleet";
    if (file === "ci-queue-size.svg") return "queue";
    if (file === "ci-bors-staging.svg") return "staging";
    if (file === "ci-failures.svg" || file === "ci-build-phases.svg")
      return "details";
    return "daily";
  }
  function chartNote(image, manifest) {
    var file = new URL(image.src, document.baseURI).pathname.split("/").pop();
    var asset = (manifest.assets || {})[file];
    if (!asset || image.src !== origin + asset.url) return;
    var figure = image.closest("figure");
    if (!figure) return;
    var note = figure.querySelector("[data-ci-chart-age]");
    if (!note) {
      note = document.createElement("p");
      note.dataset.ciChartAge = "";
      note.className = "ci-chart-age";
      figure.append(note);
    }
    var name = group(file), data = (manifest.groups || {})[name] || {};
    var text = "Updated " + age(data.published_at) + ".";
    if (data.status === "stale" || data.status === "error")
      text = "Last available chart. " + text;
    if (name === "daily" || name === "details") text += " Today is provisional.";
    if (data.pending) text += " Some build details are still arriving.";
    if (data.gaps) text += " Some source data is unavailable.";
    note.textContent = text;
    note.title = "Published: " + (data.published_at || "unknown") +
      "; inventory checked through: " + (data.source_through || "unknown");
  }
  function report(manifest, disconnected) {
    var current = manifest.current || {};
    var updated = current.computed_at || manifest.generated_at || current.as_of;
    var delayed = !Number.isFinite(Date.parse(updated)) ||
      Date.now() - Date.parse(updated) > 3 * 60 * 1000;
    var incomplete = current.truncated || !Number.isFinite(Date.parse(current.as_of)) ||
      Date.now() - Date.parse(current.as_of) > 30 * 60 * 1000;
    status.textContent =
      (disconnected
        ? "Updates paused · last updated "
        : delayed
          ? "Updates delayed · last updated "
          : incomplete
            ? "Counts may be incomplete · updated "
            : "Updated ") + age(updated);
    status.title = "Counts refreshed: " + (updated || "unknown") +
      "; inventory checked through: " + (current.as_of || "unknown");
    root.dataset.stale = String(!!(disconnected || delayed || incomplete));
    var names = {
      github: "GitHub-hosted",
      namespace: "Namespace",
      "self-hosted": "Self-hosted",
      unknown: "Unassigned",
    };
    var kinds = new Set(
      ["github", "namespace", "self-hosted"].concat(
        Object.keys(current.running || {}),
        Object.keys(current.queued || {}),
      ),
    );
    counts.replaceChildren();
    kinds.forEach(function (kind) {
      var cell = document.createElement("div");
      cell.dataset.runner = kind;
      var label = document.createElement("dt");
      label.textContent = names[kind] || "Other runners";
      var value = document.createElement("dd");
      var running = document.createElement("strong");
      running.textContent = String((current.running || {})[kind] || 0);
      var caption = document.createElement("span");
      caption.textContent = " running";
      var waiting = document.createElement("span");
      waiting.className = "ci-live-waiting";
      waiting.textContent = " " + ((current.queued || {})[kind] || 0) + " waiting";
      value.append(running, caption, waiting);
      cell.append(label, value);
      counts.append(cell);
    });
    var ready = current.ready_to_merge;
    backlog.hidden = !ready || !ready.complete ||
      !Number.isFinite(Date.parse(ready.at)) || Date.now() - Date.parse(ready.at) > 30 * 60 * 1000;
    backlog.textContent = backlog.hidden ? "" : ready.count +
      " pull request" + (ready.count === 1 ? "" : "s") + " ready to merge.";
    document.querySelectorAll("img.loc-graph").forEach(function (image) {
      chartNote(image, manifest);
    });
  }
  function preload(url) {
    return new Promise(function (resolve, reject) {
      var image = new Image();
      var timeout = setTimeout(reject, 15000);
      image.onload = function () {
        clearTimeout(timeout);
        resolve();
      };
      image.onerror = function () {
        clearTimeout(timeout);
        reject();
      };
      image.src = url;
    });
  }
  async function apply(manifest) {
    if (manifest.schema !== "tauceti-ci.manifest/v1")
      throw new Error("Unknown manifest");
    if (manifest.mode !== "live") {
      last = null;
      counts.replaceChildren();
      backlog.hidden = true;
      status.textContent =
        "Live reporting is being validated. Historical charts remain available below.";
      return;
    }
    last = manifest;
    report(manifest, false);
    var images = Array.from(document.querySelectorAll("img.loc-graph"));
    await Promise.allSettled(
      images.map(async function (image) {
        var file = new URL(image.src, document.baseURI).pathname
          .split("/")
          .pop();
        var asset = (manifest.assets || {})[file];
        if (
          !asset ||
          !/^\/v1\/ci\/assets\/[a-f0-9]+\/[a-z0-9-]+\.svg$/.test(asset.url)
        )
          return;
        var url = origin + asset.url;
        if (image.src === url) return;
        await preload(url);
        image.src = url;
        chartNote(image, manifest);
      }),
    );
  }
  function schedule() {
    clearTimeout(timer);
    if (!document.hidden) timer = setTimeout(refresh, 60000);
  }
  async function refresh() {
    if (pending || document.hidden) return;
    pending = true;
    try {
      var response = await fetch(endpoint, {
        headers: etag ? { "If-None-Match": etag } : {},
        signal: AbortSignal.timeout(15000),
      });
      if (response.status === 304) {
        if (last) report(last, false);
      } else {
        if (!response.ok) throw new Error("Report unavailable");
        await apply(await response.json());
        etag = response.headers.get("ETag");
      }
    } catch (_) {
      if (last) report(last, true);
      else
        status.textContent =
          "Live counts are unavailable. Charts remain available.";
    } finally {
      pending = false;
      schedule();
    }
  }
  document.addEventListener("visibilitychange", function () {
    clearTimeout(timer);
    if (!document.hidden) refresh();
  });
  refresh();
})();
