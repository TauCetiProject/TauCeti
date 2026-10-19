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
  var builds = root.querySelector("[data-ci-builds]");
  var freshness = root.querySelector("[data-ci-freshness]");
  function stamp(value) {
    var date = new Date(value);
    return Number.isFinite(date.getTime())
      ? date.toISOString().replace("T", " ").slice(0, 19) + " UTC"
      : "unknown";
  }
  function group(file) {
    if (file.indexOf("ci-fleet-") === 0) return "fleet";
    if (file === "ci-queue-size.svg") return "queue";
    if (file === "ci-bors-staging.svg") return "staging";
    if (file === "ci-failures.svg" || file === "ci-build-phases.svg")
      return "details";
    return "daily";
  }
  function list(target, values) {
    target.replaceChildren();
    values.forEach(function (value) {
      var li = document.createElement("li");
      if (
        value.url &&
        /^https:\/\/github\.com\/TauCetiProject\/[\w.-]+\/actions\/runs\/\d+$/.test(
          value.url,
        )
      ) {
        var a = document.createElement("a");
        a.href = value.url;
        a.textContent = value.text;
        li.append(a);
      } else li.textContent = value.text;
      target.append(li);
    });
  }
  function report(manifest, disconnected) {
    var current = manifest.current || {};
    var stale =
      !current.as_of || Date.now() - Date.parse(current.as_of) > 30 * 60 * 1000;
    status.textContent =
      (disconnected
        ? "Updates unavailable. Last successful snapshot: "
        : stale
          ? "Snapshot is stale: "
          : "Observed at ") + stamp(current.as_of);
    root.dataset.stale = String(disconnected || stale);
    var names = {
      github: "GitHub-hosted",
      namespace: "Namespace",
      "self-hosted": "self-hosted",
      unknown: "runner unassigned",
    };
    var kinds = new Set(
      Object.keys(current.running || {}).concat(
        Object.keys(current.queued || {}),
      ),
    );
    counts.textContent =
      Array.from(kinds)
        .map(function (kind) {
          return (
            (names[kind] || kind) +
            ": " +
            ((current.running || {})[kind] || 0) +
            " running, " +
            ((current.queued || {})[kind] || 0) +
            " queued"
          );
        })
        .join(" · ") || "No active jobs observed.";
    if (current.ready_to_merge && current.ready_to_merge.complete)
      counts.textContent +=
        " · Ready-to-merge backlog: " +
        current.ready_to_merge.count +
        " PRs (observed " +
        stamp(current.ready_to_merge.at) +
        ")";
    list(
      builds,
      (current.builds || [])
        .slice(0, 100)
        .map(function (job) {
          return {
            text:
              (job.repo || "") +
              " #" +
              job.run +
              " attempt " +
              job.attempt +
              ": " +
              job.status,
            url: "https://github.com/" + job.repo + "/actions/runs/" + job.run,
          };
        })
        .concat(
          (current.staging || []).map(function (run) {
            return {
              text:
                "Staging batch " +
                (run.batch || "unknown") +
                ": " +
                run.status +
                (run.members ? ", " + run.members.length + " PRs" : ""),
              url: run.url,
            };
          }),
        ),
    );
    list(
      freshness,
      Object.keys(manifest.groups || {}).map(function (name) {
        var data = manifest.groups[name];
        return {
          text:
            name +
            ": " +
            data.status +
            "; source through " +
            stamp(data.source_through) +
            "; published " +
            stamp(data.published_at) +
            (data.pending ? "; " + data.pending + " details pending" : "") +
            (data.gaps ? "; " + data.gaps + " source gaps" : ""),
        };
      }),
    );
    if (current.truncated)
      counts.textContent += " · Active inventory is incomplete.";
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
      counts.textContent = "";
      builds.replaceChildren();
      freshness.replaceChildren();
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
        var figure = image.closest("figure");
        if (!figure) return;
        var note = figure.querySelector("[data-ci-chart-age]");
        if (!note) {
          note = document.createElement("p");
          note.dataset.ciChartAge = "";
          note.className = "ci-chart-age";
          figure.append(note);
        }
        var data = (manifest.groups || {})[group(file)] || {};
        note.textContent =
          "Chart through " +
          stamp(data.published_through || data.source_through) +
          " · " +
          (data.status || "unknown") +
          " · Today is provisional.";
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
          "Live updates are unavailable. Historical charts remain available below.";
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
