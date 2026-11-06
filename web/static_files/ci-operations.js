/* Prepared operations reader. Viewer traffic only fetches allowlisted public R2 objects. */
(function () {
  "use strict";
  var root = document.querySelector("[data-operations]");
  if (!root) return;
  var origin = "https://ci-data.taucetiproject.org", manifest, etag, disconnected = false, polling = false, delay = 15000;
  var data = {}, cache = new Map(), selectedBatch, detail, memberPages = [], members = [], jobs = [], workflows = [];
  var selectedHistoryHost, hostHistories = new Map(), historyGeneration = 0, historyMetric = "busy_slots";
  var page = 0, jobPage = 0, memberFilter = "all", poolFilter = "all", statusFilter = "all", classFilter = "all", repoFilter = "all", workflowFilter = "all", platformFilter = "all", hostFilter = "all", ageFilter = "all", prResult, searchValue = "", errorText = "", generation = 0, timer;
  var waitingPage = 0, waitingOpen = false, lookupGeneration = 0, prObservedAt;
  var view = root.querySelector("[data-ops-view]"), health = root.querySelector("[data-ops-health]");
  function el(tag, text, cls) { var node = document.createElement(tag); if (text !== undefined) node.textContent = text; if (cls) node.className = cls; return node; }
  function append(parent) { Array.prototype.slice.call(arguments, 1).forEach(function (node) { if (node) parent.append(node); }); return parent; }
  function link(text, url) {
    var node = el("a", text);
    if (/^https:\/\/github\.com\/[-\w.]+\/[-\w.]+\/(pull\/\d+|commit\/[a-f0-9]{40}|actions\/runs\/\d+(\/attempts\/\d+|\/job\/\d+)?)$/.test(url || "")) node.href = url;
    else if (/^#(now|queue|runners|history)(\?|$)/.test(url || "")) node.href = location.pathname + location.search + url;
    return node;
  }
  function timestamp(value) { return Number.isFinite(typeof value === "number" ? value : Date.parse(value)) ? new Date(value).toISOString().slice(0, 19).replace("T", " ") + " UTC" : "unknown"; }
  function age(value) {
    var seconds = (Date.now() - Date.parse(value)) / 1000;
    return !Number.isFinite(seconds) ? "unknown" : seconds < -5 ? "clock ahead by " + Math.ceil(-seconds) + "s" : seconds < 60 ? Math.max(0, Math.floor(seconds)) + "s ago" : seconds < 3600 ? Math.floor(seconds / 60) + "m ago" : Math.floor(seconds / 3600) + "h ago";
  }
  function freshness(value, limit) { var delta = Date.now() - Date.parse(value); return !Number.isFinite(delta) ? "unavailable" : delta < -5000 ? "clock skew" : delta > limit * 1000 ? "delayed" : "observed"; }
  function note(text, cls) { return el("p", text, cls || "ops-note"); }
  function button(text, fn) { var b = el("button", text); b.type = "button"; b.addEventListener("click", fn); return b; }
  function badges(values) { var node = el("div", undefined, "ops-badges"); values.forEach(function (v) { node.append(el("span", v)); }); return node; }
  function heading(text) { return el("h3", text); }
  function empty(text) { return note(text, "ops-empty"); }
  function taskBuild(container, progress) {
    var b = progress && progress.build;
    if (!b) return;
    container.append(note("Reported " + b.stage + " build tasks " + b.completed_tasks + " / " + b.total_tasks + " · sampled " + age(b.sampled_at) + " (" + freshness(b.sampled_at,60) + ") · log output " + age(b.log_updated_at) + " · " + (b.last_progress_at ? "last observed count increase " + age(b.last_progress_at) : "count increase unobserved (first sample or reset)") + ". Log output alone does not establish build progress."));
  }
  function route() {
    var parts = location.hash.slice(1).split("?"), params = new URLSearchParams(parts[1] || location.search);
    var inferred = params.has("pr") || params.has("batch") ? "queue" : params.has("host") || params.has("run") ? "runners" : "now";
    return { tab: ["now", "queue", "runners", "history"].includes(parts[0]) ? parts[0] : inferred, params: params };
  }
  function platform(job) {
    var labels = (job.labels || []).join(" ").toLowerCase();
    var os = /macos|darwin/.test(labels) ? "macOS" : /windows/.test(labels) ? "Windows" : /linux|ubuntu/.test(labels) ? "Linux" : "OS unknown";
    return os + " / " + (/arm64|aarch64/.test(labels) ? "arm64" : /x64|amd64|x86_64/.test(labels) ? "amd64" : "architecture unknown");
  }
  function batchURL(id) { return "#queue?batch=" + encodeURIComponent(id); }
  function sourceNote(kind) {
    var source = (manifest && manifest.domains || {})[kind];
    if (!source || !data[kind]) return empty(kind + " observations unavailable. Last successful reports remain below when available.");
    var observed = freshness(source.observed_at, kind === "queue" ? 60 : 90);
    // Quiet webhooks do not imply a broken observer. Inventory and event times are distinct.
    if (kind === "jobs") return note("GitHub facts · publisher " + freshness(manifest.generated_at, 90) + " · last event " + age(source.observed_at) + ". Inventory confirmation is shown separately.");
    return note(kind + " · " + observed + (source.error ? " · observer projection failed; last successful data" : "") + (source.coverage === "partial" ? " · partial coverage" : "") + " · facts " + age(source.observed_at) + " · received " + age(source.received_at) + (source.truncated ? " · partial details" : ""), "ops-source " + (observed === "observed" ? "" : "ops-warning"));
  }
  async function get(ref) {
    if (!ref || !/^\/v1\/operations\/objects\/[a-f0-9]{64}\/[a-f0-9]{64}\.json$/.test(ref.url)) throw new Error("Invalid public object reference");
    if (cache.has(ref.url)) return cache.get(ref.url);
    var pending = fetch(origin + ref.url, { credentials: "omit", signal: AbortSignal.timeout(10000) }).then(async function (r) {
      if (!r.ok) throw new Error("Public object unavailable");
      var body = await r.text(); if (body.length > 2500000) throw new Error("Public object exceeds limit"); return JSON.parse(body);
    }).catch(function (error) { cache.delete(ref.url); throw error; });
    cache.set(ref.url, pending); if (cache.size > 256) cache.delete(cache.keys().next().value);
    return pending;
  }
  async function records(refs) {
    var result = [];
    for (var i = 0; i < (refs || []).length; i += 4) {
      var parts = await Promise.all(refs.slice(i, i + 4).map(get)); parts.forEach(function (p) { result.push.apply(result, p.records || []); });
    }
    return result;
  }
  function poolSummary(container) {
    container.append(heading("Observed runner pools"));
    if (!data.jobs) { container.append(empty("Job observations unavailable; pool activity is unknown.")); return; }
    var groups = new Map();
    jobs.forEach(function (j) {
      if (!j.active) return;
      var label = j.pool === "github" ? "GitHub · " + platform(j) : j.pool;
      var group = groups.get(label) || {running:0,queued:0,buildRunning:0,buildQueued:0,oldest:null};
      var running = j.status === "in_progress" && j.assigned, build = ["pr_build","staging_build","other_build"].includes(j.job_class);
      if (running) { group.running++; if (build) group.buildRunning++; }
      else { group.queued++; if (build) group.buildQueued++; if (Number.isFinite(Date.parse(j.created_at)) && (!group.oldest || Date.parse(j.created_at)<Date.parse(group.oldest))) group.oldest=j.created_at; }
      groups.set(label,group);
    });
    if (!groups.size) { container.append(empty("No active jobs in the retained observations. Source coverage is shown with the job table.")); return; }
    var scroll=el("div",undefined,"ops-scroll"), table=el("table",undefined,"ops-table ops-pools"), body=el("tbody");
    append(table,append(el("thead"),append(el("tr"),el("th","Pool"),el("th","Running / queued"),el("th","Build-only running / queued"),el("th","Oldest queued job age"))));
    Array.from(groups.entries()).sort(function(a,b){return a[0].localeCompare(b[0]);}).forEach(function(entry){var g=entry[1];body.append(append(el("tr"),el("td",entry[0]),el("td",g.running+" / "+g.queued),el("td",g.buildRunning+" / "+g.buildQueued),el("td",g.oldest?age(g.oldest):"none observed")));});
    table.append(body);scroll.append(table);container.append(scroll);
    container.append(note("Queued jobs are counted once; workflows without observed jobs are separate. Build-only counts sandboxed verification jobs. Counts describe retained observations"+(data.jobs.truncated || data.jobs.coverage === "partial" ? " and may be lower bounds." : ".")));
  }
  function queueSummary(container) {
    var queue = data.queue; container.append(sourceNote("queue"));
    if (!queue) return;
    if (queue.canonical_sha && (queue.scope.repositories || []).length) container.append(link("Canonical tip " + queue.canonical_sha.slice(0,12), "https://github.com/" + queue.scope.repositories[0] + "/commit/" + queue.canonical_sha));
    var head = (queue.batches || []).find(function (b) { return b.state === "head"; });
    if (!head) container.append(empty("No head in the last observed queue snapshot."));
    else {
      append(container, heading("Head " + head.id + " · version " + head.version),
        badges([head.size + " members", "candidate " + head.tip.slice(0, 12), "base " + head.base.slice(0, 12)]),
        link("Open head, CI attempts and repairs", batchURL(head.id)));
      var attempt = head.latest_attempt;
      if (attempt) {
        var job = jobs.find(function (j) { return j.run_id === attempt.run_id && j.run_attempt === attempt.run_attempt && j.job_class === "staging_build"; });
        var host = job && hostFor(job);
        append(container, note("Current CI: " + attempt.status + " · " + (attempt.conclusion || attempt.outcome) + " · attempt " + attempt.id),
          attempt.url ? link("Run " + attempt.run_id + " / attempt " + (attempt.run_attempt || "unknown"), attempt.url) : note("No run has been bound yet."),
          note(job ? "Build provider " + job.pool + (host ? " · host " + host.host.alias + " · VM " + host.slot.instance_id : " · assigned host unknown") + " · " + job.status : "Assigned provider/job details have not been joined for this exact run attempt."));
      }
      (head.active_tasks || []).forEach(function (task) { container.append(note("Open " + task.kind + " task " + task.id + " · " + (task.progress && task.progress.state || "worker phase unknown") + " · phase recorded " + age(task.progress && task.progress.observed_at))); taskBuild(container, task.progress); });
      if (head.first_dispatch_at) container.append(note("Head first dispatched " + age(head.first_dispatch_at) + "."));
      var claims = (queue.claims || []).filter(function (c) { return c.batch_id === head.id; });
      container.append(note(claims.length ? claims.map(function (c) { return c.operation + " by " + c.worker + " · lease expires " + timestamp(c.expires_at); }).join("; ") : "No active operation claim was observed on the head."));
    }
    var counts = queue.counts || {};
    container.append(badges([counts.waiting + " waiting/reserved inputs", (queue.batches || []).filter(function (b) { return b.state === "open"; }).length + " open successors", queue.workers.length + " repair worker observers"]));
    (queue.conditions || []).forEach(function (condition) { container.append(note(condition.kind.replaceAll("_", " ") + (condition.batch_id ? " · batch " + condition.batch_id : "") + (condition.since ? " · since " + timestamp(condition.since) : ""), "ops-warning")); });
    var configuration = el("details"); configuration.append(el("summary", "Controller and effective queue settings"));
    var service = queue.service || {};
    configuration.append(note("Controller " + (service.controller || "unknown") + " · revision " + (service.revision || "unknown") + " · publication " + (service.publication_enabled === true ? "enabled" : service.publication_enabled === false ? "disabled" : "unknown") + " · status observed " + age(queue.status_observed_at)));
    Object.entries(queue.settings || {}).forEach(function (entry) { configuration.append(note(entry[0].replaceAll("_", " ") + ": " + entry[1])); });
    var dispatch = queue.dispatch_config;
    if (dispatch) {
      configuration.append(link("Dispatch policy at " + dispatch.revision.slice(0,12), "https://github.com/" + dispatch.repository + "/commit/" + dispatch.revision));
      configuration.append(note("Configured Namespace build ceiling " + dispatch.namespace_build_cap + " · PR order " + dispatch.pr_order.join(" → ") + " · staging order " + dispatch.staging_order.join(" → ") + ". Runtime overrides are not observed; assignments are shown with each job."));
    } else configuration.append(note("Dispatch policy and cloud build ceilings are not observed in this snapshot."));
    container.append(configuration);
    queue.workers.forEach(function (w) { container.append(note(w.id + " · " + (w.state || "unknown state") + " · heartbeat " + age(w.observed_at) + " · " + freshness(w.observed_at, 60))); });
  }
  function select(label, options, value, change) {
    var wrap = el("label", label + " "), control = el("select"); control.setAttribute("aria-label", label);
    options.forEach(function (o) { var option = el("option", o.label || o); option.value = o.value || o; control.append(option); }); control.value = value;
    control.addEventListener("change", function () { change(control.value); }); wrap.append(control); return wrap;
  }
  function pager(container, current, count, change) {
    var nav = el("div", undefined, "ops-pager");
    var prev = button("Previous", function () { change(current - 1); }); prev.disabled = current === 0;
    var next = button("Next", function () { change(current + 1); }); next.disabled = (current + 1) * 100 >= count;
    append(nav, prev, el("span", count ? (current * 100 + 1) + "–" + Math.min((current + 1) * 100, count) + " of " + count : "0 records"), next); container.append(nav);
  }
  async function lookup(pr) {
    var queue = data.queue; if (!queue || !/^\d+$/.test(pr)) return;
    var token = ++lookupGeneration;
    if (searchValue !== pr) prResult = null;
    searchValue = pr; errorText = "";
    try {
      var shard = await get(queue.pr_shards[Number(BigInt(pr) % 64n)]);
      if (token !== lookupGeneration || queue !== data.queue || route().params.get("pr") !== pr) return;
      prResult = (queue.scope.repositories || []).flatMap(function (repo) { return shard.prs[repo + "#" + pr] ? [shard.prs[repo + "#" + pr]] : []; });
      prObservedAt = queue.observed_at;
      render();
    } catch (_) { if (token === lookupGeneration && queue === data.queue && route().params.get("pr") === pr) { errorText = "PR lookup unavailable; last successful records are retained."; render(); } }
  }
  async function loadBatch(id) {
    var queue = data.queue; if (!queue || !manifest) return;
    var scope = manifest.scope, ref = queue.batch_shards[Number(BigInt(id) % 64n)];
    var token = ++generation, same = selectedBatch === id; selectedBatch = id;
    function current() { return token === generation && selectedBatch === id && manifest.scope === scope && ref && data.queue && (data.queue.batch_shards[Number(BigInt(id) % 64n)] || {}).url === ref.url; }
    if (!same) { detail = null; members = []; memberPages = []; page = 0; render(); }
    try {
      var shard = await get(ref); if (!current()) return;
      var batch = shard.batches.find(function (b) { return b.id === id; });
      if (!batch) { errorText = "Batch is outside the retained detail window."; render(); return; }
      var value = await get(batch.detail); if (!current()) return;
      var loaded = await records(value.member_pages);
      var attempts = await records(value.attempt_pages), tasks = await records(value.task_pages), events = await records(value.event_pages);
      if (!current()) return;
      detail = value; members = loaded; memberPages = value.member_pages; detail.attempts = attempts; detail.tasks = tasks; detail.events = events; if (!same) page = 0; errorText = ""; render();
    } catch (_) { if (current()) { errorText = "Batch details unavailable; last successful detail for this batch is retained."; render(); } }
  }
  function timeline(container, attempts, tasks) {
    var items = attempts.map(function (a) { return { label: "CI attempt " + a.id + " · v" + a.version + " · " + a.status + " / " + (a.conclusion || a.outcome), start: a.dispatched_at, end: a.completed_at || a.cancelled_at, url: a.url, detail: a }; }).concat(tasks.map(function (t) { return { label: t.kind + " task " + t.id + " · " + t.state, start: t.created_at, end: t.resolved_at, progress: t.progress }; }));
    if (!items.length) return container.append(empty("No recorded CI or repair tasks in this detail window."));
    var starts = items.map(function (i) { return Date.parse(i.start); }).filter(Number.isFinite), left = Math.min.apply(null, starts), right = Math.max(Date.now(), left + 1000);
    container.append(note("Intervals share the same time axis; overlapping repair and CI remain separate. Open intervals end at the current clock. Their sum is not head latency."));
    items.sort(function (a, b) { return Date.parse(a.start) - Date.parse(b.start); }).forEach(function (i) {
      var row = el("article", undefined, "ops-interval"); append(row, i.url ? link(i.label, i.url) : el("strong", i.label));
      var track = el("div", undefined, "ops-track"), bar = el("span");
      var start = Date.parse(i.start), end = Date.parse(i.end) || Date.now();
      if (Number.isFinite(start) && end >= start) { bar.style.marginLeft = Math.max(0, (start - left) / (right - left) * 100) + "%"; bar.style.width = Math.max(0.5, Math.min(100, (end - start) / (right - left) * 100)) + "%"; } track.append(bar);
      append(row, track, note(timestamp(i.start) + " → " + (i.end ? timestamp(i.end) : "ongoing / completion unobserved")));
      if (i.progress && i.progress.coverage === "observed") {
        var p = i.progress;
        row.append(note("Worker phase " + p.state + " · observed " + age(p.observed_at) + " · " + p.providers.join(", ") + " / " + p.models.join(", ") + " · recorded cost subtotal $" + p.cost.recorded_usd.toFixed(2) + " (" + p.cost.recorded_attempts + " known attempts; " + p.cost.unknown_attempts + " missing estimates)"));
        taskBuild(row, p);
        var tokenLabels = {input_tokens:"input", cached_input_tokens:"cached input", output_tokens:"output", reasoning_output_tokens:"reasoning output", total_tokens:"total"};
        row.append(note("Recorded tokens · " + (p.usage ? Object.keys(tokenLabels).map(function (key) { var u=p.usage[key]; return tokenLabels[key] + ": " + (u && u.recorded_attempts ? u.recorded_tokens + " recorded (" + u.recorded_attempts + " known attempts; " + u.unknown_attempts + " missing)" : "unknown"); }).join(" · ") : "unavailable") + ". Live or unretained attempts may be absent."));
      }
      if (i.detail) {
        var a = i.detail;
        row.append(note("Candidate " + a.candidate.slice(0, 12) + " · run " + (a.run_id || "not bound") + " / attempt " + (a.run_attempt || "unknown") + " · runner " + (a.runner || "unknown")));
        row.append(badges(Object.entries(a.verdicts || {}).map(function (p) { return p[0] + ": " + p[1].state + (p[1].bound ? " (bound)" : " (unbound)"); })));
      } container.append(row);
    });
  }
  function queueView() {
    queueSummary(view); if (!data.queue) return;
    var form = el("form", undefined, "ops-search"), input = el("input"); input.type = "search"; input.inputMode = "numeric"; input.placeholder = "PR number"; input.value = searchValue; input.setAttribute("aria-label", "Find a pull request in the queue");
    append(form, input, button("Find PR", function () { location.hash = "queue?pr=" + encodeURIComponent(input.value.replace(/^#/, "")); }));
    form.addEventListener("submit", function (e) { e.preventDefault(); location.hash = "queue?pr=" + encodeURIComponent(input.value.replace(/^#/, "")); }); view.append(form);
    if (prResult) {
      if (!prResult.length) view.append(empty("No retained queue record for PR #" + searchValue + "."));
      prResult.forEach(function (pr) {
        append(view, heading("PR #" + pr.pr), link("GitHub pull request", "https://github.com/" + pr.repository + "/pull/" + pr.pr));
        view.append(note("PR record observed " + age(prObservedAt) + " · " + freshness(prObservedAt,60)));
        pr.inputs.forEach(function (i) {
          append(view, note(i.title + " · " + i.state), link("Accepted revision " + i.accepted_head.slice(0, 12), "https://github.com/" + pr.repository + "/commit/" + i.accepted_head), note("Approved " + timestamp(i.approved_at) + " · " + age(i.approved_at)));
          if (i.no_repair) view.append(note("Agents may not edit this contribution. Source fixes must come from the pull request."));
          if (i.batch_id) view.append(link("Recorded batch " + i.batch_id, batchURL(i.batch_id)));
          if (["waiting", "reserved"].includes(i.state)) view.append(note(i.state === "waiting" ? "Next event: queue admission into a batch." : "Next event: insertion into the reserved batch."));
          if (i.landed_at) view.append(note("Landed " + timestamp(i.landed_at)));
          if (i.landed_commit) view.append(link("Landed commit " + i.landed_commit.slice(0, 12), "https://github.com/" + pr.repository + "/commit/" + i.landed_commit));
        });
        pr.members.forEach(function (m) {
          append(view, link("Batch " + m.batch_id + " · version " + m.batch_version + " · " + m.disposition, batchURL(m.batch_id)), note("Inserted " + timestamp(m.inserted_at) + (m.landed_at ? " · landed " + timestamp(m.landed_at) : m.removed ? " · removed membership" : m.withdrawn ? " · withdrawn membership" : "")));
          if (m.commit_url) view.append(link("Constituent " + (m.commit || "unknown").slice(0,12), m.commit_url));
          view.append(note(m.explanation || "No programmatic explanation recorded."));
        });
      });
    }
    var waiting = el("details", undefined, "ops-waiting"); waiting.open = waitingOpen;
    waiting.addEventListener("toggle", function () { if (waiting.isConnected) waitingOpen = waiting.open; });
    waiting.append(el("summary", "Approved waiting inputs · " + data.queue.counts.waiting));
    if (data.queue.waiting_error) waiting.append(note("Waiting details could not refresh. Retained records were observed " + age(data.queue.waiting_observed_at) + ".", "ops-warning"));
    if (!data.queue.loaded_waiting) waiting.append(note("Waiting details are unavailable or loading; PR search remains available."));
    else {
      var inputs = data.queue.loaded_waiting, list = el("ul", undefined, "ops-inputs");
      if (!inputs.length) waiting.append(note("No waiting inputs in this observation; source coverage is shown above."));
      waitingPage = Math.min(waitingPage, Math.max(0, Math.ceil(inputs.length / 100) - 1));
      inputs.slice(waitingPage * 100, (waitingPage + 1) * 100).forEach(function (i) {
        var row = el("li"); append(row, link("PR #" + i.pr, "#queue?pr=" + i.pr), note(i.title + " · " + i.state + " · approved " + timestamp(i.approved_at) + " · " + age(i.approved_at)), link("Accepted " + i.accepted_head.slice(0,12), "https://github.com/" + i.repository + "/commit/" + i.accepted_head));
        if (i.no_repair) row.append(note("Agents may not edit this contribution."));
        list.append(row);
      }); waiting.append(list); pager(waiting, waitingPage, inputs.length, function (p) { waitingPage = p; render(); });
    }
    view.append(waiting);
    var choices = data.queue.batches.map(function (b) { return { value: b.id, label: "Batch " + b.id + " · " + b.state + " · v" + b.version + " · " + b.size + " members" }; });
    view.append(select("Batch", choices, selectedBatch || (choices[0] || {}).value, function (id) { location.hash = batchURL(id); }));
    if (!detail) { view.append(empty("Select a batch to load bounded detail pages.")); return; }
    append(view, heading("Batch " + detail.batch.id + " · " + detail.batch.state), link("Exact candidate " + detail.batch.tip.slice(0, 12), "https://github.com/" + detail.batch.repository + "/commit/" + detail.batch.tip));
    var latest = data.queue.batches.find(function (b) { return b.id === detail.batch.id; });
    if (latest && (latest.version !== detail.batch.version || latest.tip !== detail.batch.tip)) view.append(note("Showing last successful details for version " + detail.batch.version + "; current version " + latest.version + " is loading.", "ops-warning"));
    view.append(note("Created " + timestamp(detail.batch.created_at) + " · sealed " + timestamp(detail.batch.sealed_at) + " · first dispatched " + timestamp(detail.batch.first_dispatch_at)));
    view.append(note("Background preparation: " + (detail.batch.pre_rebase_state || "unknown") + ". Authoritative staging CI is dispatched only for the head."));
    if (!detail.member_details_complete) view.append(note("Member details are partial; the authoritative batch size is " + detail.batch.size + ".", "ops-warning"));
    view.append(select("Members", ["all", "agent_edited", "clean_replay", "reduced_empty", "already_landed_empty", "empty_unknown", "removed"], memberFilter, function (v) { memberFilter = v; page = 0; render(); }));
    var filtered = members.filter(function (m) { return memberFilter === "all" || (memberFilter === "removed" ? m.removed : m.disposition === memberFilter); });
    var table = el("table", undefined, "ops-table"); append(table, append(el("thead"), append(el("tr"), el("th", "PR"), el("th", "Constituent"), el("th", "Provenance and explanation"))));
    var body = el("tbody"); filtered.slice(page * 100, (page + 1) * 100).forEach(function (m) {
      var row = el("tr"), pr = el("td"), commit = el("td"), why = el("td");
      append(pr, link("#" + m.pr, m.pr_url), note(m.title)); append(commit, link((m.commit || "unknown").slice(0, 12), m.commit_url), note("accepted " + m.accepted_head.slice(0, 12) + " · batch v" + m.batch_version));
      append(why, el("strong", m.disposition.replaceAll("_", " ") + (m.removed ? " · removed" : "")), note(m.explanation || "No explanation recorded.")); append(row, pr, commit, why); body.append(row);
    }); table.append(body); view.append(table); pager(view, page, filtered.length, function (n) { page = n; render(); });
    view.append(heading("CI and repair timeline")); timeline(view, detail.attempts, detail.tasks);
    view.append(heading("Recorded events")); detail.events.slice(-50).forEach(function (e) { view.append(note(timestamp(e.at) + " · " + e.kind)); });
  }
  function hostFor(job) {
    if (job.host_binding) return { host: { alias: job.host_binding.alias }, slot: ((data.hosts && data.hosts.hosts || []).flatMap(function (h) { return h.slots || []; }).find(function (s) { return s.instance_id === job.host_binding.instance_id && s.runner_id === job.runner_id; }) || { slot: job.host_binding.slot, instance_id: job.host_binding.instance_id }), evidence: job.host_binding.evidence };
    var hosts = data.hosts && data.hosts.hosts || [];
    for (var host of hosts) for (var slot of host.slots || []) if (job.runner_id && slot.runner_id === job.runner_id && ((job.labels || []).includes("fleet-" + host.machine_id) || job.runner_name === "fleet-" + host.machine_id.slice(0, 12) + "-" + slot.instance_id)) return { host: host, slot: slot, evidence: "runner ID" };
    return null;
  }
  function runnerView() {
    view.append(sourceNote("hosts"));
    poolSummary(view);
    var contexts = (data.hosts && data.hosts.hosts || []).filter(function (h) { return h.capacity_context && h.capacity_context.coverage === "observed" && h.capacity_context.observed_at; }).sort(function (a,b) { return Date.parse(b.capacity_context.observed_at)-Date.parse(a.capacity_context.observed_at); });
    view.append(heading("Shared capacity cache"));
    if (contexts.length) {
      var context = contexts[0].capacity_context, counts = context.running_jobs;
      view.append(note("All organisation workflow jobs · observed " + age(context.observed_at) + " · " + freshness(context.observed_at,300) + (context.observer_error ? " · cache observer error; last known counts" : "")));
      view.append(note("Running · GitHub " + (counts.github ?? "unknown") + " · Namespace " + (counts.namespace ?? "unknown") + " · self-hosted " + (counts["self-hosted"] ?? "unknown") + ". These cache totals have a different scope from the installation-visible job table and do not establish free slots."));
    } else view.append(note("Shared capacity cache unavailable. No observation establishes spare cloud capacity."));
    if (data.hosts) (data.hosts.pools || []).filter(function (p) { return !p.machine_id; }).forEach(function (p) {
      append(view, heading(p.label), note(p.id === "namespace" ? "Installation-visible jobs only. Requested profiles do not establish account-wide workloads, billed usage or physical utilization." : "Physical resource metrics unavailable. Job lifecycle is observed through GitHub."));
    });
    if (data.hosts) (data.hosts.hosts || []).filter(function (h) { return !route().params.get("host") || route().params.get("host") === h.machine_id || route().params.get("host") === h.alias; }).forEach(function (h) {
      var card = el("article", undefined, "ops-host"); card.id = "host-" + h.machine_id;
      append(card, heading(h.alias), note("Permanent host " + h.machine_id + " · controller " + (h.source_revision || "unknown")), badges([freshness(h.observed_at, 60), "facts " + age(h.observed_at), "stream " + (h.connected ? age(h.transport_at) : "disconnected") ]));
      if (h.slots_truncated || h.workers_truncated) card.append(note("Host slot/worker details are truncated.", "ops-warning"));
      var r = h.resources || {}, compiler = h.compiler || {}, admission = h.admission || {}, activity = h.activity || {};
      append(card, note("CI " + (h.ci_enabled === null || h.ci_enabled === undefined ? "unknown" : h.ci_enabled ? "enabled" : "disabled") + " · workers " + (h.workers_enabled === null || h.workers_enabled === undefined ? "unknown" : h.workers_enabled ? "enabled" : "disabled")),
        note("CPU idle " + (r.cpus && h.cpu_idle_fraction !== null ? Math.round(h.cpu_idle_fraction * 100) + "% of " + r.cpus + " CPUs" : "unknown") + " · RAM available " + (r.memory_available === null || r.memory_available === undefined ? "unknown" : (r.memory_available / 1073741824).toFixed(1) + " GiB") + (h.memory_pressure ? " · memory pressure" : "")),
        note("Compiler admission · " + (compiler.waiting_guests === null || compiler.waiting_guests === undefined ? "unknown" : compiler.waiting_guests + " guests waiting") + " · pressure observer " + freshness(compiler.observed_at, 10)));
      card.append(note("CI ceiling " + (h.ci_max_jobs ?? "unknown") + " jobs · classes " + (admission.ci_kinds ? admission.ci_kinds.join(", ") : "unknown") + " · staging reservation " + (admission.staging_slots ?? "unknown") + " · CI RAM budget " + (admission.memory_budget_gib ?? "unknown") + " GiB · worker limit " + (h.worker_limit ?? "unknown")));
      if (admission.reservation_error) card.append(note("Staging reservation configuration needs attention.", "ops-warning"));
      card.append(note("Worker rounds in 24h · finished " + (activity.finished_rounds ?? "unknown") + " · failed " + (activity.failed_rounds ?? "unknown") + " · outcomes unconfirmed " + (activity.unknown_rounds ?? "unknown") + " · activity prepared " + age(activity.observed_at)));
      if (h.worker_memory) {
        var memory = h.worker_memory;
        function gib(value) { return value === null || value === undefined ? "unknown" : (value / 1073741824).toFixed(1) + " GiB"; }
        card.append(note("Worker RAM · working set " + gib(memory.working_set) + " · charged " + gib(memory.charged) + " · limit " + gib(memory.maximum) + " · OOM-kill counter " + (memory.oom_kill ?? "unknown") + ". This counter does not identify individual failed jobs."));
      }
      if (h.worker_admission) card.append(note("Worker admission · " + (h.worker_admission.state || "unknown").replaceAll("_", " ") + " · " + (h.worker_admission.reason || "unknown").replaceAll("_", " ")));
      if (h.ci_cooldown) card.append(note("CI launch cooldown until " + timestamp(h.ci_cooldown.until) + ". Existing work can continue."));
      (h.slots || []).forEach(function (s) { card.append(note("Slot " + s.slot + " · " + s.phase + " · " + (s.busy ? "busy" : "not marked busy") + " · runner " + (s.runner_id || "unknown") + " · VM " + (s.instance_id || "unknown") + " · configured guest " + (s.vcpus ?? "unknown") + " CPUs / " + (s.memory_gib ?? "unknown") + " GiB")); });
      (h.workers || []).forEach(function (w) { card.append(note("Worker " + w.id + " · " + w.state + " · " + (w.alive ? "reported alive" : "not marked alive") + " · heartbeat " + age(w.observed_at) + " · " + freshness(w.observed_at, 60))); });
      if (!(h.slots || []).length) card.append(note("No slots in this observation. This does not establish available capacity.")); view.append(card);
    });
    jobsView(view);
  }
  function jobsView(container) {
    container.append(sourceNote("jobs")); if (!data.jobs) return;
    if (data.jobs.coverage === "unavailable") { container.append(empty("Job counts unavailable; no observed facts establish zero activity.")); return; }
    var counts = data.jobs.counts;
    if (data.jobs.truncated || data.jobs.coverage === "partial" || (data.jobs.partition_errors || []).length) container.append(note("Job inventory is partial; counts describe retained observations and may be lower bounds.", "ops-warning"));
    append(container, heading("CI jobs"), badges([counts.running + " running", counts.queued_jobs + " queued jobs", counts.pending_workflows + " workflows awaiting observed jobs"]));
    var filters = el("div", undefined, "ops-filters"), pools = ["all"].concat(Array.from(new Set(jobs.map(function (j) { return j.pool; }))));
    append(filters, select("Pool", pools, poolFilter, function (v) { poolFilter = v; jobPage = 0; render(); }), select("State", ["all", "active", "completed", "queued", "in_progress"], statusFilter, function (v) { statusFilter = v; jobPage = 0; render(); }), select("Class", ["all", "pr_build", "staging_build", "other_build", "control", "maintenance", "other"], classFilter, function (v) { classFilter = v; jobPage = 0; render(); })); container.append(filters);
    function options(key) { return ["all"].concat(Array.from(new Set(jobs.map(function (j) { return key(j) || "unknown"; }))).sort()); }
    append(filters,
      select("Repository", options(function (j) { return j.repository; }), repoFilter, function (v) { repoFilter = v; jobPage = 0; render(); }),
      select("Workflow", options(function (j) { return j.workflow; }), workflowFilter, function (v) { workflowFilter = v; jobPage = 0; render(); }),
      select("Requested OS / architecture", options(platform), platformFilter, function (v) { platformFilter = v; jobPage = 0; render(); }),
      select("Assigned host", options(function (j) { var h = hostFor(j); return h ? h.host.alias : "unresolved"; }), hostFilter, function (v) { hostFilter = v; jobPage = 0; render(); }),
      select("Job age", [{value:"all",label:"all"},{value:"1800",label:"at least 30 min"},{value:"3600",label:"at least 1 hour"}], ageFilter, function (v) { ageFilter = v; jobPage = 0; render(); }));
    var deep = route().params;
    var filtered = jobs.filter(function (j) { var host = hostFor(j); return (!deep.get("repo") || deep.get("repo") === j.repository) && (repoFilter === "all" || j.repository === repoFilter) && (workflowFilter === "all" || (j.workflow || "unknown") === workflowFilter) && (platformFilter === "all" || platform(j) === platformFilter) && (hostFilter === "all" || (host ? host.host.alias : "unresolved") === hostFilter) && (ageFilter === "all" || (Date.now() - Date.parse(j.created_at)) / 1000 >= Number(ageFilter)) && (!deep.get("run") || deep.get("run") === j.run_id) && (!deep.get("attempt") || deep.get("attempt") === String(j.run_attempt)) && (!deep.get("job") || deep.get("job") === j.id) && (poolFilter === "all" || j.pool === poolFilter) && (statusFilter === "all" || (statusFilter === "active" ? j.active : j.status === statusFilter)) && (classFilter === "all" || j.job_class === classFilter); });
    filtered.slice(jobPage * 100, (jobPage + 1) * 100).forEach(function (j) {
      var row = el("article", undefined, "ops-job"), host = hostFor(j), current = (j.steps || []).find(function (s) { return s.started_at && !s.completed_at; }), progress = j.progress || {};
      append(row, link(j.repository + " · " + j.name + " · run " + j.run_id + " / " + j.run_attempt + " / job " + j.id, j.url), badges([j.pool, platform(j), j.status + (j.conclusion ? " / " + j.conclusion : ""), j.job_class]),
        note(host ? "Host " + host.host.alias + " · slot " + host.slot.slot + " · VM " + host.slot.instance_id + " (joined by " + host.evidence + ")" : "Runner " + (j.runner_name || "unassigned") + " · host association unknown"),
        note("Phase: " + (progress.phase || (current && current.name) || (j.status === "queued" ? "waiting for runner / job start" : "unknown")) + " · progress " + (progress.coverage || "unsupported") + (progress.last_progress_at ? " · last change " + age(progress.last_progress_at) : "")));
      if (host && host.slot.compiler) {
        var c = host.slot.compiler;
        row.append(note("This VM's compiler observer " + freshness(c.observed_at, 15) + " · " + (c.waiting_now === null ? "unknown" : c.waiting_now) + " waiting · " + (c.running_now === null ? "unknown" : c.running_now) + " running · oldest admission wait " + (c.oldest_wait === null ? "unknown" : Math.round(c.oldest_wait) + "s")));
      }
      if (progress.completed_modules !== null && progress.completed_modules !== undefined) row.append(note(progress.completed_modules + " completed modules · " + (progress.active_compilers === null ? "unknown" : progress.active_compilers) + " active compilers · CPU " + (progress.cpu_seconds === null ? "unknown" : progress.cpu_seconds + "s") + " · reporter " + freshness(progress.heartbeat_at, 45)));
      if (j.queue_binding) append(row, link("Queue batch " + j.queue_binding.batch_id + " · version " + j.queue_binding.version, batchURL(j.queue_binding.batch_id)), note("Queue-bound candidate " + j.queue_binding.candidate.slice(0, 12) + " · exact run and attempt"));
      if (j.reported_candidate) row.append(note("Run-reported candidate " + j.reported_candidate.slice(0, 12) + " · " + j.candidate_binding + ". Queue verdicts remain authoritative.")); container.append(row);
    });
    pager(container, jobPage, filtered.length, function (n) { jobPage = n; render(); });
    (data.jobs.observer.inventory || []).forEach(function (i) { container.append(note(i.repository + " · inventory confirmed through " + (i.confirmed_through ? timestamp(i.confirmed_through * 1000) : "unknown"))); });
    if (workflows.length) { container.append(heading("Workflows without observed active jobs")); workflows.slice(0, 20).forEach(function (w) { container.append(link(w.repository + " · run " + w.run_id + " / " + w.run_attempt + " · " + w.status, w.url)); }); }
  }
  async function loadHostHistory(id) {
    if (!data.host_history) return;
    var source = data.host_history.hosts.find(function (h) { return h.machine_id === id; });
    if (!source) return;
    var scope = manifest.scope, key = scope + "/" + id, token = ++historyGeneration, observed = data.host_history.observed_at;
    selectedHistoryHost = id;
    render();
    try {
      var values = await records(source.pages);
      if (manifest.scope !== scope || selectedHistoryHost !== id || token !== historyGeneration) return;
      hostHistories.set(key, { records: values, observed_at: observed, loaded: true, error: false });
      if (hostHistories.size > 16) hostHistories.delete(hostHistories.keys().next().value);
      render();
    } catch (_) {
      if (manifest.scope !== scope || selectedHistoryHost !== id || token !== historyGeneration) return;
      hostHistories.set(key, Object.assign({ records: [], loaded: false }, hostHistories.get(key), { error: true }));
      render();
    }
  }
  function hostHistoryView() {
    view.append(heading("Dedicated host history"));
    if (!data.host_history || !data.host_history.hosts.length) return view.append(empty("Host history is unavailable. Earlier periods remain unknown."));
    var hosts = data.host_history.hosts;
    view.append(select("Host", hosts.map(function (h) { return { value: h.machine_id, label: h.alias }; }), selectedHistoryHost || hosts[0].machine_id, loadHostHistory));
    view.append(select("Metric", [{ value: "busy_slots", label: "Busy CI slots" }, { value: "workers_alive", label: "Live workers" }, { value: "compiler_waiting_guests", label: "Guests waiting for compiler admission" }, { value: "cpu_idle_fraction", label: "CPU idle fraction" }, { value: "memory_available", label: "Available RAM (GiB)" }], historyMetric, function (v) { historyMetric = v; render(); }));
    var saved = hostHistories.get(manifest.scope + "/" + (selectedHistoryHost || hosts[0].machine_id));
    if (saved && saved.error) view.append(note("Host history unavailable; only this host's last successful samples are retained.", "ops-warning"));
    if (!saved || !saved.loaded) return view.append(empty("Host history is unavailable or loading for this host."));
    var days = route().params.get("window") === "7d" || route().params.get("window") === "pilot" ? 7 : 1;
    var values = saved.records.filter(function (r) { return Date.parse(r.at) >= Date.now() - days * 86400000; });
    view.append(note("Five-minute sample means for the last " + days + " day(s) · history prepared " + age(saved.observed_at) + ". Coverage starts at observer activation; gaps remain unknown."));
    var usable = values.filter(function (r) { return r.metrics && r.metrics[historyMetric] && r.metrics[historyMetric].count; });
    if (!usable.length) return view.append(empty("No observed samples for this host and metric in the selected window."));
    var scale = historyMetric === "memory_available" ? 1073741824 : 1;
    var max = Math.max.apply(null, usable.map(function (r) { return r.metrics[historyMetric].sum / r.metrics[historyMetric].count / scale; }).concat([1]));
    var ns = "http://www.w3.org/2000/svg", svg = document.createElementNS(ns, "svg"), width = 720, height = 180;
    svg.setAttribute("viewBox", "0 0 " + width + " " + (height + 30)); svg.setAttribute("role", "img"); svg.setAttribute("aria-label", "Observed five-minute means of " + historyMetric.replaceAll("_", " ") + "; data gaps are omitted.");
    svg.classList.add("ops-history-chart");
    var from = Date.now() - days * 86400000, commands = [], previous = null;
    values.forEach(function (r) {
      var metric = r.metrics && r.metrics[historyMetric], time = Date.parse(r.at);
      if (!metric || !metric.count) { previous = null; return; }
      var x = (time - from) / (days * 86400000) * width, y = height - metric.sum / metric.count / scale / max * (height - 10);
      commands.push((previous !== null && time - previous <= 300000 ? "L" : "M") + x.toFixed(1) + "," + y.toFixed(1)); previous = time;
    });
    var path = document.createElementNS(ns, "path"); path.setAttribute("d", commands.join(" ")); path.setAttribute("fill", "none"); path.setAttribute("stroke", "currentColor"); path.setAttribute("stroke-width", "2"); svg.append(path); view.append(svg);
    view.append(note("Vertical scale: 0–" + max.toFixed(2) + ". " + usable.length + " observed five-minute bins. The latest bin is provisional."));
    var table = el("table", undefined, "ops-table"); append(table, append(el("thead"), append(el("tr"), el("th", "UTC bin"), el("th", "Observed mean"), el("th", "Fresh / received samples"))));
    var body = el("tbody"); values.slice(-12).forEach(function (r) {
      var metric = r.metrics && r.metrics[historyMetric];
      body.append(append(el("tr"), el("td", timestamp(r.at)), el("td", metric && metric.count ? (metric.sum / metric.count / scale).toFixed(2) : "unknown"), el("td", r.fresh_samples + " / " + r.samples)));
    }); table.append(body); view.append(table);
  }
  function historyView() {
    view.append(heading("Queue and throughput history"));
    if (!data.history) view.append(empty("Prepared queue measurement report unavailable. Historical CI charts remain available below. Missing cost and historical host telemetry are not zero."));
    else {
      view.append(note("Report " + age(data.history.observed_at) + ". Unique PRs, nonempty constituents and interval unions use their separately stated coverage."));
      view.append(select("Window", data.history.windows.map(function (w) { return { value: w.key, label: w.label }; }), route().params.get("window") || "24h", function (v) { location.hash = "history?window=" + v; }));
      var window = data.history.windows.find(function (w) { return w.key === (route().params.get("window") || "24h"); }) || data.history.windows[0];
      if (window) {
        var summary = window.summary, baseline = data.history.baseline, cost = summary.cost;
        append(view, heading(window.label), note(timestamp(window.from) + " → " + timestamp(window.until) + " · " + window.hours.toFixed(1) + " wall-clock hours"),
          badges([summary.landed_prs + " unique PR landings", (summary.landed_prs_per_hour || 0).toFixed(1) + " PR/h", summary.nonempty_unique_prs === null ? "Nonempty contribution coverage incomplete" : summary.nonempty_unique_prs + " unique nonempty contributions", summary.empty_member_occurrences + " empty member occurrences"]),
          note("Bors baseline: " + (baseline.landed_prs_per_hour === null ? "unknown" : baseline.landed_prs_per_hour.toFixed(1) + " PR/h") + ". Nonempty contribution and cost comparisons are unavailable for that baseline."),
          note("Recorded agent cost subtotal: $" + cost.recorded_usd.toFixed(2) + " · " + cost.recorded_attempts + " known attempts · " + cost.unknown_attempts + " attempts with missing estimates. Interrupted sessions may be absent."));
        if (window.criteria) {
          var scenario = window.criteria.scenario, week = window.criteria.week;
          view.append(heading("Pilot exit criteria"));
          view.append(note("110 PRs, two source failures, under 120 minutes · " + scenario.status.replaceAll("_", " ") + " · " + scenario.qualifying_count + " qualifying / " + scenario.eligible_count + " eligible heads. Warm artifacts and zero singleton recovery still require verification."));
          scenario.qualifying_batches.forEach(function (id) { view.append(link("Qualifying batch " + id, batchURL(id))); });
          view.append(note("Week above Bors baseline · " + week.status.replaceAll("_", " ") + " · " + week.observed_days.toFixed(2) + " observed days · rate " + (week.rate_above_baseline ? "above" : "not above") + " baseline. Attribution and comment correctness need a separate audit."));
        }
        var dist = summary.head_dispatch_minutes;
        view.append(note("Head first-dispatch → landing: " + (dist.count ? "median " + dist.median.toFixed(1) + " min · p95 " + dist.p95.toFixed(1) + " min · " + dist.count + " heads" : "no observed landings")));
        var table = el("table", undefined, "ops-table"); append(table, append(el("thead"), append(el("tr"), el("th", "Head"), el("th", "Latency"), el("th", "CI / repair / overlap"))));
        var body = el("tbody"); window.heads.slice(-100).forEach(function (h) {
          var row = el("tr"), head = el("td"), timing = el("td"), intervals = el("td");
          head.append(link("Batch " + h.batch_id + " · " + h.size + " members", batchURL(h.batch_id)));
          timing.textContent = h.first_dispatch_to_landing_minutes === null ? "unknown" : h.first_dispatch_to_landing_minutes.toFixed(1) + " min";
          intervals.textContent = [h.ci_observed_minutes, h.claimed_task_minutes, h.ci_task_overlap_minutes].map(function (v) { return v === null ? "unknown" : v.toFixed(1) + "m"; }).join(" / "); append(row, head, timing, intervals); body.append(row);
        }); table.append(body); view.append(table);
        view.append(note("CI and repair can overlap; subtract their overlap before comparing against wall time. Only the latest 100 retained heads are shown here."));
      }
      (data.history.limits || []).forEach(function (limit) { view.append(note(limit)); });
    }
    hostHistoryView();
    append(view, link("View historical CI charts", "#history"), note("The historical fleet, duration, wait, failure, phase and staging charts below retain independent source coverage."));
  }
  function render() {
    var active = route().tab;
    var editing = document.activeElement && root.contains(document.activeElement) && document.activeElement.tagName === "INPUT";
    var editingState = editing ? { value: document.activeElement.value, start: document.activeElement.selectionStart, end: document.activeElement.selectionEnd } : null;
    view.replaceChildren();
    root.querySelectorAll("[data-ops-tab]").forEach(function (tab) { if (tab.dataset.opsTab === active) tab.setAttribute("aria-current", "page"); else tab.removeAttribute("aria-current"); });
    var state = manifest ? freshness(manifest.generated_at, 90) : "unavailable";
    health.textContent = "Operations publisher " + state + (manifest ? " · published " + age(manifest.generated_at) : "") + (disconnected ? " · fetch failed; last successful observations retained" : "") + ".";
    health.className = "ops-status" + (disconnected || state !== "observed" ? " ops-warning" : "");
    if (errorText) view.append(note(errorText, "ops-warning"));
    if (active === "now") { queueSummary(view); poolSummary(view); jobsView(view); }
    else if (active === "queue") queueView(); else if (active === "runners") runnerView(); else historyView();
    if (editingState) {
      var restored = root.querySelector('input[type="search"]');
      if (restored) { restored.value = editingState.value; restored.focus({ preventScroll: true }); restored.setSelectionRange(editingState.start, editingState.end); }
    }
  }
  async function navigate() {
    render(); var params = route().params, batch = params.get("batch"), pr = params.get("pr");
    if (route().tab === "history" && data.host_history && data.host_history.hosts.length) await loadHostHistory(selectedHistoryHost || data.host_history.hosts[0].machine_id);
    if (pr && data.queue) await lookup(pr);
    if (route().tab === "queue" && data.queue) {
      batch = batch || (data.queue.batches.find(function (b) { return b.state === "head"; }) || data.queue.batches[0] || {}).id;
      if (batch && /^\d+$/.test(batch)) await loadBatch(batch);
    }
  }
  async function poll() {
    if (document.hidden || polling) return;
    polling = true;
    var started = Date.now();
    try {
      var response = await fetch(origin + "/v1/operations/manifest.json", { credentials: "omit", cache: "no-store", headers: etag ? { "If-None-Match": etag } : {}, signal: AbortSignal.timeout(10000) });
      if (response.status !== 304) {
        if (!response.ok) throw new Error("Operations manifest unavailable");
        var next = await response.json(); if (next.schema !== "tauceti.operations.manifest/v1") throw new Error("Unsupported manifest");
        if (manifest && manifest.scope !== next.scope) { data = {}; cache.clear(); jobs = []; workflows = []; detail = null; members = []; prResult = null; selectedBatch = null; generation++; hostHistories.clear(); selectedHistoryHost = null; historyGeneration++; errorText = ""; }
        var previous = manifest;
        manifest = Object.assign({}, next, { domains: Object.assign({}, next.domains) });
        Object.keys(next.domains).forEach(function (kind) { if (previous && data[kind]) manifest.domains[kind] = previous.domains[kind]; });
        var changes = await Promise.all(Object.entries(next.domains).map(async function (entry) {
          if (!entry[1].url) return;
          try {
            var value = await get(entry[1]);
            if (entry[0] === "jobs") { value.loaded_jobs = await records(value.job_pages); value.loaded_workflows = await records(value.workflow_pages); jobs = value.loaded_jobs; workflows = value.loaded_workflows; }
            if (entry[0] === "queue" && data.queue) { value.loaded_waiting = data.queue.loaded_waiting; value.waiting_observed_at = data.queue.waiting_observed_at; }
            data[entry[0]] = value; manifest.domains[entry[0]] = entry[1]; render();
            if (entry[0] === "queue" && route().tab === "queue" && route().params.get("pr")) await lookup(route().params.get("pr"));
            if (entry[0] === "queue" && route().tab === "queue") {
              var batchID = route().params.get("batch") || selectedBatch || (value.batches.find(function (b) { return b.state === "head"; }) || value.batches[0] || {}).id;
              if (batchID && /^\d+$/.test(batchID)) await loadBatch(batchID);
            }
            if (entry[0] === "queue" && value.waiting_pages) {
              try { value.loaded_waiting = await records(value.waiting_pages); value.waiting_observed_at = value.observed_at; value.waiting_error = false; }
              catch (_) { value.waiting_error = true; }
              render();
            }
            return [entry[0], value];
          } catch (_) { return null; }
        }));
        // Slow or failed domains retain their own facts without delaying healthy ones.
        etag = changes.filter(Boolean).length === Object.values(next.domains).filter(function (d) { return d.url; }).length ? response.headers.get("etag") : null;
        if (route().tab === "history" && data.host_history && data.host_history.hosts.length) await loadHostHistory(selectedHistoryHost || data.host_history.hosts[0].machine_id);
      }
      disconnected = false; delay = 15000; render();
      if (data.queue && route().tab === "queue" && !detail) await navigate();
    } catch (_) { disconnected = true; delay = Math.min(60000, delay * 2); render(); }
    polling = false;
    clearTimeout(timer); if (!document.hidden) timer = setTimeout(poll, Math.max(0, delay - (Date.now() - started)));
  }
  window.addEventListener("hashchange", navigate);
  document.addEventListener("visibilitychange", function () { clearTimeout(timer); if (!document.hidden) poll(); });
  render(); poll();
})();
