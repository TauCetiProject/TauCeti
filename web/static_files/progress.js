// The Progress page: one row per roadmap, one segment per layer, beside the merged pull
// requests per week under that roadmap's label. Reads static/progress.json, which the Pages
// workflow regenerates with scripts/roadmap_progress.py (the committed copy is a fallback
// snapshot, like the chart SVGs). No dependencies; every string from the data is escaped before
// it reaches the document, and the data's shape is checked before anything is rendered.
(function () {
  "use strict";
  var root = document.getElementById("progress-board");
  if (!root) return;

  var STATES = ["done", "partial", "untouched", "unassessed"];
  var STATE_CLASS = { done: "d", partial: "p", untouched: "u", unassessed: "q" };
  var STATE_WORD = { done: "reported done", partial: "reported partial", untouched: "reported untouched", unassessed: "unassessed" };
  var REASON_TEXT = {
    "no-layers": "no layer inventory was extracted from the README, so there is nothing here to assess (which says nothing about the work)",
    "no-report": "no report has been written for this roadmap yet",
    "not-transcribed": "the report has not been transcribed into layer states yet",
    "transcription-retired": "the report changed after the layer states were transcribed, so the transcription was retired",
    "specification-changed": "the README changed after the layer states were transcribed, so the transcription was retired",
    "invalid-marker": "the report carries a coverage marker that does not fit this roadmap"
  };
  var REASON_SHORT = { "no-layers": "no layer inventory", "no-report": "no report yet", "not-transcribed": "report not transcribed",
    "transcription-retired": "transcription retired", "specification-changed": "README changed", "invalid-marker": "coverage marker invalid" };
  var ROADMAP_REPO = "https://github.com/TauCetiProject/TauCetiRoadmap";
  var LIBRARY_REPO = "https://github.com/TauCetiProject/TauCeti";
  var GH_PRS = LIBRARY_REPO + "/pulls?q=is%3Apr+is%3Amerged+label%3Aroadmap%2F";
  var SORTS = ["activity", "done", "due", "name"];
  var SHOWS = ["all", "active", "completed", "reported", "unreported", "unassessed", "due"];
  var DATE_RE = /^\d{4}-\d{2}-\d{2}$/;
  var TS_RE = /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$/;

  function esc(s) {
    return String(s).replace(/[&<>"']/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c];
    });
  }
  // Escaped text with `code` spans rendered; nothing else in the generated Markdown is interpreted.
  function inline(s) { return esc(s).replace(/`([^`]+)`/g, "<code>$1</code>"); }
  function domId(prefix, id) { return prefix + String(id).replace(/[^A-Za-z0-9]+/g, "-"); }
  function counts(states) {
    var c = { done: 0, partial: 0, untouched: 0, unassessed: 0 };
    states.forEach(function (s) { c[s]++; });
    return c;
  }
  function isCount(v) { return typeof v === "number" && isFinite(v) && v >= 0 && Math.floor(v) === v; }
  function isTs(v) { return typeof v === "string" && TS_RE.test(v) && !isNaN(Date.parse(v)) && new Date(v).toISOString() === v.replace(/Z$/, ".000Z"); }
  function isDay(v) { return typeof v === "string" && DATE_RE.test(v) && !isNaN(Date.parse(v)) && new Date(v).toISOString().slice(0, 10) === v; }
  function daysBetween(a, b) { return Math.round((Date.parse(b) - Date.parse(a)) / 86400000); }
  function plural(n, word) { return n + " " + word + (n === 1 ? "" : "s"); }

  // ---- data validation: everything that is rendered is checked first ----
  function validate(data) {
    if (!data || data.schema_version !== 3) return "unexpected data version";
    if (!Array.isArray(data.rows) || !Array.isArray(data.weeks) || !data.global) return "missing rows, weeks or global figures";
    if (!isTs(data.exported_at) || !isTs(data.cutoff)) return "missing export time or cutoff";
    if (data.collected_at !== null && !isTs(data.collected_at)) return "malformed collection time";
    if (!isCount(data.update_due_prs) || !isCount(data.recent_days)) return "malformed thresholds";
    if (!data.weeks.every(isDay)) return "malformed week labels";
    if (!Array.isArray(data.topics) || !data.topics.every(function (t) { return typeof t === "string"; })) return "malformed topic list";
    var g = data.global;
    if (!Array.isArray(g.weekly) || g.weekly.length !== data.weeks.length || !g.weekly.every(isCount)) return "malformed global weekly counts";
    if (!isCount(g.recent) || !isCount(g.total) || !isCount(g.open)) return "malformed global counts";
    if (g.first_merge !== null && !isTs(g.first_merge)) return "malformed first merge date";
    if (!g.unattributed || !isCount(g.unattributed.no_label) || !isCount(g.unattributed.several_labels) || !isCount(g.unattributed.unknown_area)) return "malformed attribution counts";
    var ids = {};
    for (var i = 0; i < data.rows.length; i++) {
      var r = data.rows[i], where = "row " + i;
      if (typeof r.id !== "string" || typeof r.name !== "string" || typeof r.title !== "string" || typeof r.topic !== "string" || typeof r.readme !== "string") return "malformed " + where;
      if (ids[r.id]) return "duplicate roadmap id " + r.id;
      ids[r.id] = true;
      if (r.parent_id !== null && typeof r.parent_id !== "string") return "malformed parent in " + r.id;
      if (!Array.isArray(r.layers) || !Array.isArray(r.states) || !Array.isArray(r.layer_ids) || !Array.isArray(r.layer_lines) || r.layers.length !== r.states.length || r.layer_ids.length !== r.layers.length || r.layer_lines.length !== r.layers.length) return "layers, ids, lines and states do not align in " + r.id;
      if (!r.layer_lines.every(function (n) { return isCount(n) && n > 0; })) return "malformed layer lines in " + r.id;
      if (!Array.isArray(r.links) || !r.links.every(function (l) { return l && typeof l.label === "string" && typeof l.url === "string" && /^https:\/\//.test(l.url); })) return "malformed links in " + r.id;
      if (!r.layers.every(function (l) { return typeof l === "string"; }) || !r.layer_ids.every(function (l) { return typeof l === "string"; })) return "malformed layer titles in " + r.id;
      var seenIds = {};
      for (var q = 0; q < r.layer_ids.length; q++) { if (seenIds[r.layer_ids[q]]) return "repeated layer id in " + r.id; seenIds[r.layer_ids[q]] = true; }
      for (var j = 0; j < r.states.length; j++) if (STATES.indexOf(r.states[j]) < 0) return "unknown layer state in " + r.id;
      if (!r.assessment || typeof r.assessment.reason !== "string") return "missing assessment in " + r.id;
      if (r.status !== null) {
        var s = r.status;
        if (!s || typeof s.to_sha !== "string" || !/^[0-9a-f]{7,40}$/.test(s.to_sha) || (s.ts !== null && !isTs(s.ts)) || typeof s.glance !== "string" || !Array.isArray(s.frontier) || typeof s.path !== "string" || typeof s.progress_path !== "string") return "malformed report in " + r.id;
        if (!s.frontier.every(function (f) { return f && typeof f.name === "string" && typeof f.text === "string"; })) return "malformed frontier in " + r.id;
      }
      if (r.activity !== null) {
        var a = r.activity;
        if (!a || !Array.isArray(a.weekly) || a.weekly.length !== data.weeks.length || !a.weekly.every(isCount) || !isCount(a.total) || !isCount(a.recent) || !isCount(a.open)) return "malformed activity in " + r.id;
        if (a.last !== null && !isTs(a.last)) return "malformed last-merge date in " + r.id;
        if (a.since_report !== null && !isCount(a.since_report)) return "malformed since-report count in " + r.id;
      }
      if (r.retired !== null && (!r.retired || !Array.isArray(r.retired.states) || r.retired.states.length !== r.layers.length || !r.retired.states.every(function (s) { return STATES.indexOf(s) >= 0; }))) return "malformed retired reading in " + r.id;
    }
    for (var k = 0; k < data.rows.length; k++) if (data.rows[k].parent_id !== null && !ids[data.rows[k].parent_id]) return "unknown parent for " + data.rows[k].id;
    return null;
  }

  // ---- URL state ----
  var state = { group: "topic", sort: "activity", show: "all", q: "", open: [], kids: [], closed: [] };
  function readUrl() {
    try {
      var q = new URLSearchParams(location.search);
      state.group = q.get("group") === "none" ? "none" : "topic";
      state.sort = SORTS.indexOf(q.get("sort")) >= 0 ? q.get("sort") : "activity";
      state.show = SHOWS.indexOf(q.get("show")) >= 0 ? q.get("show") : "all";
      state.q = q.get("q") || "";
      state.open = (q.get("open") || "").split(",").filter(Boolean);
      state.kids = (q.get("kids") || "").split(",").filter(Boolean);
      state.closed = (q.get("closed") || "").split(",").filter(Boolean);
    } catch (e) { /* no query string */ }
  }
  function writeUrl(push) {
    try {
      var q = new URLSearchParams();
      if (state.group !== "topic") q.set("group", state.group);
      if (state.sort !== "activity") q.set("sort", state.sort);
      if (state.show !== "all") q.set("show", state.show);
      if (state.q) q.set("q", state.q);
      if (state.open.length) q.set("open", state.open.join(","));
      if (state.kids.length) q.set("kids", state.kids.join(","));
      if (state.closed.length && state.q) q.set("closed", state.closed.join(","));
      var s = q.toString();
      var url = location.pathname + (s ? "?" + s : "");
      if (push) history.pushState(null, "", url); else history.replaceState(null, "", url);
    } catch (e) { /* history unavailable */ }
  }

  function render(data) {
    var rows = data.rows;
    var cutoff = data.cutoff, cutoffDay = cutoff.slice(0, 10);
    var byId = {};
    rows.forEach(function (r) { byId[r.id] = r; });
    var tops = rows.filter(function (r) { return r.parent_id === null; });
    function kids(r) { return rows.filter(function (x) { return x.parent_id === r.id; }); }
    function isLeaf(r) { return !kids(r).length; }
    function aggregate(r) {
      var ch = kids(r);
      if (!ch.length) return null;
      var c = { done: 0, partial: 0, untouched: 0, unassessed: 0 }, n = 0;
      ch.forEach(function (k) { var kc = counts(k.states); STATES.forEach(function (s) { c[s] += kc[s]; }); n += k.layers.length; });
      return { c: c, n: n, subs: ch.length };
    }
    function due(r) { return !r.completed && r.status && r.activity && r.activity.since_report !== null && r.activity.since_report >= data.update_due_prs; }
    function hasReport(r) { return !!r.status; }
    function ownReport(r) { return !!r.status && !r.status.inherited; }
    function reportAge(r) { return r.status && r.status.ts ? daysBetween(r.status.ts, cutoff) : null; }
    function beforeText(ts) {
      var n = daysBetween(ts, cutoff);
      if (n <= 0) return "on the cutoff day";
      return n === 1 ? "1 day before the cutoff" : n + " days before the cutoff";
    }

    // ---- bars: a common linear scale across every row, so heights compare ----
    var rowMax = 1;
    rows.forEach(function (r) { if (r.activity) r.activity.weekly.forEach(function (v) { if (v > rowMax) rowMax = v; }); });
    function bars(values, w, h, max, label) {
      var n = values.length, gap = 2, bw = (w - gap * (n - 1)) / n;
      var s = '<svg class="pb-bars" viewBox="0 0 ' + w + " " + h + '" preserveAspectRatio="none" role="img" aria-label="' + esc(label) + '">';
      s += '<line x1="0" y1="' + (h - 0.5) + '" x2="' + w + '" y2="' + (h - 0.5) + '" class="pb-baseline"/>';
      values.forEach(function (v, i) {
        var bh = v === 0 ? 0 : Math.max(1.5, (v / max) * (h - 3));
        var x = i * (bw + gap), now = i === n - 1;
        s += '<rect x="' + x.toFixed(2) + '" y="' + (h - 1 - bh).toFixed(2) + '" width="' + bw.toFixed(2) + '" height="' + bh.toFixed(2) + '" rx="1" class="' + (now ? "pb-bar-now" : "pb-bar") + '"><title>week of ' + esc(data.weeks[i]) + ": " + v + " merged" + (now ? " (the week of the cutoff, incomplete)" : "") + "</title></rect>";
      });
      return s + "</svg>";
    }
    function weeklyTable(values) {
      var s = '<table class="pb-weeks"><caption>Merged pull requests per week, weeks starting Monday, up to the cutoff; the last week is incomplete</caption><tbody>';
      values.forEach(function (v, i) { s += '<tr><th scope="row">' + esc(data.weeks[i]) + "</th><td>" + v + "</td></tr>"; });
      return s + "</tbody></table>";
    }

    // ---- legend and tiles ----
    function legend() {
      return '<div class="pb-legend pb-legend-main" aria-label="Layer states">' +
        '<span><span class="pb-sw d"></span>reported done</span>' +
        '<span><span class="pb-sw p"></span>reported partial</span>' +
        '<span><span class="pb-sw u"></span>reported untouched</span>' +
        '<span><span class="pb-sw q"></span>unassessed: no report, or the report does not say</span>' +
        '<span class="pb-legend-note">What each roadmap’s latest report says, not a percentage of the work.</span>' +
        '<button type="button" class="pb-jump">Jump to the roadmaps \u2193</button></div>';
    }
    function stack(c, cls) {
      var total = STATES.reduce(function (a, s) { return a + c[s]; }, 0);
      return '<div class="pb-stack ' + (cls || "") + '" role="img" aria-label="' + STATES.map(function (s) { return c[s] + " " + STATE_WORD[s]; }).join(", ") + '">' +
        STATES.filter(function (s) { return c[s] > 0; }).map(function (s) { return '<span class="' + STATE_CLASS[s] + '" style="flex:' + c[s] + '" title="' + STATE_WORD[s] + ": " + c[s] + " of " + total + '"></span>'; }).join("") + "</div>";
    }
    function tiles() {
      var active = tops.filter(function (r) { return !r.completed; }).length;
      var completed = tops.filter(function (r) { return r.completed; }).length;
      var subs = rows.length - tops.length;
      var tot = { done: 0, partial: 0, untouched: 0, unassessed: 0 };
      rows.forEach(function (r) { if (!isLeaf(r)) return; var c = counts(r.states); STATES.forEach(function (s) { tot[s] += c[s]; }); });
      var layerTotal = STATES.reduce(function (a, s) { return a + tot[s]; }, 0);
      var g = data.global;
      var reported = tops.filter(ownReport);
      var ages = reported.map(reportAge).filter(function (a) { return a !== null; }).sort(function (a, b) { return a - b; });
      var dueN = tops.filter(due).length;
      var un = g.unattributed, unN = un.no_label + un.several_labels + un.unknown_area;
      var gmax = Math.max.apply(null, g.weekly.concat([1]));
      return '<div class="pb-tiles">' +
        '<div class="pb-tile"><div class="pb-label">Roadmaps</div><div class="pb-big">' + active + "<small>active</small></div>" +
          '<div class="pb-sub"><b>' + completed + "</b> declared complete · <b>" + subs + "</b> sub-roadmaps</div></div>" +
        '<div class="pb-tile"><div class="pb-label">Layers, all roadmaps</div><div class="pb-big">' + tot.done + "<small>of " + layerTotal + " reported done</small></div>" +
          stack(tot) +
          '<div class="pb-legend">' + STATES.map(function (s) { return '<span><span class="pb-sw ' + STATE_CLASS[s] + '"></span><b>' + tot[s] + "</b> " + s + "</span>"; }).join("") + "</div></div>" +
        '<div class="pb-tile pb-tile-more"><div class="pb-label">Merged pull requests</div><div class="pb-big">' + g.recent + "<small>in " + data.recent_days + " days, all of Tau Ceti</small></div>" +
          bars(g.weekly, 200, 34, gmax, "All merged pull requests per week, " + data.weeks.length + " weeks") +
          '<div class="pb-sub"><b>' + g.total + "</b> merged up to the cutoff" + (g.first_merge ? ", since " + esc(g.first_merge.slice(0, 10)) : "") + " · <b>" + g.open + "</b> open" + (unN ? " · <b>" + unN + "</b> merged with no single roadmap label" : "") + "</div></div>" +
        '<div class="pb-tile pb-tile-more"><div class="pb-label">Reports</div><div class="pb-big">' + reported.length + "<small>of " + tops.length + " roadmaps</small></div>" +
          '<div class="pb-sub">' + (ages.length ? "oldest <b>" + ages[ages.length - 1] + "</b> days before the cutoff · " : "") + "<b>" + dueN + "</b> due an update (" + data.update_due_prs + "+ PRs since)</div></div>" +
        '<button type="button" class="pb-more" aria-expanded="false">More figures</button>' +
        "</div>";
    }

    // ---- search ----
    function matchInfo(r) {
      var q = state.q.toLowerCase();
      if (!q) return { hit: true, where: null };
      if ((r.name + " " + r.title).toLowerCase().indexOf(q) >= 0) return { hit: true, where: null };
      if (r.topic.toLowerCase().indexOf(q) >= 0) return { hit: true, where: "topic " + r.topic };
      for (var i = 0; i < r.layers.length; i++) if (r.layers[i].toLowerCase().indexOf(q) >= 0) return { hit: true, where: "layer “" + r.layers[i] + "”" };
      if (r.status) {
        if (r.status.glance.toLowerCase().indexOf(q) >= 0) return { hit: true, where: "the report’s summary" };
        for (var j = 0; j < r.status.frontier.length; j++) {
          var f = r.status.frontier[j];
          if ((f.name + " " + f.text).toLowerCase().indexOf(q) >= 0) return { hit: true, where: "the frontier: " + f.name };
        }
      }
      return { hit: false, where: null };
    }
    function passesShow(r) {
      switch (state.show) {
        case "active": return !r.completed;
        case "completed": return r.completed;
        case "reported": return hasReport(r);
        case "unreported": return !hasReport(r);
        case "unassessed": var ag = aggregate(r); return ag ? ag.c.unassessed > 0 : r.states.indexOf("unassessed") >= 0;
        case "due": return due(r);
        default: return true;
      }
    }
    function visible(r) { return passesShow(r) && matchInfo(r).hit; }
    function filtering() { return !!state.q || state.show !== "all"; }

    // ---- rows ----
    function strip(r) {
      var ag = aggregate(r);
      if (ag) return '<div class="pb-agg">' + stack(ag.c, "pb-stack-row") + '<span class="pb-faint">all layers of ' + ag.subs + " sub-roadmaps</span></div>";
      if (!r.layers.length) return '<div class="pb-covtext"><span class="pb-none">no layer inventory extracted</span></div>';
      return '<div class="pb-strip" role="img" aria-label="' + esc(r.layers.map(function (l, i) { return l + ": " + STATE_WORD[r.states[i]]; }).join("; ")) + '">' +
        r.layers.map(function (l, i) { return '<span class="' + STATE_CLASS[r.states[i]] + '" title="' + esc(l) + " — " + STATE_WORD[r.states[i]] + '"></span>'; }).join("") + "</div>";
    }
    function covText(r) {
      var ag = aggregate(r), c = ag ? ag.c : counts(r.states), n = ag ? ag.n : r.layers.length;
      var a = r.assessment;
      if (!ag && (a.reason !== "ok")) return '<div class="pb-covtext"><span class="pb-none">' + esc(REASON_SHORT[a.reason] || a.reason) + "</span>" + (n ? '<br><span class="pb-faint">' + plural(n, "layer") + " unassessed</span>" : "") + "</div>";
      var parts = [];
      if (c.done) parts.push("<b>" + c.done + "</b> done");
      if (c.partial) parts.push("<b>" + c.partial + "</b> partial");
      if (c.untouched) parts.push(c.untouched + " untouched");
      if (c.unassessed) parts.push(c.unassessed + " unassessed");
      return '<div class="pb-covtext">' + parts.join(" · ") + '<br><span class="pb-faint">of ' + plural(n, "layer") + (ag ? " across " + ag.subs + " sub-roadmaps" : "") + "</span></div>";
    }
    function activityCell(r) {
      if (!r.activity) return '<div class="pb-covtext"><span class="pb-none">' + (r.parent_id ? "shares the parent’s label" : "no labelled pull requests") + "</span></div>";
      return bars(r.activity.weekly, 128, 28, rowMax, "Merged pull requests per week, common scale, most recent " + data.weeks.length + " weeks");
    }
    function lastCell(r) {
      var a = r.activity;
      if (!a) return '<div class="pb-num"><span class="pb-sub">' + (r.parent_id ? "" : "\u2014") + "</span></div>";
      var openText = a.open ? '<span class="pb-sub pb-open">' + plural(a.open, "open PR") + "</span>" : "";
      if (!a.last) return '<div class="pb-num"><span class="pb-sub">none merged</span>' + openText + "</div>";
      return '<div class="pb-num">' + esc(a.last.slice(0, 10)) + '<span class="pb-sub">' + esc(beforeText(a.last)) + " \u00b7 " + a.total + " merged</span>" + openText + "</div>";
    }
    function reportCell(r) {
      if (!r.status) return '<div class="pb-age"><span class="pb-none">none</span></div>';
      var s = r.status, since = r.activity && r.activity.since_report !== null ? r.activity.since_report : null;
      if (s.inherited) return '<div class="pb-age"><span class="pb-sub">via ' + esc(r.parent) + "</span></div>";
      return '<div class="pb-age' + (due(r) ? " stale" : "") + '">' + (s.ts ? esc(s.ts.slice(0, 10)) : '<span class="pb-none">undated</span>') + '<span class="pb-sub">library <span class="pb-sha">' + esc(s.to_sha.slice(0, 7)) + "</span></span>" +
        (since !== null ? '<span class="pb-sub">' + plural(since, "PR") + " merged since</span>" : "") + "</div>";
    }
    function chips(r) {
      var out = "";
      if (r.completed) out += '<a class="pb-chip complete" href="' + ROADMAP_REPO + '/blob/main/Completed/README.md" title="The maintainers archived this roadmap as complete against its README; a human decision, separate from the report’s layer states.">declared complete</a>';
      if (due(r)) out += '<span class="pb-chip behind" title="' + r.activity.since_report + ' pull requests merged since the report; TauCetiProgress opens a new window at ' + data.update_due_prs + '">update due</span>';
      return out;
    }
    function rowHtml(r, ctx, shownKids, totalKids) {
      var open = state.open.indexOf(r.id) >= 0;
      var mi = matchInfo(r);
      var kidsLabel = totalKids ? ((shownKids === null ? "show " : "hide ") + (filtering() && shownKids !== null && shownKids !== totalKids ? shownKids + " of " + totalKids + " sub-roadmaps" : plural(totalKids, "sub-roadmap"))) : "";
      var name = '<div class="pb-namecell">' +
        '<button type="button" class="pb-toggle" aria-expanded="' + open + '" aria-controls="' + domId("rd-", r.id) + '" data-open="' + esc(r.id) + '"><span class="pb-chev" aria-hidden="true">' + (open ? "▾" : "▸") + '</span><span class="pb-vh">' + (open ? "Hide" : "Show") + " details for " + esc(r.name) + "</span></button>" +
        '<div><div class="pb-name"><a href="' + ROADMAP_REPO + "/blob/main/" + esc(r.readme) + '">' + esc(r.name) + "</a>" + chips(r) + (ctx ? '<span class="pb-chip" title="Shown because a sub-roadmap matches; this row itself does not">context</span>' : "") + "</div>" +
        '<div class="pb-title">' + esc(r.title) + "</div>" +
        (mi.where ? '<div class="pb-matched">matches ' + esc(mi.where) + "</div>" : "") +
        (totalKids ? '<button type="button" class="pb-kids" aria-expanded="' + (shownKids !== null) + '" data-kids="' + esc(r.id) + '">' + esc(kidsLabel) + "</button>" : "") +
        "</div></div>";
      return '<tr class="pb-row' + (r.parent_id ? " child" : "") + (ctx ? " context" : "") + '" id="' + domId("rm-", r.id) + '">' +
        '<td class="pb-c-name">' + name + "</td>" +
        '<td class="pb-c-strip">' + strip(r) + "</td>" +
        '<td class="pb-c-cov">' + covText(r) + "</td>" +
        '<td class="pb-c-act">' + activityCell(r) + "</td>" +
        '<td class="pb-c-last">' + lastCell(r) + "</td>" +
        '<td class="pb-c-rep">' + reportCell(r) + "</td></tr>" +
        '<tr class="pb-detail" id="' + domId("rd-", r.id) + '"' + (open ? "" : " hidden") + '><td colspan="6">' + (open ? detailHtml(r) : "") + "</td></tr>";
    }
    function pinned(path) { return ROADMAP_REPO + "/blob/" + (typeof data.roadmap_head === "string" && /^[0-9a-f]{7,40}$/.test(data.roadmap_head) ? data.roadmap_head : "main") + "/" + esc(path); }
    function detailHtml(r) {
      var s = r.status, a = r.assessment, left = "", right = "";
      if (s) {
        left += "<h4>The report says" + (s.inherited ? " (the " + esc(r.parent) + " report, which covers this sub-roadmap)" : "") + (s.ts ? ", as of " + esc(s.ts.slice(0, 10)) : "") + "</h4>";
        left += "<p>" + (s.glance ? inline(s.glance) : '<span class="pb-none">the report has no summary sentence</span>') + "</p>";
        if (s.frontier.length && !s.inherited) left += "<h4>Frontier, as reported on that date</h4><ul>" + s.frontier.map(function (f) { return "<li><b>" + inline(f.name) + "</b> " + inline(f.text) + "</li>"; }).join("") + "</ul>";
      } else if (r.completed) {
        left += "<h4>No report</h4><p>No STATUS.md has been written for this roadmap. It is archived as declared complete; see the archive’s README for the maintainers’ criterion.</p>";
      } else {
        left += "<h4>No report yet</h4><p>TauCetiProgress has not written a STATUS.md for this roadmap. Its layers are unassessed, which says nothing about how much of them the library has.</p>";
      }
      var sources = ['<a href="' + pinned(r.readme) + '">README used for these layers</a>', '<a href="' + ROADMAP_REPO + "/blob/main/" + esc(r.readme) + '">latest README</a>'];
      if (s) {
        sources.push('<a href="' + pinned(s.path) + '">report used here' + (s.inherited ? " (parent’s)" : "") + "</a>");
        sources.push('<a href="' + ROADMAP_REPO + "/blob/main/" + esc(s.path) + '">latest report</a>');
        sources.push('<a href="' + ROADMAP_REPO + "/blob/main/" + esc(s.progress_path) + '">progress log</a>');
        sources.push('<a href="' + LIBRARY_REPO + "/commit/" + esc(s.to_sha) + '">library commit the report describes</a>');
      }
      if (!r.parent_id) sources.push('<a href="' + GH_PRS + encodeURIComponent(r.name) + '">merged pull requests with this label</a>');
      if (r.completed) sources.push('<a href="' + ROADMAP_REPO + '/blob/main/Completed/README.md">completion decision</a>');
      r.links.forEach(function (l) { sources.push('<a href="' + esc(l.url) + '" rel="noopener">' + esc(l.label) + " \u2197</a>"); });
      left += '<div class="pb-links">' + sources.join("") + '<button type="button" class="pb-copy" data-copy="' + esc(r.id) + '">Copy link to this roadmap</button></div>';
      var evid = "Topic: " + esc(r.topic) + " (a hand assignment). ";
      if (a.reason === "ok") evid += "Layer states come from " + (a.source === "marker" ? "the coverage marker in the report" : "a hand transcription of the report’s prose, bound to that exact report and README") + "; they are the report’s assessment at library commit " + esc(s.to_sha.slice(0, 7)) + ", not a certificate that each layer’s specification is fully met. ";
      else evid += "Layer states are unassessed: " + esc(REASON_TEXT[a.reason] || a.reason) + (typeof a.detail === "string" && a.detail ? " (" + esc(a.detail) + ")" : "") + ". ";
      evid += "Pull-request counts come from labels. ";
      if (r.completed) evid += "“Declared complete” is the maintainers’ decision, recorded in the archive; it is independent of the layer states above.";
      left += '<div class="pb-evid">' + evid + "</div>";
      if (r.layers.length) {
        var notes = a.notes && typeof a.notes === "object" ? a.notes : {};
        var remaining = a.remaining && typeof a.remaining === "object" ? a.remaining : {};
        right += '<h4>Layers <span class="pb-ev">each linked to its heading in the README used</span></h4><ul class="pb-layers">' + r.layers.map(function (l, i) {
          var note = notes[r.layer_ids[i]], rem = remaining[r.layer_ids[i]];
          return '<li><span class="pb-dot ' + STATE_CLASS[r.states[i]] + '"></span><span><a href="' + pinned(r.readme) + "?plain=1#L" + r.layer_lines[i] + '">' + esc(l) + '</a> <span class="pb-faint">\u00b7 ' + STATE_WORD[r.states[i]] + "</span>" +
            (typeof rem === "string" ? '<div class="pb-note"><b>Remaining:</b> ' + inline(rem) + "</div>" : "") +
            (typeof note === "string" ? '<div class="pb-note">' + esc(note) + "</div>" : "") + "</span></li>";
        }).join("") + "</ul>";
        if (r.retired) right += '<div class="pb-note">A retired transcription' + (typeof r.retired.to_sha === "string" ? ", made against library commit " + esc(r.retired.to_sha) : "") + ", read: " + esc(r.layers.map(function (l, i) { return l + ": " + r.retired.states[i]; }).join("; ")) + ". It is not the current report.</div>";
      }
      if (r.activity) right += "<h4>Activity</h4>" + weeklyTable(r.activity.weekly);
      else if (r.parent_id) right += '<h4>Activity</h4><p class="pb-faint">Pull requests are labelled with the parent roadmap, so activity cannot be split by sub-roadmap.</p>';
      if (r.activity && r.activity.open) right += '<p class="pb-faint">' + plural(r.activity.open, "pull request") + " open with this label when the snapshot was taken (the queue as it stood then, not as of the cutoff): work in flight that no report describes yet.</p>";
      return '<div class="pb-detail-inner"><div>' + left + "</div><div>" + right + "</div></div>";
    }
    // Totals over the rows that actually match: a top-level match counts itself (or, for an
    // umbrella, all its children); a context-only parent counts only its matching children.
    function topicHeader(t, members) {
      var c = { done: 0, partial: 0, untouched: 0, unassessed: 0 }, n = 0, recent = 0, nTop = 0, nSub = 0;
      function add(r) { var ag = aggregate(r), cc = ag ? ag.c : counts(r.states); STATES.forEach(function (s) { c[s] += cc[s]; }); n += ag ? ag.n : r.layers.length; }
      members.forEach(function (r) {
        if (visible(r)) { add(r); nTop++; recent += r.activity ? r.activity.recent : 0; }
        else kids(r).filter(visible).forEach(function (k) { add(k); nSub++; });
      });
      var m = filtering() ? "matching " : "";
      var what = nTop ? plural(nTop, m + "roadmap") + (nSub ? " and " + plural(nSub, "sub-roadmap") : "") : plural(nSub, m + "sub-roadmap");
      return '<tr class="pb-topic"><td colspan="6"><span class="pb-tname">' + esc(t) + '</span><span class="pb-tstat">' + what + " · " + plural(n, "layer") + ": <b>" + c.done + "</b> reported done, <b>" + c.partial + "</b> partial, " + c.untouched + " untouched, " + c.unassessed + " unassessed" + (nTop ? " · <b>" + recent + "</b> PRs merged in " + data.recent_days + " days" : "") + "</span></td></tr>";
    }

    // ---- ordering ----
    // The done fraction is a count of headings; a roadmap with no assessment sorts after every
    // assessed one, including those whose report says nothing is done.
    function doneKey(r) { var ag = aggregate(r); if (ag) return ag.n ? ag.c.done / ag.n : -1; if (r.assessment.reason !== "ok" || !r.layers.length) return -1; return counts(r.states).done / r.layers.length; }
    function act(r, k) { return r.activity ? r.activity[k] : -1; }
    var sorters = {
      activity: function (a, b) { return (act(b, "recent") - act(a, "recent")) || (act(b, "total") - act(a, "total")) || a.name.localeCompare(b.name); },
      done: function (a, b) { return (doneKey(b) - doneKey(a)) || a.name.localeCompare(b.name); },
      due: function (a, b) { function s(r) { return r.activity && r.status && r.activity.since_report !== null ? r.activity.since_report : -1; } return (s(b) - s(a)) || a.name.localeCompare(b.name); },
      name: function (a, b) { return a.name.localeCompare(b.name); }
    };

    function renderRows() {
      var s = sorters[state.sort];
      var order = tops.slice().sort(s), out = [], shown = 0;
      function emit(r) {
        var ch = kids(r), chVisible = ch.filter(visible), self = visible(r);
        if (!self && !chVisible.length) return;
        var expand = ch.length && (state.kids.indexOf(r.id) >= 0 || (!!state.q && chVisible.length > 0 && state.closed.indexOf(r.id) < 0));
        out.push(rowHtml(r, !self, expand ? chVisible.length : null, ch.length));
        if (self) shown++;
        if (expand) chVisible.sort(state.sort === "name" ? sorters.name : s).forEach(function (c) { out.push(rowHtml(c, false, null, 0)); shown++; });
      }
      if (state.group === "topic") {
        data.topics.concat(["Unsorted"]).forEach(function (t) {
          var members = order.filter(function (r) { return r.topic === t && (visible(r) || kids(r).some(visible)); });
          if (!members.length) return;
          out.push(topicHeader(t, members));
          members.forEach(emit);
        });
      } else {
        order.forEach(emit);
      }
      if (!out.length) out.push('<tr class="pb-empty"><td colspan="6">No roadmaps match ' + (state.q ? "“" + esc(state.q) + "”" : "this filter") + '. <button type="button" class="pb-reset">Show all roadmaps</button></td></tr>');
      root.querySelector(".pb-rows").innerHTML = out.join("");
      root.querySelector(".pb-count").textContent = plural(shown, "roadmap") + " shown of " + rows.length;
      root.querySelector("[data-group]").value = state.group;
      root.querySelector("[data-sort]").value = state.sort;
      root.querySelector("[data-show]").value = state.show;
      var search = root.querySelector(".pb-search");
      if (search.value !== state.q) search.value = state.q;
    }

    // ---- assemble ----
    var head = typeof data.roadmap_head === "string" ? "TauCetiRoadmap@" + esc(data.roadmap_head.slice(0, 7)) : "TauCetiRoadmap";
    var age = daysBetween(cutoff, new Date().toISOString());
    var when = "Pull requests count up to <b>" + esc(cutoff.replace("T", " ").replace("Z", " UTC")) + "</b>" +
      (data.collected_at ? " (fetched " + esc(data.collected_at.replace("T", " ").replace("Z", " UTC")) + ")" : " (when they were fetched is not recorded)") +
      "; roadmaps read from <code>" + head + "</code>; this file written " + esc(data.exported_at.replace("T", " ").replace("Z", " UTC")) + ".";
    root.innerHTML =
      legend() +
      '<p class="pb-lede">' + when + (age > 2 ? " That cutoff is <b>" + plural(age, "day") + " ago</b>; dates below are relative to it, not to today." : " Dates below are relative to the cutoff.") + "</p>" +
      tiles() +
      '<div class="pb-controls" id="pb-roadmaps" aria-label="Group, sort and filter">' +
        '<label class="pb-group"><span>Group</span><select data-group><option value="topic">by topic</option><option value="none">no grouping</option></select></label>' +
        '<label class="pb-group"><span>Sort</span><select data-sort><option value="activity">recent activity</option><option value="done">layers reported done</option><option value="due">update due</option><option value="name">name</option></select></label>' +
        '<label class="pb-group"><span>Show</span><select data-show><option value="all">all</option><option value="active">active</option><option value="completed">declared complete</option><option value="reported">with a report</option><option value="unreported">without a report</option><option value="unassessed">with unassessed layers</option><option value="due">update due</option></select></label>' +
        '<label class="pb-group"><span class="pb-vh">Find</span><input type="search" class="pb-search" placeholder="Find a roadmap, layer or theorem" value="' + esc(state.q) + '"></label>' +
        '<div class="pb-count"></div></div>' +
      '<table class="pb-table"><thead><tr class="pb-hdr">' +
        '<th scope="col">Roadmap</th><th scope="col">Layers <span class="pb-ev">from the report · model-judged</span></th><th scope="col">Coverage</th>' +
        '<th scope="col">Merged PRs, ' + data.weeks.length + ' weeks <span class="pb-ev">from labels · mechanical</span></th><th scope="col">Pull requests <span class="pb-ev">last merged · open</span></th><th scope="col">Report</th></tr></thead>' +
        '<tbody class="pb-rows"></tbody></table>';
    renderRows();

    // ---- events ----
    root.addEventListener("change", function (e) {
      var t = e.target;
      if (t.hasAttribute("data-group")) state.group = t.value;
      else if (t.hasAttribute("data-sort")) state.sort = t.value;
      else if (t.hasAttribute("data-show")) state.show = t.value;
      else return;
      writeUrl(true); renderRows();
    });
    var searchTimer = null;
    root.querySelector(".pb-search").addEventListener("input", function (e) {
      var next = e.target.value.trim();
      if (next !== state.q) state.closed = [];
      state.q = next;
      clearTimeout(searchTimer);
      searchTimer = setTimeout(function () { writeUrl(false); renderRows(); }, 120);
    });
    function refocus(selector) { var el = root.querySelector(selector); if (el) el.focus(); }
    root.addEventListener("click", function (e) {
      var b = e.target.closest("button");
      if (!b) return;
      if (b.hasAttribute("data-open")) {
        var id = b.getAttribute("data-open"), i = state.open.indexOf(id);
        if (i >= 0) state.open.splice(i, 1); else state.open.push(id);
        writeUrl(false); renderRows(); refocus('[data-open="' + CSS.escape(id) + '"]');
      } else if (b.hasAttribute("data-kids")) {
        // Expanded either explicitly (kids) or by a matching search; collapsing an auto-expanded
        // list is recorded as an explicit close, which the next query change forgets.
        var p = b.getAttribute("data-kids"), j = state.kids.indexOf(p), k = state.closed.indexOf(p);
        var expanded = b.getAttribute("aria-expanded") === "true";
        // Both forms of expansion can hold at once (opened by hand, then a matching search), so a
        // collapse drops the explicit open and records the explicit close.
        if (expanded) { if (j >= 0) state.kids.splice(j, 1); if (k < 0) state.closed.push(p); }
        else { if (k >= 0) state.closed.splice(k, 1); if (j < 0) state.kids.push(p); }
        writeUrl(false); renderRows(); refocus('[data-kids="' + CSS.escape(p) + '"]');
      } else if (b.classList.contains("pb-reset")) {
        state.q = ""; state.show = "all";
        writeUrl(true); renderRows(); refocus(".pb-search");
      } else if (b.classList.contains("pb-jump")) {
        // The page carries a <base>, so a bare fragment href would resolve against the site root;
        // scroll within this document instead, allowing for the sticky site navigation.
        var controls = root.querySelector(".pb-controls");
        var nav = document.querySelector(".site-nav");
        controls.scrollIntoView({ block: "start", behavior: "instant" });
        window.scrollBy({ top: -((nav ? nav.getBoundingClientRect().height : 0) + 8), behavior: "instant" });
        var first = controls.querySelector("select, input");
        if (first) first.focus({ preventScroll: true });
      } else if (b.classList.contains("pb-more")) {
        var on = root.querySelector(".pb-tiles").classList.toggle("expanded");
        b.setAttribute("aria-expanded", String(on)); b.textContent = on ? "Fewer figures" : "More figures";
      } else if (b.hasAttribute("data-copy")) {
        var n = b.getAttribute("data-copy"), q = new URLSearchParams({ open: n });
        var parent = byId[n] && byId[n].parent_id;
        if (parent) q.set("kids", parent);
        var url = location.origin + location.pathname + "?" + q.toString() + "#" + domId("rm-", n);
        var done = function () { b.textContent = "Link copied"; setTimeout(function () { b.textContent = "Copy link to this roadmap"; }, 1500); };
        if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(url).then(done, function () { window.prompt("Link to this roadmap", url); });
        else window.prompt("Link to this roadmap", url);
      }
    });
    window.addEventListener("popstate", function () { readUrl(); renderRows(); });

    // A permalink: reveal the named row (its parent's list too) and scroll to it.
    if (location.hash && location.hash.indexOf("#rm-") === 0) {
      var target = document.getElementById(location.hash.slice(1));
      if (target) target.scrollIntoView();
    }
  }

  readUrl();
  fetch("static/progress.json", { cache: "no-cache" })
    .then(function (r) { if (!r.ok) throw new Error(r.status + " " + r.statusText); return r.json(); })
    .then(function (data) {
      var problem = validate(data);
      if (problem) throw new Error("the progress data is not in the expected shape: " + problem);
      render(data);
    })
    .catch(function (err) {
      root.innerHTML = '<p class="pb-error">The progress board could not be shown (' + esc(err.message) + "). The roadmaps themselves, with each one’s STATUS.md report, are at " +
        '<a href="' + ROADMAP_REPO + '">TauCetiRoadmap</a>; the board’s data is <a href="static/progress.json">progress.json</a>.</p>';
    });
})();
