// The Progress page: one row per roadmap, one segment per layer, beside the merged pull
// requests per week under that roadmap's label. Reads static/progress.json, which the Pages
// workflow regenerates with scripts/roadmap_progress.py (the committed copy is a fallback
// snapshot, like the chart SVGs). No dependencies.
(function () {
  "use strict";
  var root = document.getElementById("progress-board");
  if (!root) return;

  var STATES = ["done", "partial", "untouched", "unassessed"];
  var STATE_CLASS = { done: "d", partial: "p", untouched: "u", unassessed: "q" };
  var GH_ROADMAP = "https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/";
  var GH_PRS = "https://github.com/TauCetiProject/TauCeti/pulls?q=is%3Apr+is%3Amerged+label%3Aroadmap%2F";

  function esc(s) {
    return String(s).replace(/[&<>"]/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c];
    });
  }
  function counts(states) {
    var c = { done: 0, partial: 0, untouched: 0, unassessed: 0 };
    states.forEach(function (s) { c[s]++; });
    return c;
  }
  function dirOf(r) {
    return (r.completed ? "Completed/" : "TauCetiRoadmap/") + (r.parent ? r.parent + "/" : "") + r.name + "/";
  }
  function daysBetween(a, b) { return Math.round((Date.parse(b) - Date.parse(a)) / 86400000); }
  function ago(n) {
    if (n === null || n === undefined) return "";
    if (n <= 0) return "today";
    if (n === 1) return "1 day ago";
    if (n < 60) return n + " days ago";
    return Math.round(n / 30) + " months ago";
  }

  function render(data) {
    var rows = data.rows;
    var today = data.generated_at;
    var tops = rows.filter(function (r) { return !r.parent; });
    function kids(name) { return rows.filter(function (r) { return r.parent === name; }); }
    function assessed(r) { return !!r.states_source; }
    function aggregate(r) {
      var ch = kids(r.name);
      if (!ch.length) return null;
      var c = { done: 0, partial: 0, untouched: 0, unassessed: 0 }, n = 0;
      ch.forEach(function (k) { var kc = counts(k.states); STATES.forEach(function (s) { c[s] += kc[s]; }); n += k.layers.length; });
      return { c: c, n: n, subs: ch.length };
    }
    function due(r) { return r.status && r.activity && r.activity.since_snapshot >= data.update_due_prs; }
    function snapshotAge(r) { return r.status && r.status.ts ? daysBetween(r.status.ts, today) : null; }
    function lastAge(r) { return r.activity && r.activity.last ? daysBetween(r.activity.last, today) : null; }

    // ---- bars ----
    var sparkMax = 1;
    rows.forEach(function (r) { if (r.activity) r.activity.weekly.forEach(function (v) { if (v > sparkMax) sparkMax = v; }); });
    function bars(values, w, h, scale, label) {
      var n = values.length, gap = 2, bw = (w - gap * (n - 1)) / n;
      var s = '<svg class="pb-bars" viewBox="0 0 ' + w + " " + h + '" preserveAspectRatio="none" role="img" aria-label="' + esc(label) + '">';
      s += '<line x1="0" y1="' + (h - 0.5) + '" x2="' + w + '" y2="' + (h - 0.5) + '" class="pb-baseline"/>';
      values.forEach(function (v, i) {
        var bh = v === 0 ? 0 : Math.max(1.5, scale(v) * (h - 3));
        var x = i * (bw + gap);
        s += '<rect x="' + x.toFixed(2) + '" y="' + (h - 1 - bh).toFixed(2) + '" width="' + bw.toFixed(2) + '" height="' + bh.toFixed(2) + '" rx="1" class="' + (i === n - 1 ? "pb-bar-now" : "pb-bar") + '"><title>week of ' + data.weeks[i] + ": " + v + " merged</title></rect>";
      });
      return s + "</svg>";
    }

    // ---- tiles ----
    function tiles() {
      var active = tops.filter(function (r) { return !r.completed; }).length;
      var completed = tops.filter(function (r) { return r.completed; }).length;
      var subs = rows.length - tops.length;
      var tot = { done: 0, partial: 0, untouched: 0, unassessed: 0 };
      rows.forEach(function (r) { if (kids(r.name).length || !assessed(r)) return; var c = counts(r.states); STATES.forEach(function (s) { tot[s] += c[s]; }); });
      var layerTotal = tot.done + tot.partial + tot.untouched + tot.unassessed;
      var last30 = rows.reduce(function (a, r) { return a + (r.activity ? r.activity.last30 : 0); }, 0);
      var snaps = tops.filter(function (r) { return r.status; });
      var ages = snaps.map(snapshotAge).sort(function (a, b) { return a - b; });
      var median = ages.length ? ages[Math.floor(ages.length / 2)] : null;
      var behind = tops.filter(due).length;
      var allMax = Math.max.apply(null, data.all_weekly.concat([1]));
      return '<div class="pb-tiles">' +
        '<div class="pb-tile"><div class="pb-label">Roadmaps</div><div class="pb-big">' + active + "<small>active</small></div>" +
          '<div class="pb-sub"><b>' + completed + "</b> completed · <b>" + subs + "</b> sub-roadmaps · " + rows.length + " rows</div></div>" +
        '<div class="pb-tile"><div class="pb-label">Layers, assessed roadmaps</div><div class="pb-big">' + tot.done + "<small>of " + layerTotal + " done</small></div>" +
          '<div class="pb-stack">' + STATES.map(function (s) { return '<span class="' + STATE_CLASS[s] + '" style="flex:' + tot[s] + '" title="' + s + ": " + tot[s] + '"></span>'; }).join("") + "</div>" +
          '<div class="pb-legend">' + STATES.map(function (s) { return '<span><span class="pb-sw ' + STATE_CLASS[s] + '"></span><b>' + tot[s] + "</b> " + s + "</span>"; }).join("") + "</div></div>" +
        '<div class="pb-tile"><div class="pb-label">Merged pull requests</div><div class="pb-big">' + last30 + "<small>in the last 30 days</small></div>" +
          bars(data.all_weekly, 200, 34, function (v) { return v / allMax; }, "All merged pull requests per week") +
          '<div class="pb-sub"><b>' + data.merged_total + "</b> merged since " + esc(data.first_merge) + "</div></div>" +
        '<div class="pb-tile"><div class="pb-label">Status snapshots</div><div class="pb-big">' + snaps.length + "<small>of " + tops.length + " roadmaps</small></div>" +
          '<div class="pb-sub">median age <b>' + median + "</b> days · oldest <b>" + ages[ages.length - 1] + "</b> days · <b>" + behind + "</b> with " + data.update_due_prs + "+ PRs merged since, so an update is due</div></div>" +
        "</div>";
    }

    // ---- rows ----
    function strip(r) {
      var ag = aggregate(r);
      if (ag) {
        return '<div class="pb-stack pb-stack-row" title="All layers of the ' + ag.subs + " sub-roadmaps: " + ag.c.done + " done, " + ag.c.partial + " partial, " + ag.c.untouched + " untouched, " + ag.c.unassessed + ' unassessed">' +
          STATES.map(function (s) { return '<span class="' + STATE_CLASS[s] + '" style="flex:' + ag.c[s] + '"></span>'; }).join("") + "</div>";
      }
      if (!r.layers.length) return '<div class="pb-covtext"><span class="pb-none">no layer headings in the README</span></div>';
      return '<div class="pb-strip">' + r.layers.map(function (l, i) {
        return '<span class="' + STATE_CLASS[r.states[i]] + '" title="' + esc(l) + " — " + r.states[i] + '"></span>';
      }).join("") + "</div>";
    }
    function covText(r) {
      var ag = aggregate(r);
      if (ag) {
        return '<div class="pb-covtext"><b>' + ag.c.done + "</b> done · <b>" + ag.c.partial + "</b> partial · " + ag.c.untouched + " untouched · " + ag.c.unassessed + " unassessed<br><span class=\"pb-faint\">of " + ag.n + " layers across " + ag.subs + " sub-roadmaps</span></div>";
      }
      if (!assessed(r)) return '<div class="pb-covtext"><span class="pb-none">' + (r.status ? "snapshot not yet read" : "no snapshot yet") + "</span><br><span class=\"pb-faint\">" + r.layers.length + " layers</span></div>";
      var c = counts(r.states), parts = [];
      if (c.done) parts.push("<b>" + c.done + "</b> done");
      if (c.partial) parts.push("<b>" + c.partial + "</b> partial");
      if (c.untouched) parts.push(c.untouched + " untouched");
      if (c.unassessed) parts.push(c.unassessed + " unassessed");
      return '<div class="pb-covtext">' + parts.join(" · ") + '<br><span class="pb-faint">of ' + r.layers.length + " layers</span></div>";
    }
    function rowSpark(r) {
      if (!r.activity) return '<div class="pb-covtext"><span class="pb-none">' + (r.parent ? "shares the parent label" : "no labelled pull requests") + "</span></div>";
      return bars(r.activity.weekly, 128, 28, function (v) { return Math.sqrt(v / sparkMax); }, "Merged pull requests per week");
    }
    function rowHtml(r) {
      var chips = "";
      if (r.completed) chips += '<span class="pb-chip complete">completed</span>';
      if (due(r)) chips += '<span class="pb-chip behind" title="' + r.activity.since_snapshot + ' pull requests merged since the snapshot">update due</span>';
      var last = r.activity && r.activity.last
        ? '<div class="pb-num">' + ago(lastAge(r)) + '<span class="pb-sub">' + r.activity.total + " merged</span></div>"
        : '<div class="pb-num"><span class="pb-sub">' + (r.parent ? "" : "—") + "</span></div>";
      var snap;
      if (r.status && !r.status_inherited) snap = '<div class="pb-age' + (due(r) ? " stale" : "") + '">' + snapshotAge(r) + ' d<span class="pb-sub"><span class="pb-sha">' + esc(r.status.to_sha.slice(0, 7)) + "</span> · " + esc(r.status.ts.slice(5, 10)) + "</span>" + (r.activity && r.activity.since_snapshot !== null ? '<span class="pb-sub">' + r.activity.since_snapshot + " PRs since</span>" : "") + "</div>";
      else if (r.status) snap = '<div class="pb-age"><span class="pb-sub">via parent</span></div>';
      else if (r.completed) snap = '<div class="pb-age"><span class="pb-sub">archived</span></div>';
      else snap = '<div class="pb-age"><span class="pb-none">none</span></div>';
      return '<div class="pb-row' + (r.parent ? " child" : "") + '" data-name="' + esc(r.name) + '" tabindex="0" role="button" aria-expanded="false">' +
        '<div><div class="pb-name"><a href="' + GH_ROADMAP + dirOf(r) + 'README.md">' + esc(r.name) + "</a>" + chips + '</div><div class="pb-title">' + esc(r.title) + "</div></div>" +
        "<div>" + strip(r) + "</div>" + covText(r) + "<div>" + rowSpark(r) + "</div>" + last + snap +
        '</div><div class="pb-detail" hidden data-detail="' + esc(r.name) + '"></div>';
    }
    function detailHtml(r) {
      var dir = dirOf(r), left = "", right = "";
      if (r.status) {
        left += "<h4>At a glance" + (r.status_inherited ? " (from the parent roadmap's snapshot)" : "") + "</h4><p>" + esc(r.status.glance || "") + "</p>";
        if (r.status.frontier.length && !r.status_inherited) left += "<h4>Frontier</h4><ul>" + r.status.frontier.map(function (f) { return "<li>" + esc(f) + "</li>"; }).join("") + "</ul>";
      } else if (r.completed) {
        left += "<h4>Completed</h4><p>Declared complete by the maintainers against its README; its targets are discharged in place, so completion is checked by Lean.</p>";
      } else {
        left += "<h4>No snapshot</h4><p>TauCetiProgress has not written a STATUS.md for this roadmap yet.</p>";
      }
      left += '<div class="pb-links"><a href="' + GH_ROADMAP + dir + 'README.md">README</a>' +
        (r.status && !r.status_inherited ? '<a href="' + GH_ROADMAP + dir + 'STATUS.md">STATUS</a><a href="' + GH_ROADMAP + dir + 'PROGRESS.md">PROGRESS</a>' : "") +
        (r.parent ? "" : '<a href="' + GH_PRS + esc(r.name) + '">merged pull requests</a>') + "</div>";
      var source = { marker: "the coverage marker in STATUS.md", "hand-read": "a hand reading of the STATUS.md prose, retired when the snapshot moves", completed: "the roadmap's completion" }[r.states_source];
      left += '<div class="pb-evid">Topic: ' + esc(r.topic) + " (a hand assignment). Layer states come from " + (source || "nowhere yet: unassessed") + "; pull-request counts from labels; " + (r.completed ? "completion is Lean-checked." : "nothing here is Lean-checked.") + "</div>";
      if (r.layers.length) {
        right = '<h4>Layers</h4><ul class="pb-layers">' + r.layers.map(function (l, i) {
          return '<li><span class="pb-dot ' + STATE_CLASS[r.states[i]] + '"></span><span>' + esc(l) + ' <span class="pb-faint">· ' + r.states[i] + "</span></span></li>";
        }).join("") + "</ul>";
      }
      return "<div>" + left + "</div><div>" + right + "</div>";
    }

    // ---- sort / filter ----
    var sortKey = "activity", filterKey = "all", query = "";
    try {
      var q = new URLSearchParams(location.search);
      if (["activity", "coverage", "due", "topic", "name"].indexOf(q.get("sort")) >= 0) sortKey = q.get("sort");
      if (["all", "assessed", "unassessed", "completed"].indexOf(q.get("show")) >= 0) filterKey = q.get("show");
    } catch (e) { /* no query string */ }
    function covScore(r) { var ag = aggregate(r), c = ag ? ag.c : counts(r.states), n = (ag ? ag.n : r.layers.length) || 1; return (c.done + 0.5 * c.partial) / n; }
    function act(r, k) { return r.activity ? r.activity[k] : -1; }
    var sorters = {
      activity: function (a, b) { return (act(b, "last30") - act(a, "last30")) || (act(b, "total") - act(a, "total")) || a.name.localeCompare(b.name); },
      coverage: function (a, b) { return (covScore(b) - covScore(a)) || a.name.localeCompare(b.name); },
      due: function (a, b) { function s(r) { return r.activity && r.status ? r.activity.since_snapshot : -1; } return (s(b) - s(a)) || a.name.localeCompare(b.name); },
      name: function (a, b) { return a.name.localeCompare(b.name); }
    };
    function visible(r) {
      if (query && (r.name + " " + r.title).toLowerCase().indexOf(query) < 0) return false;
      if (filterKey === "assessed") return !!r.status && !r.status_inherited;
      if (filterKey === "unassessed") return !r.status && !r.completed;
      if (filterKey === "completed") return r.completed;
      return true;
    }
    function topicHeader(t, members) {
      var c = { done: 0, partial: 0, untouched: 0, unassessed: 0 }, n = 0, last30 = 0;
      members.forEach(function (r) { var ag = aggregate(r), cc = ag ? ag.c : counts(r.states); STATES.forEach(function (s) { c[s] += cc[s]; }); n += ag ? ag.n : r.layers.length; last30 += r.activity ? r.activity.last30 : 0; });
      return '<div class="pb-topic"><div class="pb-tname">' + esc(t) + '</div><div class="pb-tstat">' + members.length + " roadmaps · " + n + " layers: <b>" + c.done + "</b> done, <b>" + c.partial + "</b> partial, " + c.untouched + " untouched, " + c.unassessed + " unassessed · <b>" + last30 + "</b> PRs merged in 30 days</div></div>";
    }
    function renderRows() {
      var s = sorters[sortKey === "topic" ? "activity" : sortKey];
      var order = tops.slice().sort(s), out = [], n = 0;
      function emit(r) {
        var ch = kids(r.name).filter(visible).sort(sortKey === "coverage" ? s : sorters.name);
        if (!visible(r) && !ch.length) return;
        out.push(rowHtml(r)); n++;
        ch.forEach(function (c) { out.push(rowHtml(c)); n++; });
      }
      if (sortKey === "topic") {
        data.topics.concat(["Unsorted"]).forEach(function (t) {
          var members = order.filter(function (r) { return r.topic === t && (visible(r) || kids(r.name).some(visible)); });
          if (!members.length) return;
          out.push(topicHeader(t, members));
          members.forEach(emit);
        });
      } else {
        order.forEach(emit);
      }
      root.querySelector(".pb-rows").innerHTML = out.join("");
      root.querySelector(".pb-count").textContent = n + " rows";
      root.querySelectorAll("[data-sort]").forEach(function (b) { b.setAttribute("aria-pressed", b.getAttribute("data-sort") === sortKey ? "true" : "false"); });
      root.querySelectorAll("[data-filter]").forEach(function (b) { b.setAttribute("aria-pressed", b.getAttribute("data-filter") === filterKey ? "true" : "false"); });
    }

    // ---- assemble ----
    var head = data.roadmap_head ? "TauCetiRoadmap@" + esc(data.roadmap_head) : "TauCetiRoadmap";
    root.innerHTML =
      '<p class="pb-lede">Built from <code>' + head + "</code> and the pull requests merged by " + esc(today) + ". Click a row for its snapshot, frontier and layers.</p>" +
      tiles() +
      '<div class="pb-controls" aria-label="Sort and filter">' +
        '<div class="pb-group"><span>Sort</span>' +
          '<button type="button" data-sort="activity">Activity</button><button type="button" data-sort="coverage">Coverage</button>' +
          '<button type="button" data-sort="due">Update due</button><button type="button" data-sort="topic">Topic</button><button type="button" data-sort="name">Name</button></div>' +
        '<div class="pb-group"><span>Show</span>' +
          '<button type="button" data-filter="all">All</button><button type="button" data-filter="assessed">With snapshot</button>' +
          '<button type="button" data-filter="unassessed">No snapshot</button><button type="button" data-filter="completed">Completed</button></div>' +
        '<div class="pb-group"><input type="search" class="pb-search" placeholder="Find a roadmap" aria-label="Find a roadmap"></div>' +
        '<div class="pb-count"></div></div>' +
      '<div class="pb-board"><div class="pb-scroll"><div class="pb-grid">' +
        '<div class="pb-hdr"><div>Roadmap</div><div>Layers <span class="pb-ev">from STATUS.md · model-judged</span></div><div>Coverage</div>' +
        '<div>Merged PRs, 16 weeks <span class="pb-ev">from labels · mechanical</span></div><div>Last merged</div><div>Snapshot</div></div>' +
        '<div class="pb-rows"></div></div></div></div>' +
      '<div class="pb-legend pb-legend-main">' +
        '<span><span class="pb-sw d"></span>done: the layer’s milestones are proved</span>' +
        '<span><span class="pb-sw p"></span>partial: some milestones proved</span>' +
        '<span><span class="pb-sw u"></span>untouched</span>' +
        '<span><span class="pb-sw q"></span>unassessed: the snapshot does not say, or there is no snapshot</span></div>';
    renderRows();

    root.querySelector(".pb-controls").addEventListener("click", function (e) {
      var b = e.target.closest("button");
      if (!b) return;
      if (b.hasAttribute("data-sort")) sortKey = b.getAttribute("data-sort");
      else if (b.hasAttribute("data-filter")) filterKey = b.getAttribute("data-filter");
      renderRows();
    });
    root.querySelector(".pb-search").addEventListener("input", function (e) { query = e.target.value.trim().toLowerCase(); renderRows(); });
    var rowsEl = root.querySelector(".pb-rows");
    function toggle(rowEl) {
      var name = rowEl.getAttribute("data-name");
      var d = rowsEl.querySelector('[data-detail="' + (window.CSS && CSS.escape ? CSS.escape(name) : name) + '"]');
      if (!d) return;
      if (!d.hidden) { d.hidden = true; rowEl.setAttribute("aria-expanded", "false"); return; }
      d.innerHTML = detailHtml(rows.filter(function (r) { return r.name === name; })[0]);
      d.hidden = false; rowEl.setAttribute("aria-expanded", "true");
    }
    rowsEl.addEventListener("click", function (e) {
      if (e.target.closest("a")) return;
      var row = e.target.closest(".pb-row");
      if (row) toggle(row);
    });
    rowsEl.addEventListener("keydown", function (e) {
      if ((e.key === "Enter" || e.key === " ") && e.target.classList.contains("pb-row")) { e.preventDefault(); toggle(e.target); }
    });
  }

  fetch("static/progress.json", { cache: "no-cache" })
    .then(function (r) { if (!r.ok) throw new Error(r.status + " " + r.statusText); return r.json(); })
    .then(render)
    .catch(function (err) {
      root.innerHTML = '<p class="pb-error">The progress data could not be loaded (' + esc(err.message) + "). The roadmaps themselves are at " +
        '<a href="https://github.com/TauCetiProject/TauCetiRoadmap">TauCetiRoadmap</a>.</p>';
    });
})();
