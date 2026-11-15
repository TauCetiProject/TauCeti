// The exact values travel inside each SVG, including when a deploy keeps a cached
// chart. Fetch only data; leave the image and its isolated styles in place.
(function () {
  "use strict";
  var serial = 0;
  document.querySelectorAll("img.chart-hover").forEach(async function (img) {
    try {
      var response = await fetch(img.currentSrc || img.src);
      if (!response.ok) return;
      var svg = new DOMParser().parseFromString(await response.text(), "image/svg+xml");
      var metadata = svg.querySelector("metadata#chart-hover");
      if (!metadata) return; // Older fallback snapshots still display normally.
      var plots = JSON.parse(metadata.textContent);
      var viewBox = svg.documentElement.getAttribute("viewBox").trim().split(/\s+/).map(Number);
      if (!plots.length || viewBox.length !== 4 || !viewBox.every(Number.isFinite)) return;

      var wrapper = document.createElement("div");
      wrapper.className = "chart-hover-wrap";
      img.before(wrapper);
      wrapper.append(img);
      var guide = document.createElement("div");
      guide.className = "chart-hover-guide";
      guide.hidden = true;
      guide.setAttribute("aria-hidden", "true");
      wrapper.append(guide);
      var tooltip = document.createElement("div");
      tooltip.className = "chart-tooltip";
      tooltip.id = "chart-tooltip-" + (++serial);
      tooltip.setAttribute("role", "tooltip");
      tooltip.setAttribute("aria-live", "polite");
      tooltip.hidden = true;
      document.body.append(tooltip);
      img.tabIndex = 0;
      img.setAttribute("aria-describedby", tooltip.id);
      img.setAttribute("aria-keyshortcuts", "ArrowLeft ArrowRight ArrowUp ArrowDown Home End Escape");
      img.setAttribute("aria-description", "Hover or tap for values. Use arrow keys to explore dates and panels; Escape to close.");
      var plotIndex = 0, pointIndex = -1;

      function hide() {
        tooltip.hidden = true;
        guide.hidden = true;
      }
      function show(panel, index, clientX, clientY) {
        var plot = plots[panel];
        if (plotIndex !== panel || pointIndex !== index || tooltip.hidden) {
          tooltip.replaceChildren();
          var date = document.createElement("strong");
          date.textContent = plot.labels[index] + " (UTC)";
          tooltip.append(date);
          var table = document.createElement("table");
          plot.series.forEach(function (series) {
            var row = table.insertRow();
            var name = document.createElement("th");
            name.scope = "row";
            name.textContent = series.label;
            row.append(name);
            var value = series.values[index];
            var text = "Not available";
            if (value !== null && Number.isFinite(value)) {
              text = new Intl.NumberFormat("en-US", {
                maximumFractionDigits: series.digits || 0,
                signDisplay: series.signed ? "exceptZero" : "auto"
              }).format(value) + (series.unit ? " " + series.unit : "");
            }
            row.insertCell().textContent = text;
          });
          tooltip.append(table);
          if (plot.note) {
            var note = document.createElement("small");
            note.textContent = plot.note;
            tooltip.append(note);
          }
        }
        plotIndex = panel;
        pointIndex = index;
        tooltip.hidden = false;
        var bounds = plot.bounds;
        guide.style.left = ((plot.x[index] - viewBox[0]) / viewBox[2] * 100) + "%";
        guide.style.top = ((bounds[1] - viewBox[1]) / viewBox[3] * 100) + "%";
        guide.style.height = (bounds[3] / viewBox[3] * 100) + "%";
        guide.hidden = false;
        var box = tooltip.getBoundingClientRect();
        var x = clientX + 16;
        if (x + box.width > window.innerWidth - 8) x = clientX - box.width - 16;
        tooltip.style.left = Math.max(8, Math.min(x, window.innerWidth - box.width - 8)) + "px";
        tooltip.style.top = Math.max(8, Math.min(clientY + 16, window.innerHeight - box.height - 8)) + "px";
      }
      function pointer(event) {
        var rect = img.getBoundingClientRect();
        var x = viewBox[0] + (event.clientX - rect.left) / rect.width * viewBox[2];
        var y = viewBox[1] + (event.clientY - rect.top) / rect.height * viewBox[3];
        var panel = plots.findIndex(function (plot) {
          var b = plot.bounds;
          return x >= b[0] && x <= b[0] + b[2] && y >= b[1] && y <= b[1] + b[3];
        });
        if (panel < 0) { hide(); return; }
        var xs = plots[panel].x;
        var nearest = 0;
        for (var i = 1; i < xs.length; i++) {
          if (Math.abs(xs[i] - x) < Math.abs(xs[nearest] - x)) nearest = i;
        }
        show(panel, nearest, event.clientX, event.clientY);
      }
      function keyboardPoint() {
        var plot = plots[plotIndex];
        var rect = img.getBoundingClientRect();
        show(plotIndex, pointIndex,
          rect.left + (plot.x[pointIndex] - viewBox[0]) / viewBox[2] * rect.width,
          rect.top + (plot.bounds[1] - viewBox[1]) / viewBox[3] * rect.height);
      }
      img.addEventListener("pointermove", pointer);
      img.addEventListener("pointerdown", pointer);
      img.addEventListener("pointerleave", function (event) { if (event.pointerType !== "touch") hide(); });
      img.addEventListener("focus", function () {
        if (!tooltip.hidden) return; // A pointer tap has already selected its date.
        pointIndex = plots[plotIndex].x.length - 1;
        keyboardPoint();
      });
      img.addEventListener("blur", hide);
      img.addEventListener("keydown", function (event) {
        if (event.key === "Escape") { hide(); return; }
        if (!["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Home", "End"].includes(event.key)) return;
        event.preventDefault();
        if (event.key === "ArrowUp") plotIndex = Math.max(0, plotIndex - 1);
        if (event.key === "ArrowDown") plotIndex = Math.min(plots.length - 1, plotIndex + 1);
        var last = plots[plotIndex].x.length - 1;
        if (event.key === "ArrowLeft") pointIndex--;
        if (event.key === "ArrowRight") pointIndex++;
        if (event.key === "Home") pointIndex = 0;
        if (event.key === "End") pointIndex = last;
        pointIndex = Math.max(0, Math.min(last, pointIndex));
        // Force rebuilding after changing panels, even when the index is unchanged.
        tooltip.hidden = true;
        keyboardPoint();
      });
      document.addEventListener("pointerdown", function (event) {
        if (event.target !== img && !tooltip.contains(event.target)) hide();
      });
      window.addEventListener("scroll", hide, {passive: true});
      window.addEventListener("resize", hide);
    } catch (_) {
      // A missing/stale asset or disabled fetch should leave a useful static chart.
    }
  });
})();
