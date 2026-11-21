// Wire the horizontal "taste of the maths" carousels: arrows scroll one card.
document.querySelectorAll(".carousel").forEach(function (carousel) {
  var track = carousel.querySelector(".carousel-track");
  if (!track) return;
  function step() { return Math.min(track.clientWidth * 0.85, 720); }
  var prev = carousel.querySelector(".carousel-arrow.prev");
  var next = carousel.querySelector(".carousel-arrow.next");
  if (prev) prev.addEventListener("click", function () {
    track.scrollBy({ left: -step(), behavior: "smooth" });
  });
  if (next) next.addEventListener("click", function () {
    track.scrollBy({ left: step(), behavior: "smooth" });
  });
});

// Copy buttons: copy the text of the element named by data-copy-target, such as the
// front page's prompt for an AI agent. Where the clipboard is unavailable, select the
// text so that the reader can copy it by hand.
document.querySelectorAll(".copy-btn").forEach(function (button) {
  var target = document.getElementById(button.getAttribute("data-copy-target"));
  if (!target) return;
  var label = button.textContent;
  function show(text) {
    button.textContent = text;
    setTimeout(function () { button.textContent = label; }, 2000);
  }
  function select() {
    var range = document.createRange();
    range.selectNodeContents(target);
    var selection = window.getSelection();
    selection.removeAllRanges();
    selection.addRange(range);
    show("Press Ctrl+C");
  }
  button.addEventListener("click", function () {
    var text = target.innerText.trim();
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(function () { show("Copied"); }, select);
    } else {
      select();
    }
  });
});

// Fit the same-origin forecast document to its text; CSS supplies a no-JavaScript fallback.
document.querySelectorAll("iframe.roadmap-exhaustion").forEach(function (frame) {
  var observer;
  function fit() {
    var doc = frame.contentDocument;
    var section = doc && doc.querySelector("section");
    if (!section) return;
    section.style.minHeight = "0";
    frame.style.height = Math.ceil(section.getBoundingClientRect().height) + "px";
  }
  function loaded() {
    if (observer) observer.disconnect();
    var doc = frame.contentDocument;
    var section = doc && doc.querySelector("section");
    if (!section) return;
    fit();
    if (window.ResizeObserver) {
      observer = new ResizeObserver(fit);
      observer.observe(section);
    }
  }
  frame.addEventListener("load", loaded);
  window.addEventListener("resize", fit);
  if (frame.contentDocument && frame.contentDocument.readyState === "complete") loaded();
});
