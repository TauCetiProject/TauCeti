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
