import VersoBlog
open Verso Genre Blog
open Verso.Output Verso.Output.Html

/-- The roadmap board. It is rendered in the browser by `static/progress.js` from
`static/progress.json`, which the `pages` workflow regenerates at each deploy with
`scripts/roadmap_progress.py` (the committed JSON is a fallback snapshot, like the chart
SVGs), so this page never needs touching as roadmaps come and go. Embedded as a raw HTML
blob: a container the script fills, a `noscript` alternative, and the script itself. -/
def progressBoard : Html := {{
  <div class="progress-page">
    <div id="progress-board">
      <p class="pb-lede">"Loading the roadmap board…"</p>
      <noscript>
        <p>"This board needs JavaScript. Without it, the same information is in each roadmap's "
           <code>"STATUS.md"</code> " in the "
           <a href="https://github.com/TauCetiProject/TauCetiRoadmap">"TauCetiRoadmap repository"</a>
           ", and the board's data is published as "
           <a href="static/progress.json">"progress.json"</a> "."</p>
      </noscript>
    </div>
    <script src="static/progress.js" defer="defer"></script>
  </div>
}}

/-- The methodology, as a disclosure below the board rather than an essay above it. Raw HTML
because Verso's Markdown has no collapsible block; the prose is the same kind of thing the
Statistics page says inline. -/
def howToRead : Html := {{
  <details class="pb-methods progress-page">
    <summary>"How to read this board"</summary>
    <p>"The " <a href="statistics">"Statistics"</a> " page measures volume: lines of Lean per roadmap, pull requests merged, reviews written. This page measures something else, how far each roadmap has got against its own specification, and it describes coverage of the roadmaps that exist, not how much of mathematics has been formalized."</p>
    <p>"Three kinds of evidence go into the board, and they are kept apart:"</p>
    <ul>
      <li><em>"Layers"</em> " are the headings of the human-written roadmap " <code>"README.md"</code> ": layers, lanes, parts or stages. They do not move when code lands. Nothing here turns them into a percentage, because layers differ in size and a partial layer is not known to be half done. “Layers reported done” is a count of headings. A roadmap whose README names its milestones some other way has no layer inventory here, which says nothing about its work."</li>
      <li><em>"Layer states"</em> " are read from the roadmap's generated " <code>"STATUS.md"</code> ", the report that " <a href="https://github.com/TauCetiProject/TauCetiProgress">"TauCetiProgress"</a> " writes after each window of merged pull requests. “Reported done” means that report, describing the library at the commit named in its header, says the layer's milestones are proved. It is a model's account of the work, not security-validated, and not a certificate that every sentence of the layer's specification is met. Where a report says nothing about a layer, the layer is unassessed; so is every layer of a roadmap with no report yet."</li>
      <li><em>"Activity"</em> " is mechanical: pull requests merged under the roadmap's " <code>"roadmap/<Area>"</code> " label, the same attribution the Statistics page uses, counted up to the stated cutoff. A pull request with no roadmap label, or more than one, is counted in the global figures but assigned to no roadmap."</li>
    </ul>
    <p>"The formal declarations behind all of this are checked by Lean in the usual way; the board adds no checking of its own. A roadmap marked " <em>"declared complete"</em> " is one the maintainers have " <a href="https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/Completed/README.md">"archived"</a> " as complete against its README. That is a human judgment, shown beside the report's layer assessment rather than replacing it, and the two can disagree."</p>
    <p>"A report always lags the library, because it describes the last published documentation build, so its age alone is not a signal. The board marks a roadmap as due an update once ten or more pull requests have merged since its report, the threshold TauCetiProgress itself uses to open a new window; that is a heuristic, not a guarantee that nothing relevant changed below it. The umbrella roadmap for representation theory is reported as one unit, so its sub-roadmaps share its report and its label."</p>
    <p>"The topic grouping is a hand assignment kept beside the generator. So, for now, are the layer states: TauCetiProgress does not yet write them in a machine-readable form, so the generator reads a companion file transcribed from each report's prose, bound to the exact report and the exact README it was read against. When either changes, the transcription is retired and the layers go back to unassessed until it is read again. The intended replacement is a " <code>"tauceti-coverage:v1"</code> " marker beside the report's header, naming the roadmap, the library commit, the README it assessed (a hash), and one line per layer with its state and a one-line note of what remains, validated by the same script that validates the rest of a generated report. That is what this page will accept, offered as a proposal rather than an agreed format; the generator prefers such a marker whenever one is present and fits, and leaves a marker that does not name its README unassessed rather than applying it to whatever README is current. Open pull requests carrying a roadmap's label are counted beside its merged ones, as work in flight that no report describes yet, and where someone has published a map or write-up of a single roadmap, its row links to it."</p>
  </details>
}}

#doc (Page) "Progress" =>

Progress against Tau Ceti's existing roadmaps. Each segment is one layer of a roadmap, as its
own `README.md` names them; its appearance shows what the latest report says about that layer,
not a percentage of the work. Expand a roadmap for its report, its next milestones and its
sources. Merged pull requests are shown separately, as activity.

:::blob progressBoard
:::

:::blob howToRead
:::
