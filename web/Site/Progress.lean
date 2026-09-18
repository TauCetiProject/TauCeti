import VersoBlog
open Verso Genre Blog
open Verso.Output Verso.Output.Html

/-- The roadmap board. It is rendered in the browser by `static/progress.js` from
`static/progress.json`, which the `pages` workflow regenerates at each deploy with
`scripts/roadmap_progress.py` (the committed JSON is a fallback snapshot, like the chart
SVGs), so this page never needs touching as roadmaps come and go. Embedded as a raw HTML
blob: a container the script fills, and the script itself. -/
def progressBoard : Html := {{
  <div class="progress-page">
    <div id="progress-board">
      <p class="pb-lede">"Loading the roadmap board…"</p>
    </div>
    <script src="static/progress.js" defer="defer"></script>
  </div>
}}

#doc (Page) "Progress" =>

How far along is each roadmap? The [Statistics](statistics) page measures volume: lines of
Lean per roadmap, pull requests merged, reviews written. This page measures distance to the
specification instead. Each roadmap's own `README.md` names the layers (or lanes, parts,
stages) it asks for, and each segment of a strip below is one of those layers, filled by how
much of it Tau Ceti now has: solid when the layer's milestones are proved, faint when some
are, outlined when nothing has landed, hatched when nobody has assessed it. Beside the strip
are the pull requests merged under that roadmap's label, week by week.

:::blob progressBoard
:::

Three kinds of evidence go into the board, and the columns say which is which. The layers
themselves come from the human-written roadmaps and do not move when code lands. The state
of each layer is a judgment about the library, read from the roadmap's generated `STATUS.md`
snapshot, which [TauCetiProgress](https://github.com/TauCetiProject/TauCetiProgress) writes
after each window of merged pull requests; those snapshots are a model's account of the work,
not security-validated and not checked by Lean, and the board carries exactly the same
verdicts the prose does. The pull-request counts are mechanical, from the same
`roadmap/<Area>` labels the per-roadmap chart on the Statistics page uses. The one state that
is checked by Lean is "completed": a roadmap the maintainers have archived under
`Completed/`, whose target signatures are discharged in place by the library's own
declarations.

A snapshot is always somewhat behind the library, because it describes the last published
documentation build rather than the tip, so its age alone is not a signal. The board marks a
roadmap as due an update once ten or more pull requests have merged since its snapshot, the
same threshold TauCetiProgress itself uses to open a new reporting window. Roadmaps with no
snapshot yet show their layers hatched; the umbrella roadmap for representation theory is
reported as one unit, so its sub-roadmaps share its snapshot and its label.

The topic grouping is a hand assignment kept beside the generator, and so are, for now, the
per-layer states: TauCetiProgress does not yet write them in a machine-readable form, so the
generator reads a companion file of states transcribed from each snapshot's prose, keyed to
the exact commit that snapshot describes. A newer snapshot retires the transcription and the
layers go back to hatched until it is read again. The intended replacement is a
`tauceti-coverage:v1` marker beside the status header, one line per layer, validated by the
same script that validates the rest of a generated report; the generator already prefers it
whenever one is present.
