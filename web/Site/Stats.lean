import VersoBlog
open Verso Genre Blog
open Verso.Output Verso.Output.Html

/-- The two "lines of code by date" charts. The SVGs are regenerated weekly into
`static_files/` by the `loc-graph` workflow, so this page never needs touching as
the project grows. They are embedded as a raw HTML blob: each `<img>` simply points
at the static asset. -/
def locGraphs : Html := {{
  <div class="loc-graphs">
    <figure class="loc-figure">
      <img class="loc-graph" src="static/loc-tauceti.svg"
           alt="Tau Ceti: lines of Lean by date"/>
      <figcaption>"The Lean library under " <code>"TauCeti/"</code> ", total lines by date."</figcaption>
    </figure>
    <figure class="loc-figure">
      <img class="loc-graph" src="static/loc-roadmap.svg"
           alt="Tau Ceti Roadmap: lines written by date"/>
      <figcaption>"The human-owned roadmap repository, total lines by date."</figcaption>
    </figure>
  </div>
}}

#doc (Page) "Statistics" =>

How much mathematics has Tau Ceti formalized, and how fast is the roadmap that
directs it growing? Each chart plots the total number of lines present at every
commit, counted straight from the git history and rebuilt from scratch each week,
so the figures cannot drift.

:::blob locGraphs
:::

The vertical scales differ by an order of magnitude and on purpose: the library is
measured in tens of thousands of lines of Lean, the roadmap in thousands of lines of
prose and target statements. The library figure counts only the mathematics — the
files under `TauCeti/` — not the website or tooling.
