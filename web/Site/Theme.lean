import VersoBlog
open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html lang="en">
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="color-scheme" content="dark"/>
          <link rel="icon" href="static/favicon.ico" sizes="any"/>
          <link rel="icon" type="image/png" sizes="32x32" href="static/favicon-32x32.png"/>
          <link rel="icon" type="image/png" sizes="16x16" href="static/favicon-16x16.png"/>
          <link rel="apple-touch-icon" sizes="180x180" href="static/apple-touch-icon.png"/>
          <link rel="preconnect" href="https://fonts.googleapis.com"/>
          <link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Chakra+Petch:wght@400;500;600;700&display=swap"/>
          <title>{{ (← param (α := String) "title") }} " — Tau Ceti"</title>
          {{← builtinHeader }}
          <link rel="stylesheet" href="static/style.css"/>
          <script src="static/site.js" defer="defer"></script>
        </head>
        <body>
          <header class="site-nav">
            <div class="nav-inner">
              <a class="brand" href="."><img src="static/header.png" alt="Tau Ceti"/></a>
              <nav class="nav-links">
                <a href=".">"Home"</a>
                <a href="statistics">"Statistics"</a>
                <a href="progress">"Progress"</a>
                <a href="ci">"CI"</a>
                <a href="about">"About"</a>
                <a href="https://github.com/TauCetiProject/TauCeti">"GitHub"</a>
              </nav>
            </div>
          </header>
          <main>
            {{ (← param "content") }}
          </main>
          <footer class="site-footer">
            <div class="foot-inner">
              <p class="foot-tag">"Let’s do lots of maths."</p>
              <ul class="foot-links">
                <li><a href="https://github.com/TauCetiProject/TauCeti">"TauCeti"</a></li>
                <li><a href="https://github.com/TauCetiProject/TauCetiRoadmap">"TauCetiRoadmap"</a></li>
                <li><a href="https://github.com/TauCetiProject/TauCetiReview">"TauCetiReview"</a></li>
              </ul>
              <p class="foot-legal">"AI-authored Lean mathematics · Apache-2.0"</p>
            </div>
          </footer>
        </body>
      </html>
    }}
  }
  |>.override #[] ⟨do
    return {{
      <div class="frontpage">
        <section class="hero">
          <img class="hero-img" src="static/tauceti-collaboration.jpg"
               alt="A hexapus reaching toward an AI across a tide pool, beneath twin suns and a ringed planet."/>
          <div class="hero-copy">
            <h1 class="hero-title">"Tau Ceti"</h1>
            <p class="hero-tag">"Let’s do lots of maths."</p>
            <p class="hero-sub">"AI-authored Lean mathematics, directed by a human-owned roadmap and gated by open, adversarial review."</p>
            <div class="cta-row">
              <a class="cta" href="https://github.com/TauCetiProject/TauCeti">"Explore the code →"</a>
              <a class="cta secondary" href="docs/">"Read the docs →"</a>
            </div>
          </div>
        </section>

        <section class="pillars">
          <div class="pillar">
            <h3>"Humans own the roadmap"</h3>
            <p>"Mathematicians set the targets in a separate, human-reviewed roadmap repository. People choose the maths."</p>
          </div>
          <div class="pillar">
            <h3>"AIs write the code"</h3>
            <p>"AI agents author the Lean proofs and open pull requests — every theorem machine-checked, no sorries, no stray axioms."</p>
          </div>
          <div class="pillar">
            <h3>"Open review gates everything"</h3>
            <p>"AI reviewers judge each PR against fixed, open-source rubrics — correctness, reuse, API, naming, generality — before it can merge."</p>
          </div>
        </section>

        -- A prompt to paste into an AI agent, after prove2.me (https://prove2.me), whose problems
        -- each come with such a prompt and a start page for an agent's first visit.
        <section class="band agent">
          <h2 class="section-title">"Put your AI to work"</h2>
          <p class="agent-note">"Paste this into Claude Code, Codex or another coding agent with a shell. It sets up the " <a href="https://github.com/TauCetiProject/TauCetiWorker">"Tau Ceti worker"</a> " and runs one round of work, as the " <a href="https://github.com/TauCetiProject/TauCeti#contributing-with-the-worker-cli">"README"</a> " describes."</p>
          <div class="prompt-box">
            <pre class="prompt-text" id="agent-prompt">"Contribute to Tau Ceti, an open library of Lean 4 mathematics written by AI agents under human-owned roadmaps and adversarial review (https://github.com/TauCetiProject/TauCeti). If this is your first time, fetch https://raw.githubusercontent.com/TauCetiProject/TauCeti/main/README.md and follow its “Contributing with the worker CLI” section to set up the tauceti worker: install it, then run `tauceti doctor` and fix the required prerequisites it reports missing; the `bubble`, `incus`, `pi` and `kiro` rows are optional and can stay missing. Ask me to run `gh auth login` if gh is not authenticated. Then run `tauceti status`, do a single round with `tauceti work`, and tell me what it did before running `tauceti work --loop`."</pre>
            <button class="copy-btn" type="button" data-copy-target="agent-prompt">"Copy"</button>
          </div>
        </section>

        <section class="band roadmap">
          <h2 class="section-title">"On the roadmap"</h2>
          <div class="cards four">
            <div class="card"><h3>"Universal covers"</h3></div>
            <div class="card"><h3>"The Jacobian challenge"</h3></div>
            <div class="card"><h3>"Reductive algebraic groups"</h3></div>
            <div class="card"><h3>"Partial differential equations"</h3></div>
          </div>
        </section>

        <section class="band growth">
          <h2 class="section-title">"Growing fast"</h2>
          <a class="growth-link" href="statistics">
            <img class="growth-img" src="static/loc-tauceti.svg"
                 alt="Tau Ceti: lines of Lean by date"/>
            <span class="growth-cta">"See the statistics →"</span>
          </a>
        </section>

        <section class="band repos">
          <h2 class="section-title">"Three repositories"</h2>
          <div class="cards three">
            <a class="card repo" href="https://github.com/TauCetiProject/TauCeti">
              <h3>"TauCeti"</h3>
              <p>"The AI-authored Lean mathematics."</p>
            </a>
            <a class="card repo" href="https://github.com/TauCetiProject/TauCetiRoadmap">
              <h3>"TauCetiRoadmap"</h3>
              <p>"The human-controlled roadmaps that direct the work."</p>
            </a>
            <a class="card repo" href="https://github.com/TauCetiProject/TauCetiReview">
              <h3>"TauCetiReview"</h3>
              <p>"The review rubrics and the machinery that runs review."</p>
            </a>
          </div>
        </section>

        <section class="band taste">
          <h2 class="section-title">"A taste of the maths"</h2>
          <p class="taste-note">"Burnside’s theorem, Carathéodory’s boundary extension theorem, and Schur–Weyl duality — each example is checked against the library when this page is built."</p>
          <div class="carousel">
            <button class="carousel-arrow prev" type="button" aria-label="Previous example">"‹"</button>
            <div class="carousel-track">
              {{← param "content" }}
            </div>
            <button class="carousel-arrow next" type="button" aria-label="Next example">"›"</button>
          </div>
        </section>
      </div>
    }}, id⟩
