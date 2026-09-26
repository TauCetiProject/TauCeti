#!/usr/bin/env python3
"""The generated data assets the Pages build carries from `build-data` to `build-site`.

One list, in one place, printed one per line for the workflow to read.

It used to be written out by hand in pages.yml. That made adding a chart two edits in two
different files, and when they landed in two different pull requests the list was silently
wrong: `merges-by-roadmap-and-contributor.svg` and `reviews-by-roadmap-and-contributor.svg`
were generated into `web/static_files` and then not carried, so the site referenced two images
that never arrived. Nothing failed -- the artifact was simply missing them.

Deriving the pull-request statistics half from `ASSET_NAMES` means that half can never drift
again. The rest is named here because those generators take their output path from the
workflow rather than declaring it, so there is nothing to import.
"""

import pr_stats_graphs

OTHER_ASSETS = [
    "loc-tauceti.svg",        # scripts/loc_graph.py, TauCeti
    "loc-roadmap.svg",        # scripts/loc_graph.py, the roadmap repository
    "loc-per-roadmap.svg",    # scripts/loc_roadmap_graph.py
    "participation.svg",      # scripts/participant_graph.py
    "progress.json",          # scripts/roadmap_progress.py
    "pipeline-health.json",   # scripts/pipeline_health.py
]

GENERATED_ASSETS = list(pr_stats_graphs.ASSET_NAMES) + OTHER_ASSETS


if __name__ == "__main__":
    print("\n".join(GENERATED_ASSETS))
