# Roadmap completion statistics

`roadmap_completion.py` generates three Statistics-page SVGs and
`roadmap-completion.json`, using full-history clones of TauCeti and TauCetiRoadmap.
No GitHub API or model invocation is needed. The Pages workflow regenerates these
at every deployment and retains the previous assets if generation fails.

```sh
python3 scripts/roadmap_completion.py \
  --roadmap-repo ../TauCetiRoadmap --roadmap-ref origin/main \
  --code-repo . --code-ref HEAD --out-dir web/static_files
```

For a reproducible snapshot, add `--today 2026-10-08`; measurements stop at the
previous complete UTC day. The workflow avoids counting library history twice by
passing `--code-data`, the daily pairs exported by `loc_graph.py --dump-data`.
When those pairs are supplied, their final date fixes the cutoff (unless `--today`
is explicit), so crossing midnight between generators does not change the window.

## Charts

- `loc-roadmap.svg`: Markdown and Lean specification lines in actual roadmap
  directories under both `TauCetiRoadmap/` and `Completed/`, including reference notes.
  Generated `STATUS.md` and `PROGRESS.md` are excluded. Archiving transfers size into the
  completed portion without removing it from the total. An active successor
  and an archived roadmap with the same name remain separate specifications.
- `roadmap-layers.svg`: all currently named layers/lanes, including constituent
  roadmaps of an umbrella without double-counting their parent's layers.
  Coverage uses `roadmap_progress.py`'s heading and machine marker validation rules;
  the Progress page's transitional hand-read assessments are not replayed here.
  Only `done` receives credit; partial, untouched and unassessed remain in the
  denominator. The graph highlights unassessed layers. Human archival marks all
  that archived specification's layers complete, even if a report still has gaps.
- `roadmap-exhaustion.svg`: two authoring scenarios for each of two measures,
  archived specification size and completed layer count. These measures need
  not agree, since archival decisions and reports differ and goals vary in size.

Histories sample the final first-parent snapshot of each complete UTC day;
unchanged days carry forward. They do not read feature branches, untracked files,
or the current partial day. Old reports are applied to the specification that
existed at that observation date. Edited specifications retaining the same layer
IDs keep their old assessments with a stale flag, as on the Progress page;
changed layer IDs invalidate their assessment.

## Forecast

For each measure, let `C` be net observed completion credit, `L` be added library
lines over the recorded roadmap history, `v` be library LOC growth per day over
the last seven complete days, `A` be net specification growth per day over those
same seven days (floored at zero), and `B` be the current unfinished backlog.

```text
inferred completion/day = (C / L) * v
stop-authoring days     = B / inferred completion/day
continue-authoring days = B / (inferred completion/day - A)
```

Roadmap credit is frozen at the number of specification lines at archival;
later edits to an archived document do not create completion credit. Reopening
withdraws that credit. Layer credit follows the currently recorded done set,
so withdrawn assessments or removed layers reduce credit. Completion events in
the JSON include the library LOC at their observation date, allowing other fits
without re-reading git history. Events are signed credit changes: archival can
emit offsetting removals of active-layer keys and additions of archived-layer keys.
Consumers should sum their signed units; these pairs create no net new completion.

Absent positive completion history or positive recent library growth produces
`insufficient-history` with `days: null`. An incomplete seven-day observation
window does the same. If authoring equals or exceeds inferred completion, the
continued-authoring scenario is `not-catching-up`, also with `days: null`.
An empty recorded backlog produces zero days. No non-finite JSON numbers are used.

These are rough extrapolations of observations, not measurements of effort or
predictions of proof difficulty. First reports can recognize old work in a batch;
reports and archival decisions lag implementation; README revisions change scope;
library LOC includes maintenance; and the remaining goals can be much harder than
the completed ones. Missing assessments earn no credit, so a backlog can include
work already implemented but not yet reported. The site displays approximate
durations and keeps the exact inputs and assumptions in JSON.

Run the regressions with `PYTHONPATH=scripts python3 scripts/test_roadmap_completion.py`.
