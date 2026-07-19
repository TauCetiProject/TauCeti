#!/usr/bin/env python3
"""Render the proof-profile PR comment from countHeartbeats measurement logs.

Called by .github/workflows/pr-profile.yml, in the trusted step that runs
*after* the sandboxed measurement finishes. Inputs are environment variables
and the per-file `.hb` logs the sandbox wrote under $PREP/src; the output is
the Markdown comment body written to $OUTPUT.

The metric is heartbeats, from Mathlib's `linter.countHeartbeats` (reported in
`maxHeartbeats` units), summed over a file's declarations. Heartbeats are
deterministic and machine-independent, so they are the signal we compare and
flag on; wall time is not measured here.

New (added) files get an absolute per-file count. Modified files get a
base -> head comparison: a file is flagged as a build-cost regression when its
head cost is at least FLAG_RATIO times its base cost, provided the absolute
rise clears FLAG_MIN_ABS_HB (so a tiny file cannot flag on a few heartbeats).
The default ratio is 1.5, i.e. a refactor may not make a file half again as
expensive to elaborate. The comment is advisory and never fails the build.

A modified file's base and head sources are both elaborated against the same
built (head) environment. That is sound when a change is local to the file's
own proofs and definition bodies; a base source that no longer elaborates
there (typically because a statement it depends on changed) is reported and
left out of the comparison rather than mismeasured.
"""

import os
import re
from pathlib import Path

# Matches both `'Foo.bar' used 1234 heartbeats, ...` (named declaration) and
# `Used 25 heartbeats, ...` (anonymous, e.g. an `example`).
HEARTBEAT_RE = re.compile(
    r"(?:'[^']+'\s+)?[Uu]sed\s+(?:approximately\s+)?(?P<heartbeats>[0-9]+)\s+heartbeats"
)

FLAG_RATIO = float(os.environ.get("FLAG_RATIO", "1.5"))
FLAG_MIN_ABS_HB = float(os.environ.get("FLAG_MIN_ABS_HB", "1000"))

prep = Path(os.environ["PREP"])
output = Path(os.environ.get("OUTPUT", "profile.md"))
run_url = os.environ.get("RUN_URL", "")

MARKER = "<!-- proof-profile-comment -->"


def parse_hb(log_path: Path) -> dict | None:
    """Total heartbeats, declaration count, and error state for one `.hb` log.

    Returns None when the log is absent (the file was not measured on this side).
    """
    if not log_path.exists():
        return None
    heartbeats = 0.0
    declarations = 0
    errored = False
    for line in log_path.read_text(errors="replace").splitlines():
        if re.search(r"\berror:", line):
            errored = True
        match = HEARTBEAT_RE.search(line)
        if match:
            heartbeats += float(match.group("heartbeats"))
            declarations += 1
    return {"heartbeats": heartbeats, "declarations": declarations, "errored": errored}


def fmt(value: float) -> str:
    return f"{value:,.0f}"


def fmt_signed(value: float) -> str:
    return f"{value:+,.0f}"


def fmt_pct(delta: float, base: float) -> str:
    if base <= 0:
        return "—"
    return f"{delta / base * 100:+.1f}%"


def fmt_ratio(head: float, base: float) -> str:
    if base <= 0:
        return "—"
    return f"{head / base:.2f}×"


# The prep step writes one manifest row per profiled file: side, slug, path.
# The slug names the file's `.hb` log(s); reading it here (rather than
# recomputing it) keeps this in lockstep with prep however slugs are formed.
added: list[tuple[str, str]] = []
modified: list[tuple[str, str]] = []
manifest = prep / "manifest.tsv"
if manifest.exists():
    for row in manifest.read_text().splitlines():
        parts = row.split("\t")
        if len(parts) != 3:
            continue
        side, slug, path = parts
        (added if side == "added" else modified).append((slug, path))

out: list[str] = [f"{MARKER}\n", "## Proof profile (heartbeats)\n\n"]
out.append(
    "Advisory only; this never blocks merge. Heartbeats come from Mathlib's "
    "`countHeartbeats` linter, in `maxHeartbeats` units, summed over each "
    "file's declarations.\n\n"
)

# --- Modified files: base -> head comparison, with the regression flag. ------
comparison_rows = []
uncompared = []
for slug, path in modified:
    base = parse_hb(prep / "src" / "base" / f"{slug}.hb")
    head = parse_hb(prep / "src" / "head" / f"{slug}.hb")
    if head is None:
        continue
    if base is None or base["errored"] or base["heartbeats"] <= 0:
        uncompared.append(path)
        continue
    base_hb = base["heartbeats"]
    head_hb = head["heartbeats"]
    delta = head_hb - base_hb
    flagged = head_hb >= FLAG_RATIO * base_hb and delta >= FLAG_MIN_ABS_HB
    comparison_rows.append(
        {
            "path": path,
            "base": base_hb,
            "head": head_hb,
            "delta": delta,
            "flagged": flagged,
            "head_err": head["errored"],
        }
    )

comparison_rows.sort(key=lambda r: (-r["delta"], r["path"]))
flagged_rows = [r for r in comparison_rows if r["flagged"]]

if comparison_rows:
    total_base = sum(r["base"] for r in comparison_rows)
    total_head = sum(r["head"] for r in comparison_rows)
    total_delta = total_head - total_base
    total_flag = total_head >= FLAG_RATIO * total_base and total_delta >= FLAG_MIN_ABS_HB

    out.append("### Modified files — base → head\n\n")
    if flagged_rows or total_flag:
        names = ", ".join(f"`{r['path']}`" for r in flagged_rows) or "the total"
        out.append(
            f"⚠️ **Build-cost regression:** {names} grew by at least "
            f"{FLAG_RATIO:g}× in heartbeats (floor {fmt(FLAG_MIN_ABS_HB)} HB). "
            "A refactor should not make a file half again as expensive to "
            "elaborate; please check whether this is intended.\n\n"
        )
    else:
        out.append(
            f"No modified file crossed the {FLAG_RATIO:g}× regression flag "
            f"(floor {fmt(FLAG_MIN_ABS_HB)} HB).\n\n"
        )
    out.append("| File | HB base | HB head | Δ HB | Δ % | ×base |\n")
    out.append("|---|---:|---:|---:|---:|---:|\n")
    for r in comparison_rows:
        mark = " ⚠️" if r["flagged"] else ""
        note = " (head errored)" if r["head_err"] else ""
        out.append(
            f"| `{r['path']}`{mark}{note} | {fmt(r['base'])} | {fmt(r['head'])} "
            f"| {fmt_signed(r['delta'])} | {fmt_pct(r['delta'], r['base'])} "
            f"| {fmt_ratio(r['head'], r['base'])} |\n"
        )
    out.append(
        f"| **Total** | **{fmt(total_base)}** | **{fmt(total_head)}** "
        f"| **{fmt_signed(total_delta)}** | **{fmt_pct(total_delta, total_base)}** "
        f"| **{fmt_ratio(total_head, total_base)}** |\n\n"
    )

if uncompared:
    out.append(
        "_Not compared (the base source no longer elaborates against the "
        "built environment, usually because a statement it depends on "
        "changed): "
        + ", ".join(f"`{p}`" for p in uncompared)
        + "._\n\n"
    )

# --- Added files: absolute cost. ---------------------------------------------
added_rows = []
for slug, path in added:
    head = parse_hb(prep / "src" / "added" / f"{slug}.hb")
    if head is None:
        continue
    added_rows.append(
        {
            "path": path,
            "heartbeats": head["heartbeats"],
            "declarations": head["declarations"],
            "errored": head["errored"],
        }
    )
added_rows.sort(key=lambda r: (-r["heartbeats"], r["path"]))

if added_rows:
    out.append("### New files — absolute cost\n\n")
    out.append("| File | Heartbeats | Declarations |\n")
    out.append("|---|---:|---:|\n")
    for r in added_rows:
        note = " ⚠️ (errored)" if r["errored"] else ""
        out.append(
            f"| `{r['path']}`{note} | {fmt(r['heartbeats'])} "
            f"| {fmt(r['declarations'])} |\n"
        )
    out.append("\n")

if not comparison_rows and not added_rows and not uncompared:
    out.append("_No new or modified `TauCeti/` Lean files to profile._\n\n")

if run_url:
    out.append(f"<sub>[measurement run]({run_url}) · re-run with `/profile`</sub>\n")

output.write_text("".join(out))
print(f"Wrote {output} ({len(comparison_rows)} compared, {len(added_rows)} new, "
      f"{len(flagged_rows)} flagged)")
