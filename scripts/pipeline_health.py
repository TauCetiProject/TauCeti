#!/usr/bin/env python3
"""Where is the pull-request pipeline slow right now, and why?

Merge throughput is one number at the end of a queue, so a fall in it says
something is wrong without saying what. This measures each stage separately:
how fast pull requests arrive at it, how fast they leave, how deep it currently
is, and how long they sit in it, each against a trailing baseline.

Historical rates describe lifecycle-label transitions. Current depths are checked
against the pinned merge gate; label disagreements and unknown reads are explicit.
Queue membership and reservations are reported separately. The stages include:

  awaiting-CI          waiting for a build on the latest commit
  awaiting-review      green, waiting for a reviewer
  review-in-progress   a review is running on this commit
  ci-failed            build failed; the author has to act
  awaiting-author      changes requested; the author has to act
  ready-to-merge       all per-PR merge prerequisites pass
  needs-human-review   approved changes require human review
  awaiting-dependency  waiting for a stacked base
  on-hold              a draft or explicit hold

Two of those are not the project's to fix. `ci-failed` and `awaiting-author`
sit with the contributor, and reading a backlog there as a project problem
would point effort at exactly the wrong place, so they are reported separately
from the stages the project owns.

Historical data comes from the statistics snapshot. Live reports also audit open
PRs and read the queue once; --data replays the stored evidence offline:

    scripts/pipeline_health.py                       # fetch and report
    scripts/pipeline_health.py --json                # machine-readable
    scripts/pr_stats_graphs.py --dump-data snap.json --out-dir /tmp/x
    scripts/pipeline_health.py --data snap.json      # replay, no network
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from pr_lifecycle import (  # noqa: E402
    LIFECYCLE_EPOCH,
    STAGE_ORDER,
    STATE_AUTHOR_ACTION,
    STATE_INACTIVE,
    current_stage,
    label_intervals,
    waiting_since,
    iso_z,
    parse_dt,
)
from pr_stats_graphs import (  # noqa: E402
    atomic_write, fetch_snapshot, load_previous, percentile,
)

OWNED_BY_PROJECT = [s for s in STAGE_ORDER if s not in STATE_AUTHOR_ACTION | STATE_INACTIVE]


def readiness_summary(snapshot):
    """Separate a displayed label, verified prerequisites, and actual queue state."""
    audit = snapshot.get("merge_readiness") or {}
    checked = audit.get("prs") or {}
    queue = audit.get("queue") or {"known": False, "reason": "queue has not been checked"}
    summary = {"labelled_ready": 0, "verified_eligible": 0, "blocked": 0,
               "unknown": 0, "unverified_ready": 0, "label_drift": [],
               "queue": queue, "checked_at": audit.get("checked_at")}
    eligible = set()
    for pr in snapshot["prs"]:
        if pr["state"] != "OPEN" or pr["is_draft"]:
            continue
        label = current_stage(pr)
        ready = label == "ready-to-merge"
        summary["labelled_ready"] += ready
        result = checked.get(str(pr["number"]))
        if result is None or result.get("eligible") is None:
            summary["unknown"] += 1
            summary["unverified_ready"] += ready
            continue
        if result["eligible"]:
            summary["verified_eligible"] += 1
            eligible.add(pr["number"])
        elif result["category"] is not None:
            summary["blocked"] += 1
        if result["category"] is not None and label != result["category"]:
            summary["label_drift"].append({"pr": pr["number"], "label": label,
                                            "actual": result["category"], "reason": result["reason"]})
    if queue["known"]:
        queued = set(queue["numbers"])
        summary["eligible_queued"] = len(eligible & queued)
        summary["eligible_not_queued"] = len(eligible - queued)
    return summary


def rate(count: int, hours: float) -> float:
    return count / hours if hours > 0 else 0.0


# Survival is a product of rationals, and a value that is mathematically exactly
# a half can land an ulp above it after a few multiplications: 0.9 * 6/9 * 5/6
# computes to 0.5000000000000001. Compared strictly, the median then skips the
# event time it was reached at and reports the next one, which on a cohort of
# ten moved the answer from 3h to 8h. No difference this small means anything
# here, so the comparison carries a tolerance far beneath one that would.
SURVIVAL_TOLERANCE = 1e-9


def median_dwell(completed: list[float], censored: list[float]) -> float | None:
    """Median spell length by Kaplan-Meier, given spells that have not ended.

    A spell still running is not a missing observation: it is the knowledge that
    this one has already lasted at least this long. Dropping those makes a
    filling stage look fast, because the spells still running are exactly the
    slow ones -- `awaiting-review` reported a median dwell below its own
    baseline while eighty-nine pull requests sat in it for a median of five
    hours. Counting elapsed time as if it were final understates too, for the
    opposite reason: at any instant most occupants are young. Neither naive
    choice is available, so censor properly instead.

    Every observation is taken to be watched from age zero, so the caller must
    pass an inception cohort: spells selected by when they began, censored at
    the end of the period. Spells picked out by where they *ended* would include
    some already under way when the period opened, and those are at risk only
    from the age they had then; there is no delayed entry here to express that.

    None when the estimator never falls to half, which is the honest answer for
    a stage in which most spells are still running.

    The median is the first duration at which survival is a half *or below*,
    after Klein and Moeschberger. `lifelines` takes the first strictly below,
    so the two differ by one event time on the cohorts where survival lands on
    a half exactly -- about one sample in eighty of a random check against it,
    and none for any other reason. This convention is the one that makes "the
    median has reached t" and "survival is above a half just before t" the same
    statement, which is what the stall test in `anomalies` relies on.
    """
    observations = sorted([(hours, 1) for hours in completed]
                          + [(hours, 0) for hours in censored])
    total = len(observations)
    survival = 1.0
    index = 0
    while index < total:
        duration = observations[index][0]
        # Everything sharing this duration is at risk at it, events and
        # censorings alike; only the events move the estimator.
        after = index
        events = 0
        while after < total and observations[after][0] == duration:
            events += observations[after][1]
            after += 1
        if events:
            survival *= 1 - events / (total - index)
            if survival <= 0.5 + SURVIVAL_TOLERANCE:
                return duration
        index = after
    return None


def survival_at(completed: list[float], censored: list[float],
                horizon: float) -> tuple[float | None, int]:
    """Kaplan-Meier survival at `horizon`, and how many were still at risk there.

    The point of asking this rather than for a median: a median needs follow-up
    until half the cohort has finished, which a short window cannot supply for a
    badly stalled stage, and the estimate goes null exactly when it matters
    most. Survival at a fixed horizon needs follow-up only as far as that
    horizon. "Is the median at least twice the usual" and "is at least half of
    the cohort still running at twice the usual median" are the same claim, and
    only the second is answerable in a day.

    None when follow-up ran out before the horizon on a censoring, which is not
    the same as nothing having lasted that long.
    """
    observations = sorted([(hours, 1) for hours in completed]
                          + [(hours, 0) for hours in censored])
    if not observations:
        return None, 0
    last_duration, last_was_event = observations[-1]
    if last_duration < horizon and not last_was_event:
        return None, 0
    total = len(observations)
    survival, index = 1.0, 0
    while index < total and observations[index][0] < horizon:
        duration = observations[index][0]
        after, events = index, 0
        while after < total and observations[after][0] == duration:
            events += observations[after][1]
            after += 1
        if events:
            survival *= 1 - events / (total - index)
        index = after
    return survival, sum(1 for hours, _ in observations if hours >= horizon)


def observable_hours(start: datetime, end: datetime) -> float:
    """Hours of the interval in which lifecycle labels could exist at all.

    The labels landed on LIFECYCLE_EPOCH, so a window reaching back before it
    contains time in which no event could have been recorded. Dividing by the
    requested duration rather than the observable one understates every rate on
    a wide baseline.
    """
    start = max(start, LIFECYCLE_EPOCH)
    return max((end - start).total_seconds() / 3600, 0.0)


def analyse(
    snapshot: dict,
    window_hours: float,
    baseline_hours: float,
    now: datetime | None = None,
) -> dict:
    if window_hours <= 0 or baseline_hours <= 0:
        raise ValueError("window and baseline must be positive")

    # Replaying a snapshot must measure it as it was, not as though it were
    # taken now: otherwise every open interval gains however long the file has
    # been sitting on disk, and every recent rate reads as zero.
    if now is None:
        now = parse_dt(snapshot.get("fetched_at")) or datetime.now(timezone.utc)
    now = now.astimezone(timezone.utc)

    prs = snapshot["prs"]
    window_start = now - timedelta(hours=window_hours)
    # Disjoint, so the baseline is something to compare against rather than
    # something the recent window is already part of.
    baseline_end = window_start
    baseline_start = baseline_end - timedelta(hours=baseline_hours)
    window_span = observable_hours(window_start, now)
    baseline_span = observable_hours(baseline_start, baseline_end)

    entered = defaultdict(lambda: {"window": 0, "baseline": 0})
    left = defaultdict(lambda: {"window": 0, "baseline": 0})
    dwell = defaultdict(lambda: {"window": [], "baseline": []})
    censored = defaultdict(lambda: {"window": [], "baseline": []})
    depth: defaultdict[str, int] = defaultdict(int)
    oldest: dict[str, float] = {}
    # How long each pull request now in a stage has been there. `oldest` is one
    # PR and says nothing about the rest, and the dwell times below describe
    # spells that ended, which is a different population: a stage that is
    # filling holds exactly the spells that have not ended. A census of the
    # occupants cannot be censored, because nothing has to finish to observe it.
    waiting_ages: defaultdict[str, list[float]] = defaultdict(list)
    unlabelled_open = 0
    checked = (snapshot.get("merge_readiness") or {}).get("prs") or {}
    label_depth = defaultdict(int)

    for pr in prs:
        if pr["state"] == "OPEN" and not pr["is_draft"]:
            stage = label_stage = current_stage(pr)
            if stage is not None:
                label_depth[stage] += 1
            else:
                unlabelled_open += 1
            verified = checked.get(str(pr["number"]))
            if verified is not None and verified.get("eligible") is not None:
                stage = verified["category"]
            if stage is not None:
                depth[stage] += 1
                # How long this pull request has been waiting is a question
                # about its spell, not about the label currently on it: the
                # clock does not restart when the pipeline swaps a label for
                # its sibling. Rates below are the opposite, and use the atomic
                # per-label intervals.
                began = waiting_since(pr, now) if stage == label_stage else None
                if began:
                    waited = (now - began).total_seconds() / 3600
                    oldest[stage] = max(oldest.get(stage, 0.0), waited)
                    waiting_ages[stage].append(waited)

        for label, start, end in label_intervals(pr, now):
            # Dwell times take an inception cohort: a spell belongs to the
            # period it *began* in, and is censored at the end of that period if
            # it had not finished by then. Selecting instead by where a spell
            # ended would admit spells already long under way when the period
            # opened, which were only ever at risk from the age they had then;
            # counting those from zero credits them with time nothing could
            # have happened in and pushes the estimate up.
            if baseline_start <= start < baseline_end:
                entered[label]["baseline"] += 1
                if end is None or end >= baseline_end:
                    censored[label]["baseline"].append(
                        (baseline_end - start).total_seconds() / 3600)
                else:
                    dwell[label]["baseline"].append(
                        (end - start).total_seconds() / 3600)
            if start >= window_start:
                entered[label]["window"] += 1
                if end is None:
                    censored[label]["window"].append(
                        (now - start).total_seconds() / 3600)
                else:
                    dwell[label]["window"].append((end - start).total_seconds() / 3600)

            # Departure rates are the opposite question, about when spells
            # ended rather than when they began, so they keep their own cohort.
            if end is None:
                continue
            if baseline_start <= end < baseline_end:
                left[label]["baseline"] += 1
            if end >= window_start:
                left[label]["window"] += 1

    def counted(field: str, start: datetime, end: datetime) -> int:
        return sum(
            1 for pr in prs
            if pr.get(field) and start <= parse_dt(pr[field]) < end
        )

    merge_readiness = readiness_summary(snapshot)
    stages = []
    for label in STAGE_ORDER:
        # The horizon a stall is judged at: SLOWDOWN_FACTOR times the dwell this
        # stage used to have. Asking what share of the recent cohort is still
        # running there is the same question as asking whether its median has
        # multiplied by that much, but needs follow-up only this far rather than
        # until half of a stalled cohort finishes -- which a day cannot supply.
        was = median_dwell(dwell[label]["baseline"], censored[label]["baseline"])
        horizon = SLOWDOWN_FACTOR * was if was else None
        surviving, at_risk = (survival_at(dwell[label]["window"],
                                          censored[label]["window"], horizon)
                              if horizon else (None, 0))
        stages.append({
            "stage": label,
            "owned_by_project": label in OWNED_BY_PROJECT,
            "depth": (None if label == "ready-to-merge" and merge_readiness["unverified_ready"]
                      else depth[label]),
            "label_depth": label_depth[label],
            "oldest_waiting_hours": oldest.get(label, 0.0),
            # How many of `depth` these describe. A waiting age is only read
            # where the verified stage agrees with the label, since an old
            # label's clock says nothing about a stage the audit moved the pull
            # request to, so under label drift these cover part of the stage.
            # Published rather than hidden: a percentile over a subset is worth
            # having, but only if the reader can see it is one.
            "waiting_count": len(waiting_ages[label]),
            "median_waiting_hours": percentile(waiting_ages[label], 0.5),
            "p90_waiting_hours": percentile(waiting_ages[label], 0.9),
            "entered_per_hour": rate(entered[label]["window"], window_span),
            "left_per_hour": rate(left[label]["window"], window_span),
            "baseline_entered_per_hour": rate(entered[label]["baseline"], baseline_span),
            "baseline_left_per_hour": rate(left[label]["baseline"], baseline_span),
            "left_count": left[label]["window"],
            "baseline_left_count": left[label]["baseline"],
            # How many spells the dwell estimate actually rests on. Not
            # `baseline_left_count`, which counts departures: a spell that began
            # before the period and ended inside it is a departure from it but
            # no part of its inception cohort, so the two can differ by any
            # amount and only this one says whether the median is supported.
            "dwell_completions": len(dwell[label]["window"]),
            "baseline_dwell_completions": len(dwell[label]["baseline"]),
            # And how many joined the cohort at all. A stage that has stalled
            # has few completions and many unfinished spells, so gating its
            # recent evidence on completions would switch the detector off in
            # exactly the case it exists for; the survival test below is
            # supported by the whole cohort rather than by the part that ended.
            "dwell_cohort": len(dwell[label]["window"]) + len(censored[label]["window"]),
            "baseline_dwell_cohort": (len(dwell[label]["baseline"])
                                      + len(censored[label]["baseline"])),
            "median_dwell_hours": median_dwell(dwell[label]["window"],
                                               censored[label]["window"]),
            "baseline_median_dwell_hours": was,
            "stall_horizon_hours": horizon,
            # `null` where follow-up ran out before the horizon on a spell that
            # was still running, which is not the same as nothing having lasted
            # that long, and is the honest answer rather than a quiet zero.
            "stall_horizon_surviving": surviving,
            "stall_horizon_at_risk": at_risk,
        })

    result = {
        "schema_version": 4,
        "repo": snapshot.get("repo"),
        "generated_at": iso_z(now),
        "snapshot_fetched_at": snapshot.get("fetched_at"),
        "window_hours": window_hours,
        "baseline_hours": baseline_hours,
        "observable_window_hours": window_span,
        "observable_baseline_hours": baseline_span,
        "opened_per_hour": rate(counted("created_at", window_start, now), window_span),
        "baseline_opened_per_hour": rate(
            counted("created_at", baseline_start, baseline_end), baseline_span),
        "merged_per_hour": rate(counted("merged_at", window_start, now), window_span),
        "baseline_merged_per_hour": rate(
            counted("merged_at", baseline_start, baseline_end), baseline_span),
        "merged_count": counted("merged_at", window_start, now),
        "baseline_merged_count": counted("merged_at", baseline_start, baseline_end),
        "opened_count": counted("created_at", window_start, now),
        "baseline_opened_count": counted("created_at", baseline_start, baseline_end),
        "open_prs": sum(1 for pr in prs if pr["state"] == "OPEN"),
        "open_prs_without_a_lifecycle_label": unlabelled_open,
        "stages": stages,
        "merge_readiness": merge_readiness,
    }
    result["anomalies"] = anomalies(result)
    result["cause"] = find_cause(result)
    return result


ROUND_TO = 2


def rounded(result: dict) -> dict:
    """Round for output only.

    Comparisons run on the raw values: rounding first turns one event in a
    fortnight into a rate of exactly zero, which silently changes which branch
    every threshold takes.
    """
    def fix(value):
        return round(value, ROUND_TO) if isinstance(value, float) else value

    out = {k: fix(v) for k, v in result.items() if k not in ("stages", "anomalies")}
    out["stages"] = [{k: fix(v) for k, v in stage.items()} for stage in result["stages"]]
    out["anomalies"] = [{k: fix(v) for k, v in a.items()} for a in result.get("anomalies") or []]
    return out


# A stage must clear one of these to be blamed at all. Without them the search
# always returns something, and a heuristic that always finds a culprit is not a
# diagnosis.
MIN_COMPLETIONS = 3          # below this a median dwell is noise
# The stall test needs far more than that. It asks whether over half of a cohort
# is still running at the horizon, and half of three is a coin tossed three
# times: simulated on a stage with nothing wrong, a cohort of three called it
# stalled 15.5% of the time, ten 7.7%, twenty 1.5%, fifty never. Twenty is where
# the noise stops being the loudest thing in the answer. The cost is that a
# genuinely low-traffic stage is not judged on dwell at all, which is the right
# way round: it has not supplied the evidence to be judged on.
MIN_STALL_COHORT = 20
GROWTH_PER_HOUR = 0.05       # arrivals must outpace departures by a real margin
SLOWDOWN_FACTOR = 2.0        # multiple of normal dwell that counts as a stall
THROUGHPUT_FRACTION = 0.75   # of baseline, below which something is wrong


def anomalies(result: dict) -> list[dict]:
    """Every project-owned stage misbehaving, worst first.

    A pipeline can have more than one thing wrong with it, and on real data it
    usually does: naming a single culprit hid a stage full of approved work that
    was not merging, because a different stage happened to be filling faster.
    """
    found = []
    for stage in result["stages"]:
        if (stage["stage"] == "ready-to-merge"
                and (result.get("merge_readiness") or {}).get("unverified_ready", 0)):
            continue  # label depth alone cannot establish a merge bottleneck
        if not stage["owned_by_project"] or not stage["depth"]:
            continue
        growth = stage["entered_per_hour"] - stage["left_per_hour"]
        normal = stage["baseline_median_dwell_hours"]
        # The baseline median needs completions behind it. The recent side is
        # gated on its cohort instead: a stalled stage has few completions by
        # definition, so gating that on completions would switch the detector
        # off in exactly the case it exists for.
        enough = (stage["baseline_dwell_completions"] >= MIN_STALL_COHORT
                  and stage["dwell_cohort"] >= MIN_STALL_COHORT)
        # A stall is how long a spell in this stage takes now against how long
        # it took, asked as survival at the horizon rather than as a ratio of
        # medians. The two say the same thing, but a recent median goes null
        # once a stage is slower than the window is long, which is to say it
        # disappears just as the stall becomes serious.
        #
        # No occupant age belongs here. The occupants are a length-biased
        # sample -- a long spell is likelier to be caught by a census than a
        # short one -- so on a simulated stable queue whose dwell is 1h for
        # nine spells in ten and 100h for the tenth, the median occupant reads
        # 33x the median dwell and 91% of occupants have outlasted the baseline
        # p90. Both were the stall test here once; both fire on a healthy queue.
        surviving = stage["stall_horizon_surviving"]
        # A ratio when one can be had, for reading rather than for deciding.
        # None, never zero: a stage too slow to estimate has not been measured
        # to be fast.
        recent = stage["median_dwell_hours"]
        slowdown = (recent / normal if enough and normal and recent else None)
        # A newly introduced label has no historical baseline; a backfill into
        # it is not evidence of a new performance failure.
        established = (stage["baseline_left_count"] >= MIN_COMPLETIONS
                       or stage["baseline_entered_per_hour"] > 0)
        filling = growth > GROWTH_PER_HOUR and established
        # Strictly above a half, which is what makes this exactly the claim that
        # the median has reached the horizon: `median_dwell` declares the median
        # at the first duration where survival falls to a half or below, so a
        # survival of exactly a half means the median has already been reached
        # rather than not yet. One spell finishing at 1h and one still running
        # at 5h leaves survival at exactly 0.5 at a 2h horizon, with a median of
        # 1h -- half the horizon, and no stall at all.
        stalled = (enough and surviving is not None
                   and surviving > 0.5 + SURVIVAL_TOLERANCE)
        if not (filling or stalled):
            continue
        reasons = []
        if filling:
            reasons.append(
                f"arriving at {stage['entered_per_hour']:.2f}/h and leaving at "
                f"{stage['left_per_hour']:.2f}/h, so it is filling faster than it drains"
            )
        if stalled:
            reasons.append(
                f"{surviving:.0%} of the spells that began in it are still running at "
                f"{stage['stall_horizon_hours']:.1f}h, {SLOWDOWN_FACTOR:g}x its "
                f"{normal:.1f}h normal dwell"
            )
        found.append({
            "stage": stage["stage"],
            "depth": stage["depth"],
            "growth_per_hour": growth,
            "slowdown_factor": slowdown,
            "surviving_at_stall_horizon": surviving,
            "why": "; ".join(reasons),
        })
    # Filling beats merely stalled, then by how fast, then by how stuck. Ordered
    # on the survival, since that is what `stalled` was decided on and it is
    # available whenever the decision was; the ratio is null for the stages too
    # slow to estimate, which are the worst rather than the least of them.
    found.sort(key=lambda item: (item["growth_per_hour"] > GROWTH_PER_HOUR,
                                 item["growth_per_hour"],
                                 item["surviving_at_stall_horizon"] or 0.0),
               reverse=True)
    return found


def find_cause(result: dict) -> dict | None:
    """Why throughput is down, when it is.

    Fewer merges can mean the queue is stuck or simply that less went into it,
    and those want opposite responses: adding review capacity does nothing about
    a week when nobody opened anything. Both are answers, so both are reported.
    Only when neither holds is the fall genuinely unexplained, and saying so is
    better than picking a stage to blame.
    """
    baseline = result["baseline_merged_per_hour"]
    if not baseline or result["baseline_merged_count"] < MIN_COMPLETIONS:
        # Nothing to compare against. Saying "healthy" here would be a guess
        # dressed as a finding.
        return {"kind": "insufficient_data", "stage": None,
                "why": "not enough baseline data to judge"}
    if result["merged_per_hour"] >= baseline * THROUGHPUT_FRACTION:
        return None

    readiness = result.get("merge_readiness") or {}

    found = result["anomalies"] if "anomalies" in result else anomalies(result)
    opened, opened_baseline = result["opened_per_hour"], result["baseline_opened_per_hour"]
    intake_down = (
        opened_baseline
        and opened < opened_baseline * THROUGHPUT_FRACTION
        and result["baseline_opened_count"] >= MIN_COMPLETIONS
    )

    if readiness.get("unverified_ready") and not found:
        return {"kind": "unverified", "stage": None,
                "why": "ready labels have not been verified against the merge gate; "
                       "merge-queue capacity cannot be inferred from them"}
    if intake_down and not found:
        return {
            "kind": "intake", "stage": None,
            "why": (
                f"fewer pull requests are arriving: {opened:.2f}/h against "
                f"{opened_baseline:.2f}/h, and no stage was measured to be stuck; "
                "there is less to merge"
            ),
        }
    if found:
        primary = dict(found[0], kind="stage")
        if intake_down:
            primary["why"] += (
                f". Arrivals are also down, at {opened:.2f}/h against "
                f"{opened_baseline:.2f}/h, so the queue is both thinner and slower"
            )
        return primary
    return {
        "kind": "unexplained", "stage": None,
        "why": (
            f"arrivals are steady at {opened:.2f}/h and no stage was measured to "
            "be backing up, so the fall is not explained by the queue"
        ),
    }


def report(result: dict) -> str:
    lines = []
    merged, baseline = result["merged_per_hour"], result["baseline_merged_per_hour"]
    change = f"{merged / baseline:.0%} of baseline" if baseline else "no baseline"
    lines.append(f"{result['repo']}  ({result['open_prs']} open)")
    lines.append(
        f"  merged {merged}/h over the last {result['window_hours']:.0f}h "
        f"against {baseline}/h over {result['baseline_hours'] / 24:.0f}d — {change}"
    )
    lines.append(
        f"  opened {result['opened_per_hour']}/h against {result['baseline_opened_per_hour']}/h"
    )
    lines.append("")
    header = (f"  {'stage':<20}{'depth':>6}{'waiting':>9}{'oldest':>9}"
              f"{'in/h':>7}{'out/h':>7}{'dwell':>8}{'normal':>8}")
    lines.append(header)
    lines.append("  " + "-" * (len(header) - 2))
    for stage in result["stages"]:
        mark = " " if stage["owned_by_project"] else "*"
        dwell = stage["median_dwell_hours"]
        normal = stage["baseline_median_dwell_hours"]
        # `waiting` is the middle of what is sitting in the stage now; `dwell`
        # is the middle of a spell in it. Not a ratio: a census is length-biased
        # towards long spells, so healthy occupants are older than typical.
        median_wait = stage["median_waiting_hours"]
        lines.append(
            f"  {mark}{stage['stage']:<19}{str(stage['depth']) if stage['depth'] is not None else '?':>6}"
            f"{(f'{median_wait:.1f}h' if median_wait is not None else '-'):>9}"
            f"{stage['oldest_waiting_hours']:>8.0f}h"
            f"{stage['entered_per_hour']:>7}{stage['left_per_hour']:>7}"
            f"{(f'{dwell:.1f}h' if dwell is not None else '-'):>8}"
            f"{(f'{normal:.1f}h' if normal is not None else '-'):>8}"
        )
    lines.append("")
    lines.append("  * waiting on the contributor, a dependency, or an explicit hold")
    lines.append("")
    readiness = result.get("merge_readiness")
    if readiness:
        lines.append(f"  merge prerequisites: {readiness['verified_eligible']} verified eligible; "
                     f"{readiness['blocked']} blocked; {readiness['unknown']} unknown "
                     f"({readiness['labelled_ready']} labelled ready)")
        if readiness["label_drift"]:
            lines.append(f"  label drift: {len(readiness['label_drift'])} PR(s) disagree with live evidence; "
                         "current stage depths above use the verified classification")
        queue = readiness["queue"]
        if queue["known"]:
            lines.append(f"  queue: {readiness['eligible_queued']} eligible PR(s) queued; "
                         f"{readiness['eligible_not_queued']} eligible PR(s) not queued")
            if queue.get("reservation_holder") is not None:
                lines.append(f"  queue reservation: pin-moving #{queue['reservation_holder']}")
        else:
            lines.append("  queue state: unknown")
        if readiness["unverified_ready"]:
            lines.append("  ready-label counts are unverified; they are not evidence of merge capacity")
        lines.append("")
    if result.get("open_prs_without_a_lifecycle_label"):
        lines.append(
            f"  note: {result['open_prs_without_a_lifecycle_label']} open PR(s) carry no single "
            "lifecycle label, so they are absent from every depth above"
        )

    cause = result["cause"]
    found = result.get("anomalies") or []

    if cause is not None and cause["kind"] == "stage":
        lines.append(f"  cause: {cause['stage']} — {cause['why']}")
        for other in found[1:]:
            lines.append(f"  also:  {other['stage']} — {other['why']}")
    elif cause is not None:
        lines.append(f"  cause: {cause['why']}")
        for other in found:
            lines.append(f"  also:  {other['stage']} — {other['why']}")
    elif found:
        # Throughput has not fallen yet. That is not a reason to stay quiet: a
        # stage taking in more than it lets out is what a fall in throughput
        # looks like before it arrives, and by the time merges drop the queue
        # has already built.
        share = f"{merged / baseline:.0%} of baseline" if baseline else "unmeasured"
        lines.append(f"  throughput is holding at {share}, but the queue is building:")
        for other in found:
            lines.append(f"  building:  {other['stage']} — {other['why']}")
    else:
        lines.append("  throughput is normal; no stage is backing up")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default="TauCetiProject/TauCeti")
    parser.add_argument("--data", type=Path, help="replay a normalized offline snapshot")
    parser.add_argument("--dump-data", type=Path, help="write the fetched snapshot")
    parser.add_argument("--since-data", type=Path,
                        help="an earlier snapshot; pull requests untouched since it was "
                             "written keep their recorded timeline rather than being "
                             "walked again. Walking every timeline costs one request per "
                             "pull request and no longer fits in an hour's API budget.")
    parser.add_argument("--out", type=Path, help="write the JSON result here")
    parser.add_argument("--window", type=float, default=24.0, help="recent window, hours")
    parser.add_argument("--baseline", type=float, default=14 * 24.0, help="baseline, hours")
    parser.add_argument("--json", action="store_true", help="print JSON instead of a report")
    parser.add_argument("--verify-readiness", action="store_true",
                        help="check current merge prerequisites and queue even when using --data")
    parser.add_argument("--as-of", type=parse_dt,
                        help="analyse as at this instant (default: the snapshot's fetched_at)")
    args = parser.parse_args(argv)

    snapshot = (json.loads(args.data.read_text()) if args.data
                else fetch_snapshot(args.repo, load_previous(args.since_data, args.repo)))
    if not args.data or args.verify_readiness:
        if args.as_of:
            parser.error("live readiness verification cannot be combined with historical --as-of")
        sys.path.insert(0, str(Path(__file__).resolve().parent / "pr_status"))
        import readiness
        snapshot["merge_readiness"] = readiness.audit(snapshot)
    if args.dump_data:
        args.dump_data.write_text(json.dumps(snapshot, indent=1))

    result = rounded(analyse(snapshot, args.window, args.baseline, args.as_of))

    if args.out:
        # Atomically, matching pr_stats_graphs.py: a half-written JSON file is
        # worse than a missing one, because everything downstream trusts it.
        atomic_write(args.out, json.dumps(result, indent=1))
    print(json.dumps(result, indent=1) if args.json else report(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
