#!/usr/bin/env python3
"""Hermetic tests for scripts/pipeline_health.py."""

from __future__ import annotations

import unittest
from datetime import datetime, timedelta, timezone

import pipeline_health as health
import pr_lifecycle as health_lc

UTC = timezone.utc
NOW = datetime(2026, 8, 25, 12, 0, tzinfo=UTC)


def iso(when: datetime) -> str:
    return when.strftime("%Y-%m-%dT%H:%M:%SZ")


def pr(number, events, *, state="OPEN", created=None, merged=None):
    """A PR with a lifecycle label timeline, as fetch_prs would return it."""
    return {
        "number": number,
        "created_at": iso(created or NOW - timedelta(days=1)),
        "merged_at": iso(merged) if merged else None,
        "closed_at": iso(merged) if merged else None,
        "state": state,
        "is_draft": False,
        "author": "someone",
        "labels": [events[-1][1]] if events and state == "OPEN" else [],
        "labeled_events": [
            {"created_at": iso(at), "label": label} for at, label in events
        ],
    }


def snapshot(prs):
    return {"schema_version": 1, "repo": "TauCetiProject/TauCeti",
            "fetched_at": iso(NOW), "prs": prs, "scoreboards": {}}


class IntervalTests(unittest.TestCase):
    def test_consecutive_labels_bound_each_spell(self):
        item = pr(1, [
            (NOW - timedelta(hours=10), "awaiting-CI"),
            (NOW - timedelta(hours=8), "awaiting-review"),
        ])
        spells = list(health_lc.label_intervals(item, NOW))
        self.assertEqual([s[0] for s in spells], ["awaiting-CI", "awaiting-review"])
        self.assertEqual((spells[0][2] - spells[0][1]), timedelta(hours=2))

    def test_an_open_pr_s_last_spell_is_still_running(self):
        item = pr(1, [(NOW - timedelta(hours=3), "awaiting-review")])
        self.assertIsNone(list(health_lc.label_intervals(item, NOW))[-1][2])

    def test_a_merged_pr_s_last_spell_ends_at_the_merge(self):
        merged = NOW - timedelta(hours=1)
        item = pr(2, [(NOW - timedelta(hours=5), "ready-to-merge")],
                  state="MERGED", merged=merged)
        _, start, end = list(health_lc.label_intervals(item, NOW))[-1]
        self.assertEqual(end, merged)

    def test_non_lifecycle_labels_are_ignored(self):
        item = pr(3, [(NOW - timedelta(hours=4), "roadmap:algebra"),
                      (NOW - timedelta(hours=2), "awaiting-review")])
        self.assertEqual([s[0] for s in health_lc.label_intervals(item, NOW)],
                         ["awaiting-review"])

    def test_a_pr_with_no_lifecycle_events_yields_nothing(self):
        self.assertEqual(list(health_lc.label_intervals(pr(4, []), NOW)), [])


class DwellEstimatorTests(unittest.TestCase):
    """`median_dwell` has to use spells that have not ended yet.

    They are not missing observations; they are the knowledge that those spells
    have already lasted at least that long, and in a filling stage they are the
    slow ones. A median over completions alone cannot see them.
    """

    def test_with_nothing_still_running_it_is_just_the_median(self):
        self.assertEqual(health.median_dwell([1.0, 2.0, 3.0], []), 2.0)

    def test_a_long_running_spell_raises_the_estimate(self):
        """Completions alone would call this 10.5h by averaging 1 and 20. The
        spell sitting at 10h and still going is evidence against that."""
        self.assertEqual(health.median_dwell([1.0, 20.0], [10.0]), 20.0)

    def test_it_declines_to_answer_when_most_spells_are_still_running(self):
        """The old estimator called this 1.5h, which is the one thing it is
        certainly not: two spells finished quickly and three are still going."""
        self.assertIsNone(health.median_dwell([1.0, 2.0], [10.0, 10.0, 10.0]))

    def test_an_empty_sample_has_no_median(self):
        self.assertIsNone(health.median_dwell([], []))
        self.assertIsNone(health.median_dwell([], [5.0]))

    def test_a_censoring_tied_with_an_event_stays_in_the_risk_set(self):
        """Standard convention: at equal durations the event is taken first, so
        S(1) = 1 - 1/3 and the median falls at 2 rather than 1."""
        self.assertEqual(health.median_dwell([1.0, 2.0], [1.0]), 2.0)

    def test_a_survival_of_exactly_a_half_is_not_missed_by_rounding(self):
        """S(3) here is 0.9 * 6/9 * 5/6, which is exactly a half and computes to
        0.5000000000000001. Compared strictly the median skipped to the next
        event time and reported 8.0 -- nearly three times the right answer, on a
        cohort of ten. Checked against lifelines, which gives 3.0."""
        completed = [8.0, 2.0, 13.0, 2.0, 3.0, 2.0, 1.0, 8.0]
        self.assertEqual(health.median_dwell(completed, [13.0, 5.0]), 3.0)

    def test_it_matches_the_estimator_worked_by_hand(self):
        """Events at 1, 3, 5 with censorings at 2 and 4, which is the textbook
        shape. Survival steps 1 -> 4/5, then 4/5 * 2/3 = 0.533 at t=3, then 0 at
        t=5, so the median is 5 -- not the 3 an uncensored median would give."""
        self.assertEqual(health.median_dwell([1.0, 3.0, 5.0], [2.0, 4.0]), 5.0)


class AnalysisTests(unittest.TestCase):
    def test_depth_counts_only_prs_still_in_the_stage(self):
        data = snapshot([
            pr(1, [(NOW - timedelta(hours=2), "awaiting-review")]),
            pr(2, [(NOW - timedelta(hours=3), "awaiting-review")]),
            pr(3, [(NOW - timedelta(hours=9), "awaiting-review"),
                   (NOW - timedelta(hours=1), "ready-to-merge")]),
        ])
        result = health.analyse(data, 24, 24 * 14, NOW)
        by_stage = {s["stage"]: s for s in result["stages"]}
        self.assertEqual(by_stage["awaiting-review"]["depth"], 2)
        self.assertEqual(by_stage["ready-to-merge"]["label_depth"], 1)
        self.assertIsNone(by_stage["ready-to-merge"]["depth"])

    def test_an_unfinished_spell_does_not_bias_dwell_times_downwards(self):
        """A PR still sitting in a stage has not finished waiting, so counting
        its time so far as a completed dwell would make a stuck stage look fast."""
        data = snapshot([
            pr(1, [(NOW - timedelta(hours=100), "awaiting-review")]),          # stuck
            pr(2, [(NOW - timedelta(hours=4), "awaiting-review"),
                   (NOW - timedelta(hours=3), "ready-to-merge")]),             # 1h, done
        ])
        stage = next(s for s in health.analyse(data, 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertEqual(stage["median_dwell_hours"], 1.0)
        self.assertEqual(stage["oldest_waiting_hours"], 100.0)

    def test_a_filling_stage_cannot_report_a_fast_dwell_from_its_completions(self):
        """The failure this exists to prevent: one PR passes through quickly
        while five pile up behind it, and the stage reports the quick one."""
        data = snapshot(
            [pr(1, [(NOW - timedelta(hours=4), "awaiting-review"),
                    (NOW - timedelta(hours=3), "ready-to-merge")])]          # 1h, done
            + [pr(n, [(NOW - timedelta(hours=20), "awaiting-review")])       # still waiting
               for n in range(2, 7)]
        )
        stage = next(s for s in health.analyse(data, 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertEqual(stage["depth"], 5)
        self.assertIsNone(stage["median_dwell_hours"])
        self.assertEqual(stage["median_waiting_hours"], 20.0)

    def test_a_spell_already_under_way_when_the_window_opened_is_not_in_it(self):
        """It was never at risk at the ages below the one it had when the
        window opened, so counting it from zero would credit it with time in
        which nothing could have been observed. Dwell takes an inception
        cohort; the departure *rate* still counts it, having seen it leave."""
        data = snapshot([
            pr(1, [(NOW - timedelta(hours=100), "awaiting-review"),
                   (NOW - timedelta(hours=23), "ready-to-merge")]),   # 77h, began long before
            pr(2, [(NOW - timedelta(hours=6), "awaiting-review"),
                   (NOW - timedelta(hours=4), "ready-to-merge")]),    # 2h, began inside
        ])
        stage = next(s for s in health.analyse(data, 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertEqual(stage["median_dwell_hours"], 2.0)
        self.assertEqual(stage["left_count"], 2)

    def test_a_baseline_spell_is_censored_at_the_baseline_end_not_resolved_later(self):
        """What happened after the baseline closed is look-ahead: the estimate
        has to be the one that period could have supported at the time."""
        data = snapshot([
            # Begins well inside the baseline, still running 13 days later.
            pr(1, [(NOW - timedelta(days=14), "awaiting-review"),
                   (NOW - timedelta(hours=2), "ready-to-merge")]),
        ])
        stage = next(s for s in health.analyse(data, 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        # Censored at baseline_end, so no completed baseline spell to average.
        self.assertEqual(stage["baseline_dwell_completions"], 0)
        self.assertIsNone(stage["baseline_median_dwell_hours"])

    def test_departures_do_not_vouch_for_a_dwell_median_they_are_not_part_of(self):
        """Three spells begin before the baseline and end inside it, and one
        begins inside. The departure count reads four; the median rests on the
        one, and `baseline_dwell_completions` is what says so."""
        began_before = [
            pr(n, [(NOW - timedelta(days=20), "awaiting-review"),
                   (NOW - timedelta(days=10), "ready-to-merge")],
               state="MERGED", merged=NOW - timedelta(days=9))
            for n in range(3)
        ]
        began_inside = pr(99, [(NOW - timedelta(days=5), "awaiting-review"),
                               (NOW - timedelta(days=5) + timedelta(hours=7), "ready-to-merge")],
                          state="MERGED", merged=NOW - timedelta(days=4))
        stage = next(s for s in health.analyse(snapshot(began_before + [began_inside]),
                                               24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertEqual(stage["baseline_left_count"], 4)
        self.assertEqual(stage["baseline_dwell_completions"], 1)

    def test_the_occupants_of_a_stage_are_described_not_just_the_oldest(self):
        """Dwell times describe spells that ended, and a filling stage holds
        exactly the spells that have not. `oldest_waiting_hours` is one PR, so
        on its own it cannot separate a backlog from a single straggler."""
        data = snapshot([
            pr(1, [(NOW - timedelta(hours=2), "awaiting-review")]),
            pr(2, [(NOW - timedelta(hours=6), "awaiting-review")]),
            pr(3, [(NOW - timedelta(hours=10), "awaiting-review")]),
        ])
        stage = next(s for s in health.analyse(data, 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertEqual(stage["median_waiting_hours"], 6.0)
        self.assertEqual(stage["oldest_waiting_hours"], 10.0)

    def test_waiting_percentiles_say_how_much_of_the_stage_they_describe(self):
        """A pull request the audit moved to another stage is counted in that
        stage's depth, but its old label's clock says nothing about how long it
        has been in the new one, so it contributes no waiting age. The reader
        has to be able to see that the percentiles cover part of the stage."""
        data = snapshot([
            pr(1, [(NOW - timedelta(hours=8), "awaiting-CI")]),
            pr(2, [(NOW - timedelta(hours=3), "awaiting-review")]),   # drifts
        ])
        data["merge_readiness"] = {"prs": {
            "2": {"eligible": False, "category": "awaiting-CI", "reason": "head moved"},
        }}
        stage = next(s for s in health.analyse(data, 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-CI")
        self.assertEqual(stage["depth"], 2)
        self.assertEqual(stage["waiting_count"], 1)
        self.assertEqual(stage["median_waiting_hours"], 8.0)

    def test_an_empty_stage_has_no_waiting_percentiles_rather_than_zero(self):
        stage = next(s for s in health.analyse(snapshot([]), 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertIsNone(stage["median_waiting_hours"])
        self.assertIsNone(stage["p90_waiting_hours"])

    def test_author_owned_stages_are_marked_as_such(self):
        result = health.analyse(snapshot([]), 24, 24 * 14, NOW)
        owned = {s["stage"]: s["owned_by_project"] for s in result["stages"]}
        self.assertFalse(owned["ci-failed"])
        self.assertFalse(owned["awaiting-author"])
        self.assertTrue(owned["awaiting-review"])


class CauseTests(unittest.TestCase):
    """Why throughput fell: a stage backing up, a thinner intake, both, or an
    honest admission that the queue does not explain it."""

    def base(self, **overrides):
        result = {"merged_per_hour": 1.0, "baseline_merged_per_hour": 5.0,
                  "baseline_merged_count": 100, "stages": [],
                  "opened_per_hour": 5.0, "baseline_opened_per_hour": 5.0,
                  "baseline_opened_count": 100}
        result.update(overrides)
        return result

    def stage(self, name, **kw):
        item = {"stage": name, "owned_by_project": name not in health.STATE_AUTHOR_ACTION,
                "depth": 0, "oldest_waiting_hours": 0.0, "median_waiting_hours": None,
                "p90_waiting_hours": None, "entered_per_hour": 0.0,
                "left_per_hour": 0.0, "baseline_median_dwell_hours": None,
                "baseline_left_count": 20, "baseline_dwell_completions": 20,
                "baseline_entered_per_hour": 0.0}
        item.update(kw)
        return item

    def test_healthy_throughput_names_no_cause(self):
        self.assertIsNone(health.find_cause(
            self.base(merged_per_hour=5.0, baseline_merged_per_hour=5.0)))

    def test_thin_intake_is_itself_the_answer(self):
        """Fewer merges because fewer arrived is a cause, not the absence of
        one, and it wants the opposite response to a stuck queue: adding review
        capacity does nothing about a week when nobody opened anything."""
        found = health.find_cause(self.base(opened_per_hour=0.5, anomalies=[]))
        self.assertEqual(found["kind"], "intake")
        self.assertIn("fewer pull requests are arriving", found["why"])

    def test_a_stuck_stage_and_thin_intake_are_both_reported(self):
        found = health.find_cause(self.base(
            opened_per_hour=0.5,
            stages=[self.stage("awaiting-review", depth=10,
                               entered_per_hour=3.0, left_per_hour=0.5)]))
        self.assertEqual(found["kind"], "stage")
        self.assertIn("Arrivals are also down", found["why"])

    def test_an_unexplained_fall_says_so_rather_than_blaming_a_stage(self):
        found = health.find_cause(self.base(anomalies=[]))
        self.assertEqual(found["kind"], "unexplained")

    def test_thin_intake_needs_a_baseline_to_claim_it(self):
        found = health.find_cause(self.base(
            opened_per_hour=0.5, baseline_opened_count=1, anomalies=[]))
        self.assertEqual(found["kind"], "unexplained")

    def test_a_stage_filling_faster_than_it_drains_wins(self):
        result = self.base(stages=[
            self.stage("awaiting-CI", depth=50, entered_per_hour=1.0, left_per_hour=1.0),
            self.stage("awaiting-review", depth=10, entered_per_hour=3.0, left_per_hour=0.5),
        ])
        self.assertEqual(health.find_cause(result)["stage"], "awaiting-review")

    def test_a_deep_but_draining_stage_is_not_the_bottleneck(self):
        """Depth alone means nothing: a queue can be long and perfectly healthy."""
        result = self.base(stages=[
            self.stage("awaiting-CI", depth=200, entered_per_hour=2.0, left_per_hour=2.5),
            self.stage("ready-to-merge", depth=3, entered_per_hour=1.0, left_per_hour=0.2),
        ])
        self.assertEqual(health.find_cause(result)["stage"], "ready-to-merge")

    def test_no_stage_is_named_when_none_is_misbehaving(self):
        """Throughput can fall because nothing arrived. Naming a culprit anyway
        is how a heuristic becomes an oracle that is always confidently wrong."""
        result = self.base(stages=[
            self.stage("awaiting-CI", depth=5, entered_per_hour=1.0, left_per_hour=1.0,
                       oldest_waiting_hours=2.0, baseline_median_dwell_hours=3.0),
            self.stage("awaiting-review", depth=9, entered_per_hour=0.5, left_per_hour=0.6,
                       oldest_waiting_hours=4.0, baseline_median_dwell_hours=5.0),
        ])
        self.assertIsNone(health.find_cause(result)["stage"])

    def test_a_dwell_median_resting_on_too_few_spells_is_not_judged(self):
        """The gate has to count the cohort the median came from. Departures
        are a different set: spells that began before the baseline and ended
        inside it leave from it without ever joining its inception cohort, so
        they would vouch for a median resting on one observation."""
        result = self.base(stages=[
            self.stage("awaiting-review", depth=2, entered_per_hour=0.1, left_per_hour=0.1,
                       oldest_waiting_hours=500.0, baseline_median_dwell_hours=1.0,
                       baseline_left_count=40, baseline_dwell_completions=1),
        ])
        self.assertIsNone(health.find_cause(result)["stage"])

    def test_a_stalled_stage_is_named_even_without_growth(self):
        result = self.base(stages=[
            self.stage("ready-to-merge", depth=4, entered_per_hour=0.1, left_per_hour=0.1,
                       oldest_waiting_hours=100.0, baseline_median_dwell_hours=2.0),
        ])
        found = health.find_cause(result)
        self.assertEqual(found["stage"], "ready-to-merge")
        self.assertIn("normal dwell", found["why"])

    def test_a_thin_baseline_reports_insufficient_data_not_health(self):
        """Zero merges over the baseline made the old gate read 0 >= 0 and call
        an empty repository healthy."""
        found = health.find_cause(self.base(
            merged_per_hour=0.0, baseline_merged_per_hour=0.0, baseline_merged_count=0))
        self.assertEqual(found["kind"], "insufficient_data")

    def test_a_stage_with_too_few_completions_is_not_judged_on_dwell(self):
        result = self.base(stages=[
            self.stage("awaiting-review", depth=2, entered_per_hour=0.1, left_per_hour=0.1,
                       oldest_waiting_hours=500.0, baseline_median_dwell_hours=1.0,
                       baseline_left_count=1, baseline_dwell_completions=1),
        ])
        self.assertIsNone(health.find_cause(result)["stage"])

    def test_stages_waiting_on_the_author_are_never_blamed(self):
        """The project cannot fix these, so naming one would point effort at
        exactly the wrong place."""
        result = self.base(stages=[
            self.stage("ci-failed", depth=99, entered_per_hour=9.0, left_per_hour=0.1),
            self.stage("awaiting-author", depth=99, entered_per_hour=9.0, left_per_hour=0.1),
        ])
        self.assertIsNone(health.find_cause(result)["stage"])

    def test_an_empty_stage_is_not_a_bottleneck(self):
        result = self.base(stages=[self.stage("awaiting-review", depth=0,
                                              entered_per_hour=0.0, left_per_hour=0.0)])
        self.assertIsNone(health.find_cause(result)["stage"])


class TimingTests(unittest.TestCase):
    def test_replay_measures_the_snapshot_as_it_was(self):
        """Otherwise every open interval gains however long the file sat on disk."""
        old = NOW - timedelta(days=30)
        data = snapshot([pr(1, [(old - timedelta(hours=2), "awaiting-review")])])
        data["fetched_at"] = iso(old)
        stage = next(s for s in health.analyse(data, 24, 24 * 14)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertAlmostEqual(stage["oldest_waiting_hours"], 2.0, places=3)

    def test_the_baseline_excludes_the_recent_window(self):
        """A baseline containing the window it is compared against is not a
        comparison."""
        recent = NOW - timedelta(hours=2)
        data = snapshot([pr(1, [(recent, "awaiting-review")],
                            state="MERGED", merged=recent + timedelta(minutes=1))])
        result = health.analyse(data, 24, 24 * 14, NOW)
        self.assertGreater(result["merged_per_hour"], 0)
        self.assertEqual(result["baseline_merged_count"], 0)

    def test_a_nonpositive_window_is_rejected(self):
        with self.assertRaises(ValueError):
            health.analyse(snapshot([]), 0, 24, NOW)


class DepthTests(unittest.TestCase):
    def test_depth_comes_from_current_labels_not_the_last_event(self):
        """A PR whose lifecycle label was removed has left that stage."""
        item = pr(1, [(NOW - timedelta(hours=5), "awaiting-review")])
        item["labels"] = []
        stage = next(s for s in health.analyse(snapshot([item]), 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertEqual(stage["depth"], 0)

    def test_an_open_pr_with_no_lifecycle_label_is_counted_and_reported(self):
        """Silently omitting it would make the depths quietly not add up."""
        item = pr(1, [])
        item["labels"] = []
        result = health.analyse(snapshot([item]), 24, 24 * 14, NOW)
        self.assertEqual(result["open_prs_without_a_lifecycle_label"], 1)

    def test_drafts_do_not_count_towards_depth(self):
        item = pr(1, [(NOW - timedelta(hours=5), "awaiting-review")])
        item["is_draft"] = True
        stage = next(s for s in health.analyse(snapshot([item]), 24, 24 * 14, NOW)["stages"]
                     if s["stage"] == "awaiting-review")
        self.assertEqual(stage["depth"], 0)


class RoundingTests(unittest.TestCase):
    def test_comparisons_run_on_unrounded_values(self):
        """One event in a fortnight rounds to a rate of exactly zero, which
        silently changes which branch every threshold takes."""
        result = health.analyse(snapshot([]), 24, 24 * 14, NOW)
        self.assertIn("stages", health.rounded(result))
        raw = {"merged_per_hour": 0.0044, "baseline_merged_per_hour": 0.0, "stages": []}
        self.assertNotEqual(round(raw["merged_per_hour"], 2), raw["merged_per_hour"])


class ReportTests(unittest.TestCase):
    def test_report_renders_and_names_the_author_owned_marker(self):
        result = health.analyse(snapshot([
            pr(1, [(NOW - timedelta(hours=2), "awaiting-review")]),
        ]), 24, 24 * 14, NOW)
        text = health.report(health.rounded(result))
        self.assertIn("awaiting-review", text)
        self.assertIn("waiting on the contributor", text)




class AgreementTests(unittest.TestCase):
    """The charts and this report read the same timelines and must not disagree.

    They did, by nineteen hours: one treated a ci-failed to awaiting-author swap
    as a fresh wait and the other continued the spell. That is the whole reason
    the lifecycle rules now live in one module.
    """

    def swapped_author_labels(self):
        return pr(1, [
            (NOW - timedelta(hours=20), "ci-failed"),
            (NOW - timedelta(hours=1), "awaiting-author"),
        ])

    def test_waiting_time_matches_the_chart_generator(self):
        import pr_stats_graphs as stats

        item = self.swapped_author_labels()
        theirs = stats.queue_age_metrics([item], NOW)["awaiting_author_hours"][0]
        stages = health.analyse(snapshot([item]), 24, 24 * 14, NOW)["stages"]
        mine = max(s["oldest_waiting_hours"] for s in stages)
        self.assertAlmostEqual(theirs, mine, places=3)
        self.assertAlmostEqual(theirs, 20.0, places=3)

    def test_swapping_sibling_review_labels_continues_the_cycle(self):
        item = pr(2, [
            (NOW - timedelta(hours=12), "awaiting-review"),
            (NOW - timedelta(hours=2), "review-in-progress"),
        ])
        stages = health.analyse(snapshot([item]), 24, 24 * 14, NOW)["stages"]
        self.assertAlmostEqual(max(s["oldest_waiting_hours"] for s in stages), 12.0, places=3)

    def test_a_push_back_to_ci_does_start_a_fresh_wait(self):
        """Only sibling labels join; anything else is genuinely a new spell."""
        item = pr(3, [
            (NOW - timedelta(hours=30), "awaiting-author"),
            (NOW - timedelta(hours=3), "awaiting-CI"),
        ])
        stages = health.analyse(snapshot([item]), 24, 24 * 14, NOW)["stages"]
        self.assertAlmostEqual(max(s["oldest_waiting_hours"] for s in stages), 3.0, places=3)


class BuildingQueueTests(unittest.TestCase):
    """A stage filling faster than it drains is worth reporting before merges
    fall. Gating it on throughput meant the report said "no stage is backing up"
    while awaiting-review grew from 45 to 70 and took in 23.5/h against 20.9/h
    out, because throughput was still at 83% of baseline."""

    def result_with_a_building_stage(self, merged, baseline):
        return {
            "merged_per_hour": merged, "baseline_merged_per_hour": baseline,
            "baseline_merged_count": 100, "opened_per_hour": 5.0,
            "baseline_opened_per_hour": 5.0, "baseline_opened_count": 100,
            "window_hours": 24.0, "baseline_hours": 336.0, "open_prs": 100,
            "opened_count": 120, "merged_count": 90,
            "open_prs_without_a_lifecycle_label": 0,
            "repo": "x", "generated_at": "2026-08-25T00:00:00Z",
            "stages": [{
                "stage": "awaiting-review", "owned_by_project": True, "depth": 70,
                "oldest_waiting_hours": 342.0, "median_waiting_hours": 6.0,
                "p90_waiting_hours": 90.0, "entered_per_hour": 23.5,
                "left_per_hour": 20.9, "baseline_entered_per_hour": 20.0,
                "baseline_left_per_hour": 20.0, "left_count": 500,
                "baseline_left_count": 5000, "baseline_dwell_completions": 5000,
                "dwell_completions": 500, "median_dwell_hours": 2.0,
                "baseline_median_dwell_hours": 1.0,
            }],
        }

    def test_a_building_stage_is_reported_while_throughput_still_holds(self):
        r = self.result_with_a_building_stage(3.92, 4.75)      # 83% of baseline
        r["anomalies"] = health.anomalies(r)
        r["cause"] = health.find_cause(r)
        self.assertIsNone(r["cause"])
        self.assertEqual([a["stage"] for a in r["anomalies"]], ["awaiting-review"])
        text = health.report(health.rounded(r))
        self.assertIn("the queue is building", text)
        self.assertNotIn("no stage is backing up", text)

    def test_a_genuinely_quiet_queue_still_reports_normal(self):
        r = self.result_with_a_building_stage(4.75, 4.75)
        r["stages"][0].update(entered_per_hour=20.0, left_per_hour=20.0,
                              oldest_waiting_hours=1.0)
        r["anomalies"] = health.anomalies(r)
        r["cause"] = health.find_cause(r)
        self.assertIn("no stage is backing up", health.report(health.rounded(r)))


class VerifiedReadiness(unittest.TestCase):
    def data(self, category="ready-to-merge", eligible=True, queue=None):
        data = snapshot([pr(1, [(NOW - timedelta(hours=3), "ready-to-merge")])])
        data["merge_readiness"] = {
            "prs": {"1": {"number": 1, "category": category, "eligible": eligible,
                            "reason": "gate reason"}},
            "queue": queue or {"known": True, "numbers": [], "reservation_holder": None}}
        return data

    def test_ready_label_does_not_override_a_gate_refusal(self):
        result = health.analyse(self.data("awaiting-review", False), 24, 336, NOW)
        stages = {s["stage"]: s for s in result["stages"]}
        self.assertEqual(stages["ready-to-merge"]["depth"], 0)
        self.assertEqual(stages["ready-to-merge"]["label_depth"], 1)
        self.assertEqual(stages["awaiting-review"]["depth"], 1)
        self.assertEqual(result["merge_readiness"]["verified_eligible"], 0)
        self.assertEqual(len(result["merge_readiness"]["label_drift"]), 1)

    def test_label_drift_does_not_transfer_historical_wait(self):
        result = health.analyse(self.data("awaiting-review", False), 24, 336, NOW)
        stage = next(s for s in result["stages"] if s["stage"] == "awaiting-review")
        self.assertEqual(stage["oldest_waiting_hours"], 0)

    def test_new_stage_migration_is_not_a_throughput_anomaly(self):
        result = health.analyse(self.data("needs-human-review", False), 24, 336, NOW)
        stage = next(s for s in result["stages"] if s["stage"] == "needs-human-review")
        stage.update(depth=20, entered_per_hour=10, left_per_hour=0)
        self.assertFalse(any(a["stage"] == "needs-human-review" for a in health.anomalies(result)))

    def test_closed_during_audit_is_not_blocked_or_drifted(self):
        summary = health.readiness_summary(self.data(None, False))
        self.assertEqual(summary["blocked"], 0)
        self.assertEqual(summary["label_drift"], [])

    def test_human_review_is_a_separate_stage(self):
        result = health.analyse(self.data("needs-human-review", False), 24, 336, NOW)
        stages = {s["stage"]: s for s in result["stages"]}
        self.assertEqual(stages["needs-human-review"]["depth"], 1)
        self.assertEqual(stages["ready-to-merge"]["depth"], 0)

    def test_reservation_preserves_eligibility_and_explains_queue_delay(self):
        queue = {"known": True, "numbers": [9], "reservation_holder": 9}
        result = health.analyse(self.data(queue=queue), 24, 336, NOW)
        summary = result["merge_readiness"]
        self.assertEqual(summary["verified_eligible"], 1)
        self.assertEqual(summary["eligible_not_queued"], 1)
        self.assertEqual(summary["eligible_queued"], 0)
        result.update(baseline_merged_count=20, baseline_merged_per_hour=1, merged_per_hour=0)
        self.assertNotEqual((health.find_cause(result) or {}).get("kind"), "reservation")
        self.assertIn("queue reservation: pin-moving #9", health.report(result))

    def test_queued_and_not_queued_are_distinguished(self):
        queue = {"known": True, "numbers": [1], "reservation_holder": None}
        summary = health.readiness_summary(self.data(queue=queue))
        self.assertEqual(summary["eligible_queued"], 1)
        self.assertEqual(summary["eligible_not_queued"], 0)

    def test_failed_read_and_old_snapshot_are_unknown_not_mergeable(self):
        for data in (self.data(None, None), snapshot([pr(1, [(NOW, "ready-to-merge")])])):
            result = health.analyse(data, 24, 336, NOW)
            self.assertEqual(result["merge_readiness"]["unverified_ready"], 1)
            self.assertEqual(result["merge_readiness"]["verified_eligible"], 0)
            ready = next(s for s in result["stages"] if s["stage"] == "ready-to-merge")
            self.assertIsNone(ready["depth"])
            result.update(baseline_merged_count=20, baseline_merged_per_hour=1, merged_per_hour=0)
            self.assertEqual(health.find_cause(result)["kind"], "unverified")
            self.assertIn("not evidence of merge capacity", health.report(result))

    def test_missed_label_update_does_not_hide_an_eligible_pr(self):
        data = self.data()
        data["prs"][0]["labels"] = ["awaiting-review"]
        result = health.analyse(data, 24, 336, NOW)
        self.assertEqual(result["merge_readiness"]["labelled_ready"], 0)
        self.assertEqual(result["merge_readiness"]["verified_eligible"], 1)


if __name__ == "__main__":
    unittest.main()
