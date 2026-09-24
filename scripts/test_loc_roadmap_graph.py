#!/usr/bin/env python3
"""Unit tests for the per-roadmap line chart."""

import datetime as dt
import unittest

import loc_roadmap_graph as graph


def pr(number, title, area, additions, deletions, day="2026-07-01"):
    return {
        "number": number,
        "title": title,
        "labels": [{"name": area}],
        "mergedAt": f"{day}T12:00:00Z",
        "additions": additions,
        "deletions": deletions,
    }


class RoadmapSeries(unittest.TestCase):
    def test_excludes_maintenance_even_with_area_label(self):
        prs = [
            pr(1, "feat: add theorem", "roadmap/PDE", 20, 2),
            pr(2, "refactor(PDE): share proof", "roadmap/PDE", 100, 5),
            pr(3, "fix: repair theorem", "roadmap/PDE", 10, 1),
        ]
        dates, order, series, totals = graph.build_series(prs, today=dt.date(2026, 7, 2))
        self.assertEqual(dates, ["2026-07-01"])
        self.assertEqual(order, ["roadmap/PDE"])
        self.assertEqual(series, {"roadmap/PDE": [18]})
        self.assertEqual(totals, {"roadmap/PDE": 18})

    def test_still_excludes_none_and_unknown(self):
        prs = [
            pr(1, "feat: add theorem", "roadmap/none", 10, 0),
            pr(2, "feat: add another theorem", "roadmap/Unknown", 10, 0),
        ]
        self.assertEqual(graph.build_series(prs), ([], [], {}, {}))

    def test_rejects_negative_cumulative_area(self):
        prs = [
            pr(1, "feat: remove obsolete API", "roadmap/PDE", 0, 5),
        ]
        with self.assertRaisesRegex(ValueError, "negative cumulative"):
            graph.build_series(prs)


class TruncationTest(unittest.TestCase):
    """A cumulative chart cannot survive losing its oldest rows.

    `gh pr list` returns at most --limit results, newest first, and reports nothing when it
    stops there. The limit was 2000 while the repository had 5072 merged pull requests, so every
    band silently began 3000 pull requests too late and the chart looked entirely plausible.
    """

    def test_a_full_result_is_refused_rather_than_drawn(self):
        prs = [pr(n, "feat: add theorem", "roadmap/PDE", 1, 0)
               for n in range(graph.MERGED_PR_CEILING)]
        with self.assertRaisesRegex(RuntimeError, "ceiling"):
            graph.check_complete(prs)

    def test_a_short_result_is_accepted(self):
        self.assertIsNone(graph.check_complete([pr(1, "feat: x", "roadmap/PDE", 1, 0)]))

    def test_the_ceiling_is_well_clear_of_the_project(self):
        # The point of the ceiling is to stop a runaway query, not to bound the project. If it
        # ever sits near the real number of merged pull requests, the guard above starts firing
        # on healthy runs instead of on a bug.
        self.assertGreaterEqual(graph.MERGED_PR_CEILING, 50_000)


class CollapseTail(unittest.TestCase):
    """Bundling the long tail of roadmaps into a single `Other` band."""

    def series_of(self, count):
        """`count` roadmaps merging on two days, each smaller than the last."""
        prs = []
        for index in range(count):
            for number, day in ((index * 2 + 1, "2026-06-01"), (index * 2 + 2, "2026-06-02")):
                prs.append(pr(number, "feat: add theorem", f"roadmap/Area{index:02d}",
                              (count - index) * 100, 0, day))
        return graph.build_series(prs, today=dt.date(2026, 6, 3))

    def test_leaves_a_short_list_untouched(self):
        dates, order, series, totals = self.series_of(graph.LEGEND_LIMIT)

        collapsed, _, _, omitted = graph.collapse_tail(order, series, totals)

        self.assertEqual(omitted, 0)
        self.assertEqual(collapsed, order)
        self.assertNotIn(graph.OTHER, collapsed)

    def test_bundles_the_tail_and_keeps_the_total(self):
        dates, order, series, totals = self.series_of(graph.LEGEND_LIMIT + 5)

        collapsed, bundled_series, bundled_totals, omitted = graph.collapse_tail(
            order, series, totals)

        self.assertEqual(omitted, 5)
        self.assertEqual(len(collapsed), graph.LEGEND_LIMIT + 1)
        self.assertEqual(bundled_totals[graph.OTHER],
                         sum(totals[a] for a in order[graph.LEGEND_LIMIT:]))
        # Nothing is lost and nothing is double counted.
        self.assertEqual(sum(bundled_totals[a] for a in collapsed), sum(totals.values()))
        # The band is the tail summed at every point, not just at the end.
        self.assertEqual(
            bundled_series[graph.OTHER],
            [sum(series[a][i] for a in order[graph.LEGEND_LIMIT:]) for i in range(len(dates))])

    def test_other_sits_on_top_however_big_it_is(self):
        # Every bundled roadmap is tiny, so `Other` is far smaller than the bands it covers;
        # it still goes last. The reverse case matters more -- a huge `Other` must not sort
        # itself down into the middle of the stack -- and both are the same rule.
        dates, order, series, totals = self.series_of(graph.LEGEND_LIMIT + 3)

        collapsed, _, bundled_totals, _ = graph.collapse_tail(order, series, totals)

        self.assertEqual(collapsed[-1], graph.OTHER)
        self.assertLess(bundled_totals[graph.OTHER], bundled_totals[collapsed[0]])

    def test_the_chart_reports_the_true_roadmap_count(self):
        import tempfile

        dates, order, series, totals = self.series_of(graph.LEGEND_LIMIT + 5)
        collapsed, bundled_series, bundled_totals, omitted = graph.collapse_tail(
            order, series, totals)

        with tempfile.NamedTemporaryFile(suffix=".svg") as handle:
            graph.render(dates, collapsed, bundled_series, bundled_totals,
                         "Per roadmap", handle.name, omitted)
            svg = open(handle.name).read()

        # Twenty roadmaps drawn as sixteen bands must still say twenty.
        self.assertIn(f"across {graph.LEGEND_LIMIT + 5} roadmaps", svg)
        self.assertIn("Other (5 roadmaps)", svg)
        self.assertEqual(svg.count("<polygon"), graph.LEGEND_LIMIT + 1)

    def test_short_leaves_a_non_label_alone(self):
        self.assertEqual(graph.short("roadmap/PDE"), "PDE")
        self.assertEqual(graph.short(graph.OTHER), graph.OTHER)

    def test_exactly_one_over_the_limit_collapses(self):
        _, order, series, totals = self.series_of(graph.LEGEND_LIMIT + 1)

        collapsed, _, collapsed_totals, omitted = graph.collapse_tail(order, series, totals)

        self.assertEqual(omitted, 1)
        self.assertEqual(collapsed[-1], graph.OTHER)
        self.assertEqual(collapsed_totals[graph.OTHER], totals[order[-1]])

    def test_the_returned_dictionaries_hold_exactly_the_returned_order(self):
        """So `sum(totals.values())` cannot quietly count the bundled tail twice."""
        _, order, series, totals = self.series_of(graph.LEGEND_LIMIT + 5)

        collapsed, collapsed_series, collapsed_totals, _ = graph.collapse_tail(
            order, series, totals)

        self.assertEqual(set(collapsed), set(collapsed_totals))
        self.assertEqual(set(collapsed), set(collapsed_series))
        self.assertEqual(sum(collapsed_totals.values()), sum(totals.values()))

    def test_it_leaves_the_caller_s_data_alone(self):
        _, order, series, totals = self.series_of(graph.LEGEND_LIMIT + 5)
        before_order, before_totals = list(order), dict(totals)

        graph.collapse_tail(order, series, totals)

        self.assertEqual(order, before_order)
        self.assertEqual(totals, before_totals)
        self.assertNotIn(graph.OTHER, totals)

    def test_the_sentinel_never_reaches_the_svg_and_the_svg_parses(self):
        import tempfile
        import xml.etree.ElementTree as ET

        dates, order, series, totals = self.series_of(graph.LEGEND_LIMIT + 5)
        collapsed, collapsed_series, collapsed_totals, omitted = graph.collapse_tail(
            order, series, totals)

        with tempfile.NamedTemporaryFile(suffix=".svg") as handle:
            graph.render(dates, collapsed, collapsed_series, collapsed_totals,
                         "Per roadmap", handle.name, omitted)
            svg = open(handle.name).read()

        self.assertNotIn(graph.OTHER, svg)
        ET.fromstring(svg)


class CompletedDaysTest(unittest.TestCase):
    def test_yesterday_is_in_and_today_is_out(self):
        prs = [
            pr(1, "feat: add theorem", "roadmap/PDE", 10, 0, day="2026-07-10"),
            pr(2, "feat: add another", "roadmap/PDE", 20, 0, day="2026-07-11"),
        ]

        dates, _, _, totals = graph.build_series(prs, today=dt.date(2026, 7, 11))

        self.assertEqual(dates, ["2026-07-10"])
        self.assertEqual(totals, {"roadmap/PDE": 10})

    def test_an_offset_timestamp_is_filed_by_its_utc_day(self):
        """23:00 on the 10th in UTC-5 is the 11th in UTC, and the cutoff is a UTC one."""
        late = {"number": 1, "title": "feat: add theorem",
                "labels": [{"name": "roadmap/PDE"}],
                "mergedAt": "2026-07-10T23:00:00-05:00",
                "additions": 10, "deletions": 0}

        dates, _, _, _ = graph.build_series([late], today=dt.date(2026, 7, 12))

        self.assertEqual(dates, ["2026-07-11"])

    def test_the_series_reaches_the_last_completed_day(self):
        prs = [pr(1, "feat: add theorem", "roadmap/PDE", 10, 0, day="2026-07-10")]

        dates, _, series, _ = graph.build_series(prs, today=dt.date(2026, 7, 14))

        self.assertEqual(dates, ["2026-07-10", "2026-07-11", "2026-07-12", "2026-07-13"])
        self.assertEqual(series["roadmap/PDE"], [10, 10, 10, 10])

    def test_merges_only_today_leave_an_empty_series(self):
        prs = [pr(1, "feat: add theorem", "roadmap/PDE", 10, 0, day="2026-07-12")]

        self.assertEqual(graph.build_series(prs, today=dt.date(2026, 7, 12)),
                         ([], [], {}, {}))


if __name__ == "__main__":
    unittest.main()
