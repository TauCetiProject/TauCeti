#!/usr/bin/env python3
"""Estimate serial bors capacity and CI cost from observed arrivals and build times.

The simulator starts one batch from all approvals accumulated while the previous
batch ran. A failing batch is tested recursively by halves. It reports the CI
minutes consumed per merged PR and whether departures keep pace with arrivals.
Per-PR integration failure is a scenario input, because a failed PR-head build
does not estimate the failure rate of already-approved PRs in a combined batch.
"""
import argparse
import json
import math
import random
import statistics
from collections import deque


def exponential_arrivals(rate_per_day, days, rng):
    minute = 0.0
    out = []
    while minute < days * 1440:
        minute += rng.expovariate(rate_per_day / 1440)
        if minute < days * 1440:
            out.append(minute)
    return out


def replay_arrivals(week_minutes, scale, days, rng):
    """Repeat the observed weekly shape, scaling each event with local jitter."""
    out = []
    for week in range(math.ceil(days / 7)):
        for minute in week_minutes:
            copies = int(scale) + (rng.random() < scale % 1)
            for _ in range(copies):
                shifted = week * 7 * 1440 + minute
                if scale != 1:
                    shifted += rng.uniform(-30, 30)
                if 0 <= shifted < days * 1440:
                    out.append(shifted)
    return sorted(out)


def simulate(rate_per_day, durations, failure_rate, cap, *, days=28,
             duration_growth=0.0, seed=1, arrival_template=None, rate_scale=1):
    rng = random.Random(seed)
    arrivals = (replay_arrivals(arrival_template, rate_scale, days, rng)
                if arrival_template else exponential_arrivals(rate_per_day * rate_scale, days, rng))
    bad = [rng.random() < failure_rate for _ in arrivals]
    pending = deque()
    next_arrival = 0
    now = 0.0
    ci_minutes = 0.0
    completed = []
    rejected = 0
    batch_sizes = []
    horizon = days * 1440

    def admit():
        nonlocal next_arrival
        while next_arrival < len(arrivals) and arrivals[next_arrival] <= now:
            pending.append(next_arrival)
            next_arrival += 1

    def test_group(group):
        nonlocal now, ci_minutes, rejected
        duration = rng.choice(durations) * (1 + duration_growth * math.log2(len(group)))
        now += duration
        ci_minutes += duration
        admit()
        if not any(bad[i] for i in group):
            completed.extend((i, now) for i in group)
        elif len(group) == 1:
            rejected += 1
        else:
            half = len(group) // 2
            test_group(group[:half])
            test_group(group[half:])

    while now < horizon:
        admit()
        if not pending:
            if next_arrival >= len(arrivals):
                break
            now = arrivals[next_arrival] + 10 / 60  # bors batch delay
            admit()
        group = [pending.popleft() for _ in range(min(cap, len(pending)))]
        batch_sizes.append(len(group))
        test_group(group)

    # A growing backlog at the end of the observation window means the
    # configuration cannot keep up. Compare arrivals and terminal decisions,
    # and expose the queue depth so short-window effects remain visible.
    total = len(arrivals)
    unfinished = total - len(completed) - rejected
    waits = [done - arrivals[i] for i, done in completed]
    return {
        "cap": cap,
        "rate_per_day": rate_per_day * rate_scale,
        "failure_rate": failure_rate,
        "arrivals": total,
        "merged": len(completed),
        "rejected": rejected,
        "backlog": unfinished,
        "backlog_fraction": round(unfinished / total, 4) if total else 0,
        "ci_minutes_per_merge": round(ci_minutes / len(completed), 3) if completed else None,
        "mean_wait_minutes": round(statistics.mean(waits), 1) if waits else None,
        "mean_batch_size": round(statistics.mean(batch_sizes), 1) if batch_sizes else None,
        "stable": unfinished <= max(10, total * 0.01),
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--observations", help="JSON with admissions_per_day and ci_minutes samples")
    ap.add_argument("--admissions-per-day", type=float, default=192)
    ap.add_argument("--ci-minutes", type=float, default=13.4)
    ap.add_argument("--failure-rates", default="0.001,0.003,0.01,0.03")
    ap.add_argument("--rate-scales", default="1,10")
    ap.add_argument("--caps", default="1,2,4,8,16,32,64,128,256")
    ap.add_argument("--days", type=int, default=28)
    ap.add_argument("--duration-growth", type=float, default=0.0,
                    help="fractional CI duration increase for each batch-size doubling")
    args = ap.parse_args()
    obs = json.load(open(args.observations)) if args.observations else {}
    rate = obs.get("admissions_per_day", args.admissions_per_day)
    durations = obs.get("ci_minutes", [args.ci_minutes])
    template = obs.get("arrival_minutes_in_week")
    if rate <= 0 or not durations or min(durations) <= 0:
        ap.error("arrival rate and CI durations must be positive")
    for scale in map(float, args.rate_scales.split(",")):
        for failure in map(float, args.failure_rates.split(",")):
            rows = [simulate(rate, durations, failure, cap, days=args.days,
                             duration_growth=args.duration_growth, seed=20260925,
                             arrival_template=template, rate_scale=scale)
                    for cap in map(int, args.caps.split(","))]
            stable = [row for row in rows if row["stable"]]
            # Costs within 1% are indistinguishable for this approximate model;
            # choose the smaller cap rather than chasing Monte Carlo noise.
            floor = min((row["ci_minutes_per_merge"] for row in stable), default=None)
            near_minimum = ([row for row in stable if row["ci_minutes_per_merge"] <= floor * 1.01]
                            if floor is not None else [])
            best = min(near_minimum, key=lambda row: row["cap"]) if near_minimum else None
            print(json.dumps({"scale": scale, "failure_rate": failure,
                              "recommended_cap": best["cap"] if best else None,
                              "rows": rows}))


if __name__ == "__main__":
    main()
