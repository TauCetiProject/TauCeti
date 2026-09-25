#!/usr/bin/env python3
from bors_capacity import replay_arrivals, simulate
import random


def test_replay_preserves_weekly_shape():
    xs = replay_arrivals([20, 60, 100], 1, 14, random.Random(1))
    assert xs == [20, 60, 100, 10100, 10140, 10180]


def test_batching_reduces_ci_minutes_when_arrivals_are_fast():
    small = simulate(2000, [14], 0, 1, days=7, seed=1)
    large = simulate(2000, [14], 0, 128, days=7, seed=1)
    assert not small['stable']
    assert large['stable']
    assert large['ci_minutes_per_merge'] < small['ci_minutes_per_merge']


if __name__ == '__main__':
    test_replay_preserves_weekly_shape()
    test_batching_reduces_ci_minutes_when_arrivals_are_fast()
