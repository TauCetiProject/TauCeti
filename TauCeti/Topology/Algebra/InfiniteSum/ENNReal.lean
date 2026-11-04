/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Sums of extended nonnegative series

A series in `ℝ≥0∞` with a finite sum has a convergent real-valued series obtained by applying
`ENNReal.toReal` termwise. The real sum is the `toReal` of the original sum. This converts
nonnegative mass series into real probability formulas without repeating the finiteness argument.

Summing the indicator of a set `s` with value one counts its elements: the sum is `s.encard`.
This is the indicator form of `ENNReal.tsum_set_one`.
-/

public section

open scoped ENNReal

/-- Applying `ENNReal.toReal` termwise preserves a series with finite sum. -/
theorem HasSum.toReal {ι : Type*} {f : ι → ℝ≥0∞} {s : ℝ≥0∞}
    (h : HasSum f s) (hs : s ≠ ∞) : HasSum (fun i ↦ (f i).toReal) s.toReal := by
  have hfin : ∑' i, f i ≠ ∞ := by rwa [h.tsum_eq]
  simpa only [← ENNReal.tsum_toReal_eq (_root_.ne_top_of_tsum_ne_top hfin), h.tsum_eq]
    using ENNReal.hasSum_toReal hfin

/-- Summing the indicator of a set with value one counts its elements. -/
theorem ENNReal.tsum_indicator_one {β : Type*} (s : Set β) :
    ∑' b, s.indicator (fun _ => (1 : ℝ≥0∞)) b = s.encard := by
  rw [← ENNReal.tsum_set_one, tsum_subtype _ fun _ => (1 : ℝ≥0∞)]
