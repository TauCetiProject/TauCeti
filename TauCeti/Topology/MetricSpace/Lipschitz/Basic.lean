/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
import TauCeti.Algebra.Order.Field.Basic

/-!
# Basic Lipschitz estimates

This file collects elementary `LipschitzWith` facts and bounded-gauge estimates:

* The shifted positive part `t ↦ max (t - k) 0` is `1`-Lipschitz on the real line.
* A `K`-Lipschitz map with `1 ≤ K` scales the bounded-metric gauge `d / (1 + d)` by at most `K`,
  and a `K`-Lipschitz binary map on a product pseudometric space bounds the output gauge by `K`
  times the sum of the component gauges.

## Main results

* `TauCeti.lipschitzWith_max_sub_const_zero`: the shifted positive part is `1`-Lipschitz.
* `LipschitzWith.dist_div_one_add_dist_le_mul`: bounded-gauge estimate for a `K`-Lipschitz map
  with `1 ≤ K`.
* `LipschitzWith.dist_div_one_add_dist_prod_le`: bounded-gauge estimate for a `K`-Lipschitz binary
  map `α × β → γ` with `1 ≤ K`.
-/

public section

open scoped NNReal

namespace TauCeti

/-- The shifted positive part `t ↦ max (t - k) 0` is `1`-Lipschitz on the real line. -/
theorem lipschitzWith_max_sub_const_zero (k : ℝ) : LipschitzWith 1 (fun t : ℝ => max (t - k) 0) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (x - k) (y - k) 0

end TauCeti

namespace LipschitzWith

/-- For a `K`-Lipschitz map `f : α → β` with `1 ≤ K`, the bounded-metric gauge `d / (1 + d)`
satisfies `dist (f x) (f y) / (1 + dist (f x) (f y)) ≤ K * (dist x y / (1 + dist x y))`. -/
theorem dist_div_one_add_dist_le_mul {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {K : ℝ≥0} {f : α → β} (hf : LipschitzWith K f) (hK : 1 ≤ K) (x y : α) :
    dist (f x) (f y) / (1 + dist (f x) (f y)) ≤
      (K : ℝ) * (dist x y / (1 + dist x y)) :=
  (TauCeti.div_one_add_mono dist_nonneg (hf.dist_le_mul x y)).trans
    (TauCeti.mul_div_one_add_mul_le (NNReal.one_le_coe.mpr hK) dist_nonneg)

/-- For a `K`-Lipschitz binary map `f : α × β → γ` with `1 ≤ K`, the bounded-metric gauge of `f`
is bounded by `K` times the sum of the component gauges. -/
theorem dist_div_one_add_dist_prod_le {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] {K : ℝ≥0} {f : α × β → γ} (hf : LipschitzWith K f) (hK : 1 ≤ K)
    (p q : α × β) :
    dist (f p) (f q) / (1 + dist (f p) (f q)) ≤
      (K : ℝ) * (dist p.1 q.1 / (1 + dist p.1 q.1)) +
        (K : ℝ) * (dist p.2 q.2 / (1 + dist p.2 q.2)) := by
  calc dist (f p) (f q) / (1 + dist (f p) (f q))
      ≤ (K : ℝ) * (dist p q / (1 + dist p q)) :=
        hf.dist_div_one_add_dist_le_mul hK p q
    _ ≤ (K : ℝ) * (dist p.1 q.1 / (1 + dist p.1 q.1) +
          dist p.2 q.2 / (1 + dist p.2 q.2)) := by
        refine mul_le_mul_of_nonneg_left ?_ K.coe_nonneg
        rw [Prod.dist_eq]
        rcases le_total (dist p.1 q.1) (dist p.2 q.2) with h | h
        · rw [max_eq_right h]
          exact le_add_of_nonneg_left (TauCeti.div_one_add_nonneg dist_nonneg)
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (TauCeti.div_one_add_nonneg dist_nonneg)
    _ = (K : ℝ) * (dist p.1 q.1 / (1 + dist p.1 q.1)) +
          (K : ℝ) * (dist p.2 q.2 / (1 + dist p.2 q.2)) := mul_add _ _ _

end LipschitzWith
