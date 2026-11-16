/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz real functions

Basic Lipschitz bounds for real-valued maps: the shifted positive part `t ↦ max (t - k) 0` is
`1`-Lipschitz on the real line, and a real-valued `L`-Lipschitz function bounded by `M` on any
pseudo-metric space has `(2 * M * L)`-Lipschitz square and `(M * L)`-Lipschitz `r₀ - f² / 2`.

## Main results

* `TauCeti.lipschitzWith_max_sub_const_zero`: the shifted positive part is `1`-Lipschitz.
* `TauCeti.lipschitzWith_sq_of_abs_le`: if `|f x| ≤ M` and `f` is `L`-Lipschitz, then `f²` is
  `(2 * M * L)`-Lipschitz.
* `TauCeti.lipschitzWith_const_sub_sq_div_two`: if `|f x| ≤ M` and `f` is `L`-Lipschitz, then
  `x ↦ r₀ - f x ^ 2 / 2` is `(M * L)`-Lipschitz.
-/

public section

open scoped NNReal

namespace TauCeti

/-- The shifted positive part `t ↦ max (t - k) 0` is `1`-Lipschitz on the real line. -/
theorem lipschitzWith_max_sub_const_zero (k : ℝ) : LipschitzWith 1 (fun t : ℝ => max (t - k) 0) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (x - k) (y - k) 0

/-- The square of a real-valued `L`-Lipschitz function bounded in absolute value by `M` is
`(2 * M * L)`-Lipschitz. -/
theorem lipschitzWith_sq_of_abs_le {X : Type*} [PseudoMetricSpace X] {M L : ℝ≥0} {f : X → ℝ}
    (hM : ∀ x, |f x| ≤ M) (hL : LipschitzWith L f) :
    LipschitzWith (2 * M * L) (fun x ↦ f x ^ 2) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq, show f x ^ 2 - f y ^ 2 = (f x + f y) * (f x - f y) by ring, abs_mul,
    NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_ofNat, mul_assoc]
  exact mul_le_mul ((abs_add_le (f x) (f y)).trans (by linarith [hM x, hM y]))
    (by simpa only [Real.dist_eq] using hL.dist_le_mul x y) (abs_nonneg _) (by positivity)

/-- For a real-valued `L`-Lipschitz function bounded in absolute value by `M`, the map
`x ↦ r₀ - f x ^ 2 / 2` is `(M * L)`-Lipschitz. -/
theorem lipschitzWith_const_sub_sq_div_two {X : Type*} [PseudoMetricSpace X] (r₀ : ℝ) {M L : ℝ≥0}
    {f : X → ℝ} (hM : ∀ x, |f x| ≤ M) (hL : LipschitzWith L f) :
    LipschitzWith (M * L) (fun x ↦ r₀ - f x ^ 2 / 2) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hsq := (lipschitzWith_sq_of_abs_le hM hL).dist_le_mul x y
  rw [Real.dist_eq, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_ofNat] at hsq
  rw [Real.dist_eq, NNReal.coe_mul,
    show (r₀ - f x ^ 2 / 2) - (r₀ - f y ^ 2 / 2) = -(f x ^ 2 - f y ^ 2) / 2 by ring,
    abs_div, abs_neg, show |(2 : ℝ)| = 2 by norm_num]
  linarith

end TauCeti
