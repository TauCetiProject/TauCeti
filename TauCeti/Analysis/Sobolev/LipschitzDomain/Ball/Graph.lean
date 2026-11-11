/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic

/-!
# Balls as epigraphs in Lipschitz boundary charts

Seen from rigid coordinates `e` in which the centre of `ball 0 r` is the point `c = e 0`, the lower
boundary of the ball is the graph of `v ↦ c.fst - √(r ^ 2 - ‖v - c.snd‖ ^ 2)` over the tangential
coordinate. Truncating the tangential distance at `ρ < r` gives the globally Lipschitz function
`TauCeti.ballGraph r ρ c`, and inside a chart cylinder lying in the lower half of the ball the
ball is exactly the region above this graph. This supplies the boundary charts of domains whose
boundary contains a piece of a round sphere.

## Main declarations

* `TauCeti.ballGraph r ρ c`: the truncated lower boundary of the ball of radius `r` centred at `c`.
* `TauCeti.lipschitzWith_ballGraph`: the truncated graph is Lipschitz with constant
  `ρ / √(r ^ 2 - ρ ^ 2)`.
* `TauCeti.symm_mem_ball_iff_ballGraph_lt`: inside a cylinder in the lower half of the ball, the
  ball is the region above `TauCeti.ballGraph`.
-/

public section

noncomputable section

open Metric Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- The lower boundary of the ball of radius `r` centred at `c` in `WithLp 2 (ℝ × E)`, as a graph
over the tangential coordinate, truncated at tangential distance `ρ` from `c` so that it is
globally Lipschitz. -/
def ballGraph (r ρ : ℝ) (c : WithLp 2 (ℝ × E)) (v : E) : ℝ :=
  c.fst - √(r ^ 2 - min ‖v - c.snd‖ ρ ^ 2)

/-- `TauCeti.ballGraph r ρ c v` is `c.fst - √(r ^ 2 - min ‖v - c.snd‖ ρ ^ 2)`. -/
theorem ballGraph_def (r ρ : ℝ) (c : WithLp 2 (ℝ × E)) (v : E) :
    ballGraph r ρ c v = c.fst - √(r ^ 2 - min ‖v - c.snd‖ ρ ^ 2) :=
  (rfl)

/-- For `0 ≤ ρ < r`, the truncated lower boundary of the ball is Lipschitz with constant
`ρ / √(r ^ 2 - ρ ^ 2)`. -/
theorem lipschitzWith_ballGraph {c : WithLp 2 (ℝ × E)} {r ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < r) :
    LipschitzWith (ρ / √(r ^ 2 - ρ ^ 2)).toNNReal (ballGraph r ρ c) := by
  have hs : 0 < √(r ^ 2 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  set m := min ‖v - c.snd‖ ρ
  set n := min ‖w - c.snd‖ ρ
  have hm0 : 0 ≤ m := le_min (norm_nonneg _) hρ0
  have hn0 : 0 ≤ n := le_min (norm_nonneg _) hρ0
  have hmρ : m ≤ ρ := min_le_right _ _
  have hnρ : n ≤ ρ := min_le_right _ _
  have hmn : |m - n| ≤ dist v w := by
    calc |m - n| ≤ max |‖v - c.snd‖ - ‖w - c.snd‖| |ρ - ρ| := abs_min_sub_min_le_max _ _ _ _
      _ = |‖v - c.snd‖ - ‖w - c.snd‖| := by simp
      _ ≤ ‖(v - c.snd) - (w - c.snd)‖ := abs_norm_sub_norm_le _ _
      _ = dist v w := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  set x := √(r ^ 2 - m ^ 2)
  set y := √(r ^ 2 - n ^ 2)
  have hx : x ^ 2 = r ^ 2 - m ^ 2 := Real.sq_sqrt (by nlinarith)
  have hy : y ^ 2 = r ^ 2 - n ^ 2 := Real.sq_sqrt (by nlinarith)
  have hxs : √(r ^ 2 - ρ ^ 2) ≤ x := Real.sqrt_le_sqrt (by nlinarith)
  have hys : √(r ^ 2 - ρ ^ 2) ≤ y := Real.sqrt_le_sqrt (by nlinarith)
  have hd : dist (ballGraph r ρ c v) (ballGraph r ρ c w) = |y - x| := by
    rw [ballGraph, ballGraph, Real.dist_eq, sub_sub_sub_cancel_left]
  rw [hd, Real.coe_toNNReal _ (div_nonneg hρ0 hs.le), div_mul_eq_mul_div,
    le_div_iff₀ hs]
  -- `|y - x| (x + y) = |m - n| (m + n) ≤ 2 ρ dist v w`, and `x + y ≥ 2 √(r² - ρ²)`.
  have hprod : |y - x| * (x + y) = |m - n| * (m + n) := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ x + y), ← abs_of_nonneg (by positivity : 0 ≤ m + n),
      ← abs_mul, ← abs_mul]
    rw [abs_eq_abs]
    left
    linear_combination hy - hx
  have h1 : |y - x| * (2 * √(r ^ 2 - ρ ^ 2)) ≤ |y - x| * (x + y) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h2 : |m - n| * (m + n) ≤ dist v w * (2 * ρ) :=
    mul_le_mul hmn (by linarith) (by positivity) dist_nonneg
  nlinarith [abs_nonneg (y - x)]

/-- Inside a cylinder lying in the lower half of the ball `ball 0 r` seen from the chart `e`, the
ball is the region above `TauCeti.ballGraph`. -/
theorem symm_mem_ball_iff_ballGraph_lt [NormedSpace ℝ E]
    {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {r ρ a b : ℝ}
    (hr : 0 ≤ r) (ha : a ≤ (e 0).fst) (hb : ‖(e 0).snd‖ + b ≤ ρ) {z : WithLp 2 (ℝ × E)}
    (hz : z ∈ normalCylinder a b) :
    e.symm z ∈ ball 0 r ↔ ballGraph r ρ (e 0) z.snd < z.fst := by
  set c := e 0
  rw [mem_normalCylinder] at hz
  have hdist : dist (e.symm z) 0 = dist z c := by rw [← e.dist_map, e.apply_symm_apply]
  have hm : min ‖z.snd - c.snd‖ ρ = ‖z.snd - c.snd‖ :=
    min_eq_left (by linarith [norm_sub_le z.snd c.snd])
  have hpos : 0 ≤ c.fst - z.fst := by linarith
  have hsq : dist z c ^ 2 = (z.fst - c.fst) ^ 2 + ‖z.snd - c.snd‖ ^ 2 := by
    rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd,
      Real.norm_eq_abs, sq_abs]
  rw [mem_ball, hdist, ballGraph, hm, sub_lt_comm, Real.lt_sqrt hpos,
    ← sq_lt_sq₀ dist_nonneg hr, hsq]
  constructor <;> intro h <;> nlinarith

end TauCeti
