/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Density bounds through charts

Density bounds `c ρ ^ d ≤ μ (closedBall x ρ) ≤ C ρ ^ d` are often proved in a chart, for the
balls of a model space `Y`, while packing and covering are counted with the balls of a
pseudometric space `X`, as on a manifold with a distance. This file transfers such bounds from
the balls of the chart to the balls of `X`. Let `e : X → Y` be a map on a set `s`, and let `ν` be
a measure on `Y`, compared with `μ` on the ball `ball (e x) R` through the sets `s ∩ e ⁻¹' t`;
when `ν` is the pushforward of `μ` restricted to `s`, both comparisons below hold with equality.

* If the inverse of `e` is `Λ`-Lipschitz at `e x`, that is `dist y x ≤ Λ * dist (e y) (e x)` for
  `y ∈ s` with `e y ∈ ball (e x) R`, and `ν t ≤ μ (s ∩ e ⁻¹' t)`, then the chart ball of radius
  `ρ < R` has `ν`-measure at most the `μ`-measure of the ball of radius `Λ ρ` about `x`
  (`TauCeti.measure_closedBall_le_measure_closedBall_mul_of_dist_le_mul_dist_apply`). So a lower
  density bound `c ρ ^ d` for `ν` at `e x` gives the lower density bound `(c / Λ ^ d) ρ ^ d` for
  `μ` at `x` (`TauCeti.ofReal_div_mul_pow_le_measure_closedBall_of_dist_le_mul_dist_apply`), to
  which the covering bound `TauCeti.coveringNumber_le_of_mul_pow_le_measure_closedBall` applies.
* Dually, if `e` is `Λ`-Lipschitz at `x` on a ball about `x` contained in `s`, and
  `μ (s ∩ e ⁻¹' t) ≤ ν t`, then the ball of radius `ρ` about `x` has `μ`-measure at most the
  `ν`-measure of the chart ball of radius `Λ ρ`
  (`TauCeti.measure_closedBall_le_measure_closedBall_mul_of_dist_apply_le_mul_dist`). So an upper
  density bound `C ρ ^ d` for `ν` gives the upper density bound `C Λ ^ d ρ ^ d` for `μ`
  (`TauCeti.measure_closedBall_le_ofReal_mul_mul_pow_of_dist_apply_le_mul_dist`).

In the large-parameter analysis of the Seiberg–Witten equations, `Y` is a Darboux chart, `ν` the
defect energy of a solution read in the chart and `μ` its defect energy on the manifold.

## Main results

* `TauCeti.ofReal_div_mul_pow_le_measure_closedBall_of_dist_le_mul_dist_apply`: a lower density
  bound in the chart gives a lower density bound for the balls of `X`.
* `TauCeti.measure_closedBall_le_ofReal_mul_mul_pow_of_dist_apply_le_mul_dist`: an upper density
  bound in the chart gives an upper density bound for the balls of `X`.
-/

public section

open MeasureTheory Metric Set

namespace TauCeti

variable {X Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [PseudoMetricSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure X} {ν : Measure Y} {e : X → Y}
  {s : Set X} {x : X} {Λ R : ℝ}

/-- **Chart balls and metric balls.** Let `e : X → Y` be a map on a set `s` whose inverse is
`Λ`-Lipschitz at `e x` on the ball `ball (e x) R`, in the sense that `dist y x ≤ Λ dist (e y) (e x)`
for every `y ∈ s` with `e y ∈ ball (e x) R`, and let `ν` be a measure on `Y` with
`ν t ≤ μ (s ∩ e ⁻¹' t)` for every measurable `t ⊆ ball (e x) R`. Then for `ρ < R` the closed
ball of radius `ρ` about `e x` has `ν`-measure at most the `μ`-measure of the closed ball of radius
`Λ ρ` about `x`. -/
theorem measure_closedBall_le_measure_closedBall_mul_of_dist_le_mul_dist_apply
    (hdist : ∀ y ∈ s, e y ∈ ball (e x) R → dist y x ≤ Λ * dist (e y) (e x))
    (hν : ∀ t ⊆ ball (e x) R, MeasurableSet t → ν t ≤ μ (s ∩ e ⁻¹' t)) (hΛ : 0 ≤ Λ) {ρ : ℝ}
    (hρR : ρ < R) :
    ν (closedBall (e x) ρ) ≤ μ (closedBall x (Λ * ρ)) := by
  have hball : closedBall (e x) ρ ⊆ ball (e x) R := closedBall_subset_ball hρR
  refine (hν _ hball measurableSet_closedBall).trans (measure_mono fun y hy ↦ ?_)
  rw [mem_closedBall]
  exact (hdist y hy.1 (hball hy.2)).trans (mul_le_mul_of_nonneg_left hy.2 hΛ)

/-- **Lower density bounds through a chart.** Let `e : X → Y` be a map on a set `s` whose inverse
is `Λ`-Lipschitz at `e x` on the ball `ball (e x) R`, with `Λ > 0`, and let `ν` be a measure on `Y`
with `ν t ≤ μ (s ∩ e ⁻¹' t)` for every measurable `t ⊆ ball (e x) R`. If
`ν (closedBall (e x) ρ) ≥ c ρ ^ d` for every radius `a ≤ ρ ≤ b`, with `b < R`, then
`μ (closedBall x ρ) ≥ (c / Λ ^ d) ρ ^ d` for every radius `Λ a ≤ ρ ≤ Λ b`. -/
theorem ofReal_div_mul_pow_le_measure_closedBall_of_dist_le_mul_dist_apply {a b c : ℝ} {d : ℕ}
    (hdist : ∀ y ∈ s, e y ∈ ball (e x) R → dist y x ≤ Λ * dist (e y) (e x))
    (hν : ∀ t ⊆ ball (e x) R, MeasurableSet t → ν t ≤ μ (s ∩ e ⁻¹' t)) (hΛ : 0 < Λ)
    (hbR : b < R)
    (hlow : ∀ ρ, a ≤ ρ → ρ ≤ b → ENNReal.ofReal (c * ρ ^ d) ≤ ν (closedBall (e x) ρ))
    {ρ : ℝ} (haρ : Λ * a ≤ ρ) (hρb : ρ ≤ Λ * b) :
    ENNReal.ofReal (c / Λ ^ d * ρ ^ d) ≤ μ (closedBall x ρ) := by
  -- The chart radius is `ρ / Λ`, which lies in `[a, b]`.
  have ha : a ≤ ρ / Λ := by rwa [le_div_iff₀ hΛ, mul_comm]
  have hb : ρ / Λ ≤ b := by rwa [div_le_iff₀ hΛ, mul_comm]
  have hρ : Λ * (ρ / Λ) = ρ := mul_div_cancel₀ ρ hΛ.ne'
  calc ENNReal.ofReal (c / Λ ^ d * ρ ^ d) = ENNReal.ofReal (c * (ρ / Λ) ^ d) := by
        congr 1; ring
    _ ≤ ν (closedBall (e x) (ρ / Λ)) := hlow _ ha hb
    _ ≤ μ (closedBall x (Λ * (ρ / Λ))) :=
        measure_closedBall_le_measure_closedBall_mul_of_dist_le_mul_dist_apply hdist hν hΛ.le
          (hb.trans_lt hbR)
    _ = μ (closedBall x ρ) := by rw [hρ]

/-- **Metric balls and chart balls.** Let `e : X → Y` be a map on a set `s` containing the closed
ball of radius `ρ` about `x`, which is `Λ`-Lipschitz at `x` on that ball, in the sense that
`dist (e y) (e x) ≤ Λ dist y x` for every `y` in it, and let `ν` be a measure on `Y` with
`μ (s ∩ e ⁻¹' t) ≤ ν t` for every measurable `t ⊆ ball (e x) R`. If `0 ≤ Λ` and `Λ ρ < R`, then
the closed ball of radius `ρ` about `x` has `μ`-measure at most the `ν`-measure of the closed ball
of radius `Λ ρ` about `e x`. -/
theorem measure_closedBall_le_measure_closedBall_mul_of_dist_apply_le_mul_dist {ρ : ℝ}
    (hs : closedBall x ρ ⊆ s) (hdist : ∀ y ∈ closedBall x ρ, dist (e y) (e x) ≤ Λ * dist y x)
    (hν : ∀ t ⊆ ball (e x) R, MeasurableSet t → μ (s ∩ e ⁻¹' t) ≤ ν t) (hΛ : 0 ≤ Λ)
    (hρR : Λ * ρ < R) :
    μ (closedBall x ρ) ≤ ν (closedBall (e x) (Λ * ρ)) := by
  have hsub : closedBall x ρ ⊆ s ∩ e ⁻¹' closedBall (e x) (Λ * ρ) := fun y hy ↦
    ⟨hs hy, (hdist y hy).trans (mul_le_mul_of_nonneg_left (mem_closedBall.1 hy) hΛ)⟩
  exact (measure_mono hsub).trans (hν _ (closedBall_subset_ball hρR) measurableSet_closedBall)

/-- **Upper density bounds through a chart.** Let `e : X → Y` be a map on a set `s` containing the
closed ball of radius `R₁` about `x`, which is `Λ`-Lipschitz at `x` on that ball, with `Λ ≥ 0`,
and let `ν` be a measure on `Y` with `μ (s ∩ e ⁻¹' t) ≤ ν t` for every measurable
`t ⊆ ball (e x) R`. If `ν (closedBall (e x) ρ) ≤ C ρ ^ d` for every radius `a ≤ ρ ≤ b`, with
`b < R`, then `μ (closedBall x ρ) ≤ C Λ ^ d ρ ^ d` for every radius `ρ ≤ R₁` with
`a ≤ Λ ρ ≤ b`. -/
theorem measure_closedBall_le_ofReal_mul_mul_pow_of_dist_apply_le_mul_dist {a b C R₁ : ℝ} {d : ℕ}
    (hs : closedBall x R₁ ⊆ s) (hdist : ∀ y ∈ closedBall x R₁, dist (e y) (e x) ≤ Λ * dist y x)
    (hν : ∀ t ⊆ ball (e x) R, MeasurableSet t → μ (s ∩ e ⁻¹' t) ≤ ν t) (hΛ : 0 ≤ Λ)
    (hbR : b < R)
    (hup : ∀ ρ, a ≤ ρ → ρ ≤ b → ν (closedBall (e x) ρ) ≤ ENNReal.ofReal (C * ρ ^ d))
    {ρ : ℝ} (hρR₁ : ρ ≤ R₁) (haρ : a ≤ Λ * ρ) (hρb : Λ * ρ ≤ b) :
    μ (closedBall x ρ) ≤ ENNReal.ofReal (C * Λ ^ d * ρ ^ d) := by
  have hsub : closedBall x ρ ⊆ closedBall x R₁ := closedBall_subset_closedBall hρR₁
  calc μ (closedBall x ρ) ≤ ν (closedBall (e x) (Λ * ρ)) :=
        measure_closedBall_le_measure_closedBall_mul_of_dist_apply_le_mul_dist (hsub.trans hs)
          (fun y hy ↦ hdist y (hsub hy)) hν hΛ (hρb.trans_lt hbR)
    _ ≤ ENNReal.ofReal (C * (Λ * ρ) ^ d) := hup _ haρ hρb
    _ = ENNReal.ofReal (C * Λ ^ d * ρ ^ d) := by congr 1; ring

end TauCeti
