/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Density
public import TauCeti.MeasureTheory.Function.AreaFormula.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The arcs of a circle near one of its points

For the circle `S = sphere c ρ` of radius `ρ > 0` in `ℂ = ℝ²` and a point `x = circleMap c ρ φ` on
it, the arc of `S` within distance `r` of `x` is the image of the angles `θ` with
`|θ - φ| < 2 arcsin (r / (2ρ))`, since the chord from `x` to `circleMap c ρ θ` has length
`2ρ |sin ((θ - φ) / 2)|` (`TauCeti.preimage_circleMap_ball_inter_Icc`). For `0 < r ≤ 2ρ` its
length is therefore `H¹(S ∩ B(x, r)) = 4ρ arcsin (r / (2ρ))`
(`Complex.euclideanHausdorffMeasure_sphere_inter_ball`), and
`4ρ arcsin (r / (2ρ)) / (2r) → 1` as `r → 0⁺`
(`TauCeti.Examples.CircleArc.tendsto_arcLength_div`): `H¹⌞S` has one-dimensional density `1` at
every point of `S` (`TauCeti.Examples.CircleArc.hasDensity_one_sphere`), the normalisation being
by `ω₁ r = 2r`. Dividing by `r` instead would give the limit `2`
(`TauCeti.Examples.CircleArc.tendsto_arcLength_div_radius`).
-/

public section

noncomputable section

open MeasureTheory Metric Set Real Filter Topology
open scoped ENNReal

namespace TauCeti.Examples.CircleArc

/-- **The density ratio of a short arc tends to `1`**: `4ρ arcsin (r / (2ρ)) / (2r) → 1` as
`r → 0⁺`. -/
theorem tendsto_arcLength_div {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun r ↦ 4 * ρ * arcsin (r / (2 * ρ)) / (2 * r)) (𝓝[>] 0) (𝓝 1) := by
  -- `arcsin u / u → arcsin' 0 = 1` as `u → 0⁺`.
  have hd := (hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)).tendsto_slope_zero_right
  simp only [zero_add, arcsin_zero, sub_zero, smul_eq_mul, sq, mul_zero, Real.sqrt_one,
    div_one] at hd
  have hu : Tendsto (fun r : ℝ ↦ r / (2 * ρ)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_,
      eventually_nhdsWithin_of_forall fun r (hr : 0 < r) ↦ div_pos hr (by positivity)⟩
    simpa using ((continuous_id.div_const (2 * ρ)).tendsto 0).mono_left nhdsWithin_le_nhds
  refine (hd.comp hu).congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) ↦ ?_)
  simp only [Function.comp_apply]
  field_simp
  ring

/-- Normalising by `r` instead of `ω₁ r = 2r` gives the limit `2`. -/
theorem tendsto_arcLength_div_radius {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun r ↦ 4 * ρ * arcsin (r / (2 * ρ)) / r) (𝓝[>] 0) (𝓝 2) := by
  have h := (tendsto_arcLength_div hρ).const_mul 2
  rw [mul_one] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) ↦ ?_)
  field_simp

/-- **`H¹⌞S` has density `1` at every point of the circle `S`.** -/
theorem hasDensity_one_sphere (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {x : ℂ} (hx : x ∈ sphere c ρ) :
    (μHE[1].restrict (sphere c ρ)).HasDensity 1 x 1 := by
  rw [Measure.hasDensity_iff]
  have h := ENNReal.tendsto_ofReal (tendsto_arcLength_div hρ)
  rw [ENNReal.ofReal_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 2 * ρ)] with r hr
  rw [Measure.densityRatio_def, Metric.eball_ofReal,
    Measure.restrict_apply measurableSet_ball, inter_comm,
    Complex.euclideanHausdorffMeasure_sphere_inter_ball c hρ hr.1 hr.2.le hx, unitBallVolume_one,
    pow_one, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by linarith [hr.1])]

end TauCeti.Examples.CircleArc
