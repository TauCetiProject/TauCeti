/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Density
public import TauCeti.MeasureTheory.Function.AreaFormula.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# The arcs of a circle near one of its points

For the circle `S = sphere c ρ` of radius `ρ > 0` in `ℂ = ℝ²` and a point `x = circleMap c ρ φ` on
it, the arc of `S` within distance `r` of `x` is the image of the angles `θ` with
`|θ - φ| < 2 arcsin (r / (2ρ))`, since the chord from `x` to `circleMap c ρ θ` has length
`2ρ |sin ((θ - φ) / 2)|`. For `0 < r ≤ 2ρ` its length is therefore
`H¹(S ∩ B(x, r)) = 4ρ arcsin (r / (2ρ))`
(`TauCeti.Examples.CircleArc.euclideanHausdorffMeasure_sphere_inter_ball`), and
`4ρ arcsin (r / (2ρ)) / (2r) → 1` as `r → 0⁺`
(`TauCeti.Examples.CircleArc.tendsto_arcLength_div`): `H¹⌞S` has one-dimensional density `1` at
every point of `S` (`TauCeti.Examples.CircleArc.hasDensity_one_sphere`), the normalisation being
by `ω₁ r = 2r`. Dividing by `r` instead would give the limit `2`
(`TauCeti.Examples.CircleArc.tendsto_arcLength_div_radius`).

This is a Check of roadmap `GeometricMeasureTheory`, §2.1 (approximate tangent spaces).
-/

public section

noncomputable section

open MeasureTheory Metric Set Real Filter Topology
open scoped ENNReal

namespace TauCeti.Examples.CircleArc

/-- `ρ` times the image of Lebesgue measure on `[φ - π, φ + π]` under `circleMap c ρ` is `H¹` on
the circle `sphere c ρ`. -/
theorem smul_map_volume_restrict_circleMap_Icc (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (φ : ℝ) :
    ENNReal.ofReal ρ • (volume.restrict (Icc (φ - π) (φ + π))).map (circleMap c ρ) =
      μHE[1].restrict (sphere c ρ) := by
  have himage : circleMap c ρ '' Icc (φ - π) (φ + π) = sphere c ρ := by
    refine Subset.antisymm ((image_subset_range _ _).trans_eq ?_) ?_
    · rw [range_circleMap, abs_of_pos hρ]
    · have h := (periodic_circleMap c ρ).image_Ioc two_pi_pos (φ - π)
      rw [range_circleMap, abs_of_pos hρ, show φ - π + 2 * π = φ + π by ring] at h
      exact h.symm.subset.trans (image_mono Ioc_subset_Icc_self)
  have h := LipschitzOnWith.map_withDensity_enorm_deriv_eq_euclideanHausdorffMeasure_restrict
    ((lipschitzWith_circleMap c ρ).lipschitzOnWith (s := Icc (φ - π) (φ + π)))
    ((injOn_circleMap_of_abs_sub_le' (a := φ - π) (b := φ + π) (c := c) hρ.ne'
      (by linarith)).mono Ioo_subset_Ico_self)
  have hd : (fun t ↦ ‖deriv (circleMap c ρ) t‖ₑ) = fun _ ↦ ENNReal.ofReal ρ :=
    funext fun t ↦ by simp [deriv_circleMap, ← ofReal_norm, abs_of_pos hρ]
  rwa [hd, withDensity_const, Measure.map_smul, himage] at h
  exact (continuous_circleMap c ρ).aemeasurable

/-- The chord from `circleMap c ρ φ` to `circleMap c ρ θ` has length `2ρ |sin ((θ - φ) / 2)|`. -/
theorem dist_circleMap (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (θ φ : ℝ) :
    dist (circleMap c ρ θ) (circleMap c ρ φ) = 2 * ρ * |sin ((θ - φ) / 2)| := by
  have h : circleMap c ρ θ - circleMap c ρ φ =
      ρ * Complex.exp (φ * Complex.I) * (Complex.exp (Complex.I * (θ - φ : ℝ)) - 1) := by
    simp only [circleMap, Complex.ofReal_sub]
    rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [dist_eq_norm, h, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Complex.norm_real, Real.norm_of_nonneg hρ, norm_mul,
    Real.norm_two, Real.norm_eq_abs]
  ring

/-- For `|y| ≤ π / 2` and `0 < s ≤ 1`, `|sin y| < s` exactly when `|y| < arcsin s`. -/
theorem abs_sin_lt_iff {y s : ℝ} (hy : |y| ≤ π / 2) (hs : s ∈ Icc (-1 : ℝ) 1) :
    |sin y| < s ↔ |y| < arcsin s := by
  have hy' := abs_le.1 hy
  have hsin : |sin y| = sin |y| := by
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h (by linarith [pi_pos]))]
    · rw [abs_of_nonpos h, sin_neg, abs_of_nonpos]
      exact sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith [pi_pos])
  rw [hsin, lt_arcsin_iff_sin_lt ⟨by linarith [abs_nonneg y, pi_pos], hy⟩ hs]

/-- The arc of `sphere c ρ` within distance `r` of `circleMap c ρ φ` is parametrised by the angles
`θ ∈ [φ - π, φ + π]` with `|θ - φ| < 2 arcsin (r / (2ρ))`, for `0 < r ≤ 2ρ`. -/
theorem Icc_inter_preimage_ball (c : ℂ) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hr2 : r ≤ 2 * ρ)
    (φ : ℝ) :
    circleMap c ρ ⁻¹' ball (circleMap c ρ φ) r ∩ Icc (φ - π) (φ + π) =
      Ioo (φ - 2 * arcsin (r / (2 * ρ))) (φ + 2 * arcsin (r / (2 * ρ))) := by
  have hs : r / (2 * ρ) ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [div_pos hr (by linarith : (0 : ℝ) < 2 * ρ)],
      (div_le_one (by linarith)).2 hr2⟩
  have ha : arcsin (r / (2 * ρ)) ≤ π / 2 := arcsin_le_pi_div_two _
  ext θ
  simp only [mem_inter_iff, mem_preimage, mem_ball, mem_Icc, mem_Ioo, dist_circleMap c hρ.le]
  constructor
  · rintro ⟨h, h1, h2⟩
    have hy : |(θ - φ) / 2| ≤ π / 2 := by
      rw [abs_le]; constructor <;> linarith
    have h' : |sin ((θ - φ) / 2)| < r / (2 * ρ) := by
      rw [lt_div_iff₀ (by linarith)]; linarith
    rw [abs_sin_lt_iff hy hs, abs_lt] at h'
    constructor <;> linarith [h'.1, h'.2]
  · rintro ⟨h1, h2⟩
    have hy : |(θ - φ) / 2| ≤ π / 2 := by
      rw [abs_le]; constructor <;> linarith
    have h' : |(θ - φ) / 2| < arcsin (r / (2 * ρ)) := by
      rw [abs_lt]; constructor <;> linarith
    rw [← abs_sin_lt_iff hy hs, lt_div_iff₀ (by linarith)] at h'
    refine ⟨by linarith, by linarith, by linarith⟩

/-- **The length of a short arc.** For `0 < r ≤ 2ρ`, the arc of the circle `sphere c ρ` within
distance `r` of a point `x` on it has length `4ρ arcsin (r / (2ρ))`. -/
theorem euclideanHausdorffMeasure_sphere_inter_ball (c : ℂ) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hr2 : r ≤ 2 * ρ) {x : ℂ} (hx : x ∈ sphere c ρ) :
    μHE[1] (sphere c ρ ∩ ball x r) = ENNReal.ofReal (4 * ρ * arcsin (r / (2 * ρ))) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, circleMap c ρ φ = x := by
    rw [← mem_range, range_circleMap, abs_of_pos hρ]
    exact hx
  rw [inter_comm, ← Measure.restrict_apply measurableSet_ball,
    ← smul_map_volume_restrict_circleMap_Icc c hρ φ, smul_apply,
    Measure.map_apply (continuous_circleMap c ρ).measurable measurableSet_ball,
    Measure.restrict_apply (measurableSet_ball.preimage (continuous_circleMap c ρ).measurable),
    Icc_inter_preimage_ball c hρ hr hr2, Real.volume_Ioo, smul_eq_mul,
    ← ENNReal.ofReal_mul hρ.le]
  congr 1
  ring

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
    euclideanHausdorffMeasure_sphere_inter_ball c hρ hr.1 hr.2.le hx, unitBallVolume_one, pow_one,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by linarith [hr.1])]

end TauCeti.Examples.CircleArc
