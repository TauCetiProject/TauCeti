/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.MeasureTheory.Function.AreaFormula.Curve
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Geometry.Euclidean.Volume.Sphere
import TauCeti.Topology.Circle.Metric
import TauCeti.Topology.EMetricSpace.CurveLength

/-!
# The length of a circle traversed twice

The parametrization `circleMap c R` traverses the circle `sphere c |R|` once on `[0, 2π]` and
twice on `[0, 4π]`; both traces are the whole circle. On `[0, 4π]` every point of the circle
other than the base point `circleMap c R 0` has exactly two parameters. The Banach indicatrix
formula `ContinuousOn.eVariationOn_eq_lintegral_encard` therefore gives the double traversal
twice the length of the single one, although the two traces have the same one-dimensional
Hausdorff measure. Length counts multiplicity; trace measure does not. That measure is the
circumference: a circle of radius `r` has one-dimensional Hausdorff measure `2 π r`, the planar
case of the measure `n ω_n r ^ (n - 1)` of spheres.

## Main results

* `TauCeti.encard_Icc_zero_four_pi_inter_preimage_circleMap`: away from the base point, the
  fibers of `circleMap c R` on `[0, 4π]` have exactly two points.
* `Complex.euclideanHausdorffMeasure_sphere`: a circle of radius `r` has one-dimensional
  Hausdorff measure `2 π r`.
* `ContinuousOn.eVariationOn_eq_of_image_eq_sphere`: a simple parametrization of a circle of
  radius `r` has length `2 π r`.
* `TauCeti.eVariationOn_circleMap_Icc_zero_two_pi`: the single traversal has length
  `μHE[1] (sphere c |R|)`.
* `TauCeti.eVariationOn_circleMap_Icc_zero_four_pi`: the double traversal has length
  `2 * μHE[1] (sphere c |R|)`.
* `TauCeti.smul_map_volume_restrict_circleMap`: `|R|` times the image of Lebesgue measure on
  `[a, a + 2π]` under `circleMap c R` is `μHE[1]` restricted to `sphere c |R|`.
* `Complex.euclideanHausdorffMeasure_sphere_inter_ball`: for `0 < r ≤ 2ρ`, the arc of the circle
  `sphere c ρ` within distance `r` of a point on it has length `4ρ arcsin (r / (2ρ))`.
-/

public section

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace TauCeti

/-- On `[0, 4π]`, the parametrization `circleMap c R` of a nondegenerate circle takes the value
`circleMap c R θ` exactly twice when `0 < θ < 2π`, namely at `θ` and at `θ + 2π`. -/
theorem encard_Icc_zero_four_pi_inter_preimage_circleMap (c : ℂ) {R θ : ℝ} (hR : R ≠ 0)
    (hθ : θ ∈ Ioo 0 (2 * π)) :
    (Icc 0 (4 * π) ∩ circleMap c R ⁻¹' {circleMap c R θ}).encard = 2 := by
  have hfiber : Icc 0 (4 * π) ∩ circleMap c R ⁻¹' {circleMap c R θ} = {θ, θ + 2 * π} := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_preimage, mem_singleton_iff, mem_insert_iff,
      circleMap_eq_circleMap_iff c hR]
    constructor
    · rintro ⟨⟨h0, h4⟩, n, hn⟩
      replace hn : t = θ + n * (2 * π) := by simpa using congrArg Complex.im hn
      -- `t = θ + 2πn` lies in `[0, 4π]` and `0 < θ < 2π`, so `n` is `0` or `1`.
      have hlo : (-1 : ℝ) < n := by
        refine lt_of_not_ge fun h ↦ ?_
        nlinarith [pi_pos, hθ.2]
      have hhi : (n : ℝ) < 2 := by
        refine lt_of_not_ge fun h ↦ ?_
        nlinarith [pi_pos, hθ.1]
      have hn' : n = 0 ∨ n = 1 := by
        have : -1 < n := by exact_mod_cast hlo
        have : n < 2 := by exact_mod_cast hhi
        omega
      rcases hn' with rfl | rfl
      · left
        simpa using hn
      · right
        simpa [mul_comm] using hn
    · rintro (rfl | rfl)
      · exact ⟨⟨hθ.1.le, by linarith [pi_pos, hθ.2]⟩, 0, by simp⟩
      · exact ⟨⟨by linarith [pi_pos, hθ.1], by linarith [hθ.2]⟩, 1, by push_cast; ring⟩
  rw [hfiber, encard_pair (by linarith [pi_pos])]

/-- A circle of radius zero is a point, so its one-dimensional Hausdorff measure vanishes. -/
private theorem hausdorffMeasure_sphere_zero (c : ℂ) : μHE[1] (sphere c |(0 : ℝ)|) = 0 := by
  rw [abs_zero, sphere_zero, Measure.euclideanHausdorffMeasure_one]
  have := Measure.nullSingletonClass_hausdorff ℂ (show (0 : ℝ) < 1 by norm_num)
  exact measure_singleton c

/-- **The circumference of a circle.** A circle of radius `r` in `ℂ` has one-dimensional
Hausdorff measure `2 π r`; for negative `r` both sides vanish. -/
theorem _root_.Complex.euclideanHausdorffMeasure_sphere (c : ℂ) {r : ℝ} :
    μHE[1] (sphere c r) = ENNReal.ofReal (2 * π * r) := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · rw [sphere_eq_empty_of_neg hr, measure_empty,
      ENNReal.ofReal_of_nonpos (by nlinarith [pi_pos])]
  · simpa using hausdorffMeasure_sphere_zero c
  have h := TauCeti.euclideanHausdorffMeasure_sphere c hr
  rw [Complex.finrank_real_complex] at h
  rw [h, Complex.volume_ball, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul zero_le_two,
    ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  simp

/-- A continuous curve on `[a, b]` that is injective on `(a, b)` and traces the circle
`sphere c r` has length `2 π r`. In particular such a parametrization is rectifiable. -/
theorem _root_.ContinuousOn.eVariationOn_eq_of_image_eq_sphere {γ : ℝ → ℂ} {a b : ℝ} {c : ℂ}
    {r : ℝ} (hcont : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b))
    (himage : γ '' Icc a b = sphere c r) :
    eVariationOn γ (Icc a b) = ENNReal.ofReal (2 * π * r) := by
  rw [hcont.eVariationOn_eq_euclideanHausdorffMeasure_image hinj, himage,
    _root_.Complex.euclideanHausdorffMeasure_sphere c]

/-- The parametrization of a circle of radius zero is constant, so it has zero variation. -/
private theorem eVariationOn_circleMap_zero (c : ℂ) (s : Set ℝ) :
    eVariationOn (circleMap c 0) s = 0 :=
  eVariationOn.constant_on (by simp [subsingleton_singleton.anti])

/-- A single traversal of a circle has length equal to the one-dimensional Hausdorff measure of
the circle. For `R = 0` both sides vanish. -/
theorem eVariationOn_circleMap_Icc_zero_two_pi (c : ℂ) (R : ℝ) :
    eVariationOn (circleMap c R) (Icc 0 (2 * π)) = μHE[1] (sphere c |R|) := by
  rcases eq_or_ne R 0 with rfl | hR
  · exact (eVariationOn_circleMap_zero c _).trans (hausdorffMeasure_sphere_zero c).symm
  have himage : circleMap c R '' Icc 0 (2 * π) = sphere c |R| :=
    Subset.antisymm ((image_subset_range _ _).trans_eq (range_circleMap c R))
      ((image_circleMap_Ioc c R).symm.subset.trans (image_mono Ioc_subset_Icc_self))
  rw [← himage]
  exact (continuous_circleMap c R).continuousOn.eVariationOn_eq_euclideanHausdorffMeasure_image
    ((injOn_circleMap_of_abs_sub_le' hR (by simp)).mono Ioo_subset_Ico_self)

/-- A double traversal of a circle has twice the length of a single traversal: its length is
twice the one-dimensional Hausdorff measure of the circle, which is also its trace. For `R = 0`
both sides vanish. -/
theorem eVariationOn_circleMap_Icc_zero_four_pi (c : ℂ) (R : ℝ) :
    eVariationOn (circleMap c R) (Icc 0 (4 * π)) = 2 * μHE[1] (sphere c |R|) := by
  rcases eq_or_ne R 0 with rfl | hR
  · rw [eVariationOn_circleMap_zero, hausdorffMeasure_sphere_zero, mul_zero]
  rw [(continuous_circleMap c R).continuousOn.eVariationOn_eq_lintegral_encard,
    Measure.euclideanHausdorffMeasure_one]
  have := Measure.nullSingletonClass_hausdorff ℂ (show (0 : ℝ) < 1 by norm_num)
  -- Off the base point, the multiplicity is the indicator of the circle with value two.
  have hmult : (fun y ↦ ((Icc 0 (4 * π) ∩ circleMap c R ⁻¹' {y}).encard : ℝ≥0∞)) =ᵐ[μH[1]]
      (sphere c |R|).indicator fun _ ↦ 2 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (circleMap c R 0))]
      with y hy
    by_cases hys : y ∈ sphere c |R|
    · obtain ⟨θ, hθ, rfl⟩ := (image_circleMap_Ioc c R).symm.subset hys
      have hθ' : θ < 2 * π := hθ.2.lt_of_ne fun h ↦ hy (by
        rw [h, ← zero_add (2 * π), periodic_circleMap c R 0]
        exact mem_singleton _)
      rw [indicator_of_mem hys, encard_Icc_zero_four_pi_inter_preimage_circleMap c hR ⟨hθ.1, hθ'⟩]
      norm_cast
    · rw [indicator_of_notMem hys]
      have hempty : Icc 0 (4 * π) ∩ circleMap c R ⁻¹' {y} = ∅ :=
        eq_empty_of_forall_notMem fun t ht ↦ hys (ht.2 ▸ circleMap_mem_sphere' c R t)
      simp [hempty]
  rw [lintegral_congr_ae hmult, lintegral_indicator_const isClosed_sphere.measurableSet]

/-- **Arc length on a circle.** The parametrization `circleMap c R` has speed `|R|`, so `|R|`
times the image of Lebesgue measure on a full turn `[a, a + 2π]` under it is the one-dimensional
Hausdorff measure on the circle `sphere c |R|`. For `R = 0` both sides vanish. -/
theorem smul_map_volume_restrict_circleMap (c : ℂ) (R a : ℝ) :
    ENNReal.ofReal |R| • (volume.restrict (Icc a (a + 2 * π))).map (circleMap c R) =
      μHE[1].restrict (sphere c |R|) := by
  rcases eq_or_ne R 0 with rfl | hR
  · rw [abs_zero, ENNReal.ofReal_zero, zero_smul, eq_comm, Measure.restrict_eq_zero]
    simpa using hausdorffMeasure_sphere_zero c
  have himage : circleMap c R '' Icc a (a + 2 * π) = sphere c |R| := by
    rw [(periodic_circleMap c R).image_Icc two_pi_pos a, range_circleMap]
  have h := LipschitzOnWith.map_withDensity_enorm_deriv_eq_euclideanHausdorffMeasure_restrict
    ((lipschitzWith_circleMap c R).lipschitzOnWith (s := Icc a (a + 2 * π)))
    ((injOn_circleMap_of_abs_sub_le' hR (by simp)).mono Ioo_subset_Ico_self)
  have hd : (fun t ↦ ‖deriv (circleMap c R) t‖ₑ) = fun _ ↦ ENNReal.ofReal |R| :=
    funext fun t ↦ by simp [deriv_circleMap, ← ofReal_norm]
  rwa [hd, withDensity_const, Measure.map_smul, himage] at h
  exact (continuous_circleMap c R).aemeasurable

/-- **The length of a short arc.** For `0 < r ≤ 2ρ`, the arc of the circle `sphere c ρ` within
distance `r` of a point `x` on it has length `4ρ arcsin (r / (2ρ))`. -/
theorem _root_.Complex.euclideanHausdorffMeasure_sphere_inter_ball (c : ℂ) {ρ r : ℝ} (hρ : 0 < ρ)
    (hr : 0 < r) (hr2 : r ≤ 2 * ρ) {x : ℂ} (hx : x ∈ sphere c ρ) :
    μHE[1] (sphere c ρ ∩ ball x r) = ENNReal.ofReal (4 * ρ * arcsin (r / (2 * ρ))) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, circleMap c ρ φ = x := by
    rw [← mem_range, range_circleMap, abs_of_pos hρ]
    exact hx
  have hμ := smul_map_volume_restrict_circleMap c ρ (φ - π)
  rw [abs_of_pos hρ, show φ - π + 2 * π = φ + π by ring] at hμ
  rw [inter_comm, ← Measure.restrict_apply measurableSet_ball, ← hμ, smul_apply,
    Measure.map_apply (continuous_circleMap c ρ).measurable measurableSet_ball,
    Measure.restrict_apply (measurableSet_ball.preimage (continuous_circleMap c ρ).measurable),
    preimage_circleMap_ball_inter_Icc c hρ hr hr2, Real.volume_Ioo, smul_eq_mul,
    ← ENNReal.ofReal_mul hρ.le]
  congr 1
  ring

end TauCeti
