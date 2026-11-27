/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentialFDeriv
public import TauCeti.MeasureTheory.Function.AreaFormula.Circle
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Topology.Circle.Metric

/-!
# Check: the tangential area formula for the projection of the circle onto a line

Let `M` be the unit circle `sphere (0 : ℂ) 1` in `ℂ = ℝ²`, `k = 1`, and `f(x, y) = x` the real
part. Both sides of the tangential area formula `∫_M J^M f dH¹ = ∫_ℝ #(M ∩ f⁻¹(t)) dt` are `4`:

* at `e^{iθ}` the tangential Jacobian of `f` along `M` is `|sin θ|`
  (`tangentialJacobian_re_circleMap`), computed from the chart `circleMap 0 1` on
  `(θ - π / 2, θ + π / 2)` by `HasFDerivWithinAt.tangentialJacobian_mul_normDet`; at a point `z`
  of `M` it is `|Im z|` (`tangentialJacobian_re`);
* so the left side is `∫_0^{2π} |sin θ| dθ = 4` (`lintegral_tangentialJacobian_re`);
* the fibre `M ∩ f⁻¹(t)` has two points for `-1 < t < 1` (`encard_fibre_of_abs_lt`) and none for
  `|t| > 1` (`fibre_eq_empty_of_one_lt_abs`), so the right side is `2 · 2 = 4`
  (`lintegral_encard_fibre`).

The full derivative `Df = (1, 0)` gives other numbers: its norm determinant as a map `ℝ² → ℝ` is
`0`, since it is not injective (`normDet_reCLM`), and integrating its norm `1` over `M` gives the
length `2π` (`lintegral_norm_reCLM`).

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §12 (the area formula on rectifiable sets).
-/

open MeasureTheory Measure Set Metric Module Filter Topology Function Real
open scoped ENNReal NNReal

public noncomputable section

namespace TauCeti.Examples.CircleProjection

open TauCeti

/-- The chord between two points of the unit circle at angles less than half a turn apart is at
least `2 / π` times the angular gap (Jordan's inequality). -/
private theorem abs_sub_le_mul_dist_circleMap {a b : ℝ} (hab : |a - b| ≤ π) :
    |a - b| ≤ π / 2 * dist (circleMap 0 1 a) (circleMap 0 1 b) := by
  rw [dist_circleMap_eq_two_mul_sin_abs 0 1 (by linarith [pi_pos]), abs_one, mul_one]
  have h := mul_le_sin (x := |a - b| / 2) (by positivity) (by linarith)
  have := pi_pos
  calc |a - b| = π / 2 * (2 * (2 / π * (|a - b| / 2))) := by field_simp
    _ ≤ π / 2 * (2 * sin (|a - b| / 2)) := by gcongr

/-- On the open half-turn `(θ - π / 2, θ + π / 2)`, the chart `circleMap 0 1` is inverse-Lipschitz
with constant `π / 2`. -/
private theorem antilipschitzWith_domRestrict_circleMap (θ : ℝ) :
    AntilipschitzWith (Real.toNNReal (π / 2))
      ((Ioo (θ - π / 2) (θ + π / 2)).domRestrict (circleMap 0 1)) :=
  AntilipschitzWith.of_le_mul_dist fun a b ↦ by
    rw [Real.coe_toNNReal _ (by positivity)]
    refine (abs_sub_le_mul_dist_circleMap ?_ : |(a : ℝ) - b| ≤ _)
    have ha := a.property
    have hb := b.property
    exact abs_le.2 ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩

/-- A point of the unit circle within distance `1` of `e^{iθ}` is `e^{iφ}` for an angle `φ` with
`|φ - θ| < π / 2`. -/
private theorem exists_eq_circleMap_of_dist_lt_one {θ : ℝ} {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1)
    (hd : dist z (circleMap 0 1 θ) < 1) : ∃ φ, |φ - θ| < π / 2 ∧ circleMap 0 1 φ = z := by
  have hz' : z ∈ circleMap 0 1 '' Ioc (θ - π) (θ - π + 2 * π) := by
    rw [(periodic_circleMap 0 1).image_Ioc two_pi_pos, range_circleMap, abs_one]
    exact hz
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, rfl⟩ := hz'
  refine ⟨φ, lt_of_not_ge fun h ↦ hd.not_ge ?_, rfl⟩
  have hφ : |φ - θ| ≤ π := abs_le.2 ⟨by linarith, by linarith⟩
  have hle := dist_circleMap_le_dist_circleMap_of_abs_sub_le 0 1 (u := θ + π / 2)
    (by rwa [add_sub_cancel_left, abs_of_pos (by positivity)]) hφ
  refine le_trans ?_ hle
  rw [dist_circleMap_eq_two_mul_abs_sin, add_sub_cancel_left, abs_one,
    show π / 2 / 2 = π / 4 by ring, sin_pi_div_four, abs_of_pos (by positivity)]
  nlinarith [one_lt_sqrt_two]

/-- **The tangential Jacobian of the projection along the circle.** At `e^{iθ}` the tangential
Jacobian of the real part along the unit circle is `|sin θ|`. -/
theorem tangentialJacobian_re_circleMap (θ : ℝ) :
    tangentialJacobian 1 (sphere (0 : ℂ) 1) (fun z : ℂ ↦ z.re) (circleMap 0 1 θ) = |sin θ| := by
  set s : Set ℝ := Ioo (θ - π / 2) (θ + π / 2)
  have hθ : θ ∈ s := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  set v : ℂ := circleMap 0 1 θ * Complex.I
  let A : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight v
  have hf : HasFDerivWithinAt (circleMap 0 1) A s θ :=
    (hasDerivAt_circleMap 0 1 θ).hasFDerivAt.hasFDerivWithinAt
  have hv : ‖v‖ = 1 := by simp [v]
  have hinj : Injective A := fun a b h ↦ by
    have h' : a • v = b • v := by simpa [A] using h
    exact smul_left_injective ℝ (norm_ne_zero_iff.mp (hv ▸ one_ne_zero)) h'
  have hi := antilipschitzWith_domRestrict_circleMap θ
  have hsub : circleMap 0 1 '' s ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨t, -, rfl⟩
    exact circleMap_mem_sphere 0 zero_le_one t
  have hdens : Tendsto (fun r ↦ volume (s ∩ closedBall θ r) / volume (closedBall (0 : ℝ) r))
      (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < π / 2)] with r ⟨hr, hrπ⟩
    have hsub' : closedBall θ r ⊆ s := by
      rw [Real.closedBall_eq_Icc]
      exact Icc_subset_Ioo (by linarith) (by linarith)
    rw [inter_eq_right.2 hsub', Real.volume_closedBall, Real.volume_closedBall,
      ENNReal.div_self (by simpa using hr) ENNReal.ofReal_ne_top]
  have hdiff : Tendsto (fun r ↦ μHE[finrank ℝ ℝ]
      ((sphere (0 : ℂ) 1 \ circleMap 0 1 '' s) ∩ closedBall (circleMap 0 1 θ) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ ℝ))) r)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with r ⟨_, hr⟩
    rw [eq_comm, ENNReal.div_eq_zero_iff]
    left
    convert measure_empty (μ := μHE[finrank ℝ ℝ])
    refine eq_empty_of_forall_notMem fun z ⟨⟨hz, hzs⟩, hzr⟩ ↦ hzs ?_
    obtain ⟨φ, hφ, rfl⟩ := exists_eq_circleMap_of_dist_lt_one hz
      ((mem_closedBall.mp hzr).trans_lt hr)
    exact ⟨φ, ⟨by linarith [(abs_lt.1 hφ).1], by linarith [(abs_lt.1 hφ).2]⟩, rfl⟩
  have hgf : HasFDerivWithinAt ((fun z : ℂ ↦ z.re) ∘ circleMap 0 1)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (-sin θ)) s θ := by
    have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 1 θ))
    have hre : Complex.reCLM v = -sin θ := by
      simp [v, circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [hre] at h
    exact h.hasFDerivAt.hasFDerivWithinAt
  have h := hf.tangentialJacobian_mul_normDet hinj hi hθ hsub hdens hdiff hgf
  have hnA : A.toLinearMap.normDet = 1 := by
    rw [LinearMap.normDet_eq_norm_apply_one]
    simpa [A] using hv
  rw [finrank_self, hnA, mul_one, LinearMap.normDet_eq_norm_apply_one] at h
  simpa using h

/-- At a point `z` of the unit circle, the tangential Jacobian of the real part along the circle
is `|Im z|`. -/
theorem tangentialJacobian_re {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    tangentialJacobian 1 (sphere (0 : ℂ) 1) (fun z : ℂ ↦ z.re) z = |z.im| := by
  obtain ⟨θ, rfl⟩ : z ∈ range (circleMap 0 1) := by rwa [range_circleMap, abs_one]
  rw [tangentialJacobian_re_circleMap]
  simp [circleMap, Complex.exp_ofReal_mul_I_im]

/-- `∫_0^{2π} |sin θ| dθ = 4`. -/
private theorem integral_abs_sin : ∫ θ in (0 : ℝ)..2 * π, |sin θ| = 4 := by
  have h₁ : ∫ θ in (0 : ℝ)..π, |sin θ| = 2 := by
    rw [intervalIntegral.integral_congr fun θ hθ ↦ abs_of_nonneg
      (sin_nonneg_of_nonneg_of_le_pi (uIcc_of_le pi_pos.le ▸ hθ).1
        (uIcc_of_le pi_pos.le ▸ hθ).2)]
    simp [integral_sin]
    norm_num
  have h₂ : ∫ θ in π..2 * π, |sin θ| = 2 := by
    have h := intervalIntegral.integral_comp_add_right (fun θ ↦ |sin θ|) π (a := 0) (b := π)
    simp only [sin_add_pi, abs_neg, zero_add] at h
    rw [two_mul, ← h, h₁]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π), h₁, h₂]
  · norm_num
  all_goals exact (continuous_abs.comp continuous_sin).intervalIntegrable _ _

/-- **The left side of the area formula.** The tangential Jacobian of the real part integrates to
`∫_0^{2π} |sin θ| dθ = 4` over the unit circle. -/
theorem lintegral_tangentialJacobian_re :
    ∫⁻ z in sphere (0 : ℂ) 1,
      ENNReal.ofReal (tangentialJacobian 1 (sphere (0 : ℂ) 1) (fun z : ℂ ↦ z.re) z) ∂μHE[1] =
      4 := by
  rw [setLIntegral_congr_fun isClosed_sphere.measurableSet fun z hz ↦ by
    rw [tangentialJacobian_re hz]]
  have hμ := smul_map_volume_restrict_circleMap 0 1 0
  rw [abs_one, zero_add, ENNReal.ofReal_one, one_smul] at hμ
  rw [← hμ, lintegral_map (Complex.continuous_im.abs.measurable.ennreal_ofReal)
    (continuous_circleMap 0 1).measurable]
  have him (θ : ℝ) : (circleMap 0 1 θ).im = sin θ := by
    simp [circleMap, Complex.exp_ofReal_mul_I_im]
  simp_rw [him]
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun θ ↦ |sin θ|)
    ((by fun_prop : Continuous fun θ : ℝ ↦ |sin θ|).integrableOn_Icc)
    (.of_forall fun θ ↦ abs_nonneg _), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity), integral_abs_sin]
  norm_num

/-- The fibre of the real part over `t` on the unit circle consists of the points `t + is` with
`s² = 1 - t²`. -/
theorem fibre_eq (t : ℝ) :
    sphere (0 : ℂ) 1 ∩ (fun z : ℂ ↦ z.re) ⁻¹' {t} =
      (fun s : ℝ ↦ (⟨t, s⟩ : ℂ)) '' {s | s ^ 2 = 1 - t ^ 2} := by
  ext z
  simp only [mem_inter_iff, mem_sphere_zero_iff_norm, mem_preimage, mem_singleton_iff,
    mem_image, mem_ofPred_eq]
  have hn : ‖z‖ = 1 ↔ z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [← h, ← sq_eq_sq₀ (norm_nonneg z) zero_le_one, one_pow]
  rw [hn]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨z.im, by linarith, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨by simp only; linarith, rfl⟩

/-- Over `-1 < t < 1` the fibre of the real part on the unit circle has two points. -/
theorem encard_fibre_of_abs_lt {t : ℝ} (ht : |t| < 1) :
    (sphere (0 : ℂ) 1 ∩ (fun z : ℂ ↦ z.re) ⁻¹' {t}).encard = 2 := by
  have hc : 0 < 1 - t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  have hroots : {s : ℝ | s ^ 2 = 1 - t ^ 2} = {√(1 - t ^ 2), -√(1 - t ^ 2)} := by
    ext s
    have h := sq_eq_sq_iff_eq_or_eq_neg (a := s) (b := √(1 - t ^ 2))
    rw [Real.sq_sqrt hc.le] at h
    rw [mem_ofPred_eq, h, mem_insert_iff, mem_singleton_iff]
  have hinj : Injective fun s : ℝ ↦ (⟨t, s⟩ : ℂ) := fun a b h ↦ congrArg Complex.im h
  rw [fibre_eq, hroots, hinj.encard_image, encard_pair]
  have := Real.sqrt_pos.2 hc
  linarith

/-- Over `|t| > 1` the fibre of the real part on the unit circle is empty. -/
theorem fibre_eq_empty_of_one_lt_abs {t : ℝ} (ht : 1 < |t|) :
    sphere (0 : ℂ) 1 ∩ (fun z : ℂ ↦ z.re) ⁻¹' {t} = ∅ := by
  rw [fibre_eq, image_eq_empty]
  refine eq_empty_of_forall_notMem fun s (hs : s ^ 2 = 1 - t ^ 2) ↦ ?_
  nlinarith [sq_nonneg s, sq_abs t, abs_nonneg t]

/-- **The right side of the area formula.** The number of points of the circle over `t` integrates
to `2 · 2 = 4` against Lebesgue measure, which is `H¹` on `ℝ`. -/
theorem lintegral_encard_fibre :
    ∫⁻ t, ((sphere (0 : ℂ) 1 ∩ (fun z : ℂ ↦ z.re) ⁻¹' {t}).encard : ℝ≥0∞) = 4 := by
  have h : (fun t ↦ ((sphere (0 : ℂ) 1 ∩ (fun z : ℂ ↦ z.re) ⁻¹' {t}).encard : ℝ≥0∞)) =ᵐ[volume]
      (Ioo (-1 : ℝ) 1).indicator fun _ ↦ 2 := by
    filter_upwards [Measure.ae_ne volume (1 : ℝ), Measure.ae_ne volume (-1 : ℝ)] with t h₁ h₂
    rcases lt_or_gt_of_ne (show |t| ≠ 1 from fun h ↦ (abs_eq zero_le_one).1 h |>.elim h₁ h₂)
      with ht | ht
    · rw [encard_fibre_of_abs_lt ht, indicator_of_mem (abs_lt.1 ht)]
      rfl
    · rw [fibre_eq_empty_of_one_lt_abs ht, encard_empty, indicator_of_notMem fun h ↦
        ht.not_gt (abs_lt.2 h)]
      simp
  rw [lintegral_congr_ae h, lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo]
  norm_num

/-- **Both sides of the area formula agree.** `∫_M J^M f dH¹ = ∫_ℝ #(M ∩ f⁻¹(t)) dt`. -/
theorem lintegral_tangentialJacobian_re_eq_lintegral_encard :
    ∫⁻ z in sphere (0 : ℂ) 1,
      ENNReal.ofReal (tangentialJacobian 1 (sphere (0 : ℂ) 1) (fun z : ℂ ↦ z.re) z) ∂μHE[1] =
      ∫⁻ t, ((sphere (0 : ℂ) 1 ∩ (fun z : ℂ ↦ z.re) ⁻¹' {t}).encard : ℝ≥0∞) := by
  rw [lintegral_tangentialJacobian_re, lintegral_encard_fibre]

/-- The full derivative `Df = (1, 0)` of the real part, a map `ℝ² → ℝ`, is not injective, so its
norm determinant is `0`. -/
theorem normDet_reCLM : Complex.reCLM.toLinearMap.normDet = 0 :=
  LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 fun h ↦ Complex.I_ne_zero <|
    (LinearMap.ker_eq_bot'.1 h) Complex.I (by simp)

/-- Integrating the norm `1` of the full derivative `Df = (1, 0)` over the unit circle gives its
length `2π`, not `4`. -/
theorem lintegral_norm_reCLM :
    ∫⁻ _ in sphere (0 : ℂ) 1, ‖Complex.reCLM‖ₑ ∂μHE[1] = ENNReal.ofReal (2 * π) := by
  rw [setLIntegral_const, Complex.euclideanHausdorffMeasure_sphere, ← ofReal_norm,
    Complex.reCLM_norm, ENNReal.ofReal_one, one_mul, mul_one]

end TauCeti.Examples.CircleProjection
