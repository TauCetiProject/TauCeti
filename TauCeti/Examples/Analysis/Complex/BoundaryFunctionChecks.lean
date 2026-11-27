/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Boundary.Function
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# Checks for boundary functions of bounded holomorphic functions on the half-plane

Explicit boundary functions `F*` (`TauCeti.upperHalfPlaneBoundaryFun`).

* *The exponential.* For `F(z) = e^{iz}`, `|F(x + iy)| = e^{-y}`
  (`norm_exp_mul_I_ofReal_add_mul_I`), so `F` is bounded by `1` on `ℂ₊`; its boundary function is
  `F*(x) = e^{ix}` (`upperHalfPlaneBoundaryFun_exp_mul_I`), and `F = P[F*]` on `ℂ₊`
  (`exp_mul_I_eq_upperHalfPlanePoissonIntegralFun`).
* *A constant.* The boundary function of `c` is `c` (`TauCeti.upperHalfPlaneBoundaryFun_const`).
* *A Blaschke factor.* For `F(z) = (z - i) / (z + i)`, `F*(x) = (x - i) / (x + i)` has modulus `1`
  everywhere (`norm_upperHalfPlaneBoundaryFun_blaschke`), so `log|F*| = 0`
  (`log_norm_upperHalfPlaneBoundaryFun_blaschke`) and `P[log|F*|](i) = 0`
  (`upperHalfPlanePoissonIntegralFun_log_norm_blaschke`), while `F(i) = 0`, so
  `log|F(i)| = -∞ ≤ 0` (`log_enorm_blaschke_I`, `log_enorm_blaschke_I_le`).
* *An essential singularity on the boundary.* For `F(z) = e^{-i/z}`,
  `|F(z)| = e^{-Im z / |z|²}` (`norm_exp_neg_I_div`), so `|F| ≤ 1` on `ℂ₊`
  (`norm_exp_neg_I_div_le_one`), but `F` has no limit at `0` within `ℂ₊`
  (`not_tendsto_exp_neg_I_div_zero`): it tends to `0` along the imaginary axis and has modulus
  tending to `e^{-1}` along the parabola `t + i t²`. Still `F*(x) = e^{-i/x}` for `x ≠ 0`
  (`upperHalfPlaneBoundaryFun_exp_neg_I_div`) and `F = P[F*]` on `ℂ₊`
  (`exp_neg_I_div_eq_upperHalfPlanePoissonIntegralFun`). Its Cayley transform is
  `g(w) = exp(-(1 - w) / (1 + w))` (`exp_neg_I_div_I_mul_one_add_div_one_sub`), with no limit at
  `w = -1` within the disc (`not_tendsto_exp_neg_one_sub_div_one_add_neg_one`) and `log|g| < 0` on
  the open disc (`log_norm_exp_neg_one_sub_div_one_add_lt_zero`). The logarithmic bound at `i` is
  strict: `log|F(i)| = -1` (`log_norm_exp_neg_I_div_I`) while `P[log|F*|](i) = 0`
  (`upperHalfPlanePoissonIntegralFun_log_norm_exp_neg_I_div`).
-/

public section

noncomputable section

namespace TauCeti.Examples.BoundaryFunction

open Complex Filter MeasureTheory Set Topology
open _root_.UpperHalfPlane (upperHalfPlaneSet)

/-! ### The exponential `e^{iz}` -/

/-- `|e^{i(x + iy)}| = e^{-y}`. -/
theorem norm_exp_mul_I_ofReal_add_mul_I (x y : ℝ) :
    ‖exp (I * ((x : ℂ) + y * I))‖ = Real.exp (-y) := by
  rw [norm_exp]
  congr 1
  simp

/-- `e^{iz}` is bounded by `1` on the upper half-plane. -/
theorem norm_exp_mul_I_le_one {z : ℂ} (hz : z ∈ upperHalfPlaneSet) : ‖exp (I * z)‖ ≤ 1 := by
  rw [norm_exp, Real.exp_le_one_iff]
  simpa using (le_of_lt (show 0 < z.im from hz))

/-- The boundary function of `e^{iz}` is `e^{ix}`. -/
theorem upperHalfPlaneBoundaryFun_exp_mul_I (x : ℝ) :
    upperHalfPlaneBoundaryFun (fun z ↦ exp (I * z)) x = exp (I * x) :=
  upperHalfPlaneBoundaryFun_eq_of_continuousOn (by fun_prop) x

/-- `e^{iz} = P[e^{ix}](z)` on the upper half-plane. -/
theorem exp_mul_I_eq_upperHalfPlanePoissonIntegralFun {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    exp (I * z) = upperHalfPlanePoissonIntegralFun (fun x : ℝ ↦ exp (I * x)) z := by
  rw [eq_upperHalfPlanePoissonIntegralFun_upperHalfPlaneBoundaryFun (S := 1)
    (fun w _ ↦ by fun_prop) (fun w hw ↦ norm_exp_mul_I_le_one hw) hz]
  rw [funext upperHalfPlaneBoundaryFun_exp_mul_I]

/-! ### A Blaschke factor -/

/-- The boundary function of `(z - i) / (z + i)` has modulus `1` everywhere. -/
theorem norm_upperHalfPlaneBoundaryFun_blaschke (x : ℝ) :
    ‖upperHalfPlaneBoundaryFun (fun z ↦ (z - I) / (z + I)) x‖ = 1 := by
  rw [upperHalfPlaneBoundaryFun_eq_of_continuousWithinAt
    (continuousAt_sub_I_div_add_I x).continuousWithinAt, norm_div, norm_sub_I_div_norm_add_I_ofReal]

/-- `log|F*| = 0` for the Blaschke factor `F(z) = (z - i) / (z + i)`. -/
theorem log_norm_upperHalfPlaneBoundaryFun_blaschke (x : ℝ) :
    Real.log ‖upperHalfPlaneBoundaryFun (fun z ↦ (z - I) / (z + I)) x‖ = 0 := by
  rw [norm_upperHalfPlaneBoundaryFun_blaschke, Real.log_one]

/-- `P[log|F*|](i) = 0` for the Blaschke factor `F(z) = (z - i) / (z + i)`. -/
theorem upperHalfPlanePoissonIntegralFun_log_norm_blaschke :
    upperHalfPlanePoissonIntegralFun
      (fun x ↦ (Real.log ‖upperHalfPlaneBoundaryFun (fun z ↦ (z - I) / (z + I)) x‖ : ℂ)) I = 0 := by
  simp_rw [log_norm_upperHalfPlaneBoundaryFun_blaschke, ofReal_zero]
  exact upperHalfPlanePoissonIntegralFun_const 0 (by simp)

/-- The Blaschke factor `F(z) = (z - i) / (z + i)` vanishes at `i`: `log|F(i)| = -∞`. -/
theorem log_enorm_blaschke_I : ENNReal.log ‖(I - I) / (I + I)‖ₑ = ⊥ := by
  simp

/-- The logarithmic bound `log|F(i)| ≤ P[log|F*|](i)` for the Blaschke factor
`F(z) = (z - i) / (z + i)`, where it reads `-∞ ≤ 0`. -/
theorem log_enorm_blaschke_I_le :
    ENNReal.log ‖(I - I) / (I + I)‖ₑ ≤
      (((upperHalfPlanePoissonIntegralFun fun x ↦
        (Real.log ‖upperHalfPlaneBoundaryFun (fun z ↦ (z - I) / (z + I)) x‖ : ℂ)) I).re :
        EReal) := by
  rw [log_enorm_blaschke_I]
  exact bot_le

/-! ### The function `e^{-i/z}` -/

/-- `|e^{-i/z}| = e^{-Im z / |z|²}`. -/
theorem norm_exp_neg_I_div (z : ℂ) : ‖exp (-I / z)‖ = Real.exp (-(z.im / normSq z)) := by
  rw [norm_exp]
  congr 1
  simp [div_re, neg_div]

/-- `e^{-i/z}` is bounded by `1` on the upper half-plane. -/
theorem norm_exp_neg_I_div_le_one {z : ℂ} (hz : z ∈ upperHalfPlaneSet) : ‖exp (-I / z)‖ ≤ 1 := by
  rw [norm_exp_neg_I_div, Real.exp_le_one_iff, neg_nonpos]
  exact div_nonneg (le_of_lt hz) (normSq_nonneg z)

/-- `e^{-i/z}` is holomorphic on the upper half-plane. -/
theorem differentiableOn_exp_neg_I_div :
    DifferentiableOn ℂ (fun z ↦ exp (-I / z)) upperHalfPlaneSet := fun _ hz ↦
  ((differentiableAt_const _).div differentiableAt_id
    (ne_of_apply_ne im (ne_of_gt hz))).cexp.differentiableWithinAt

/-- `e^{-i/(it)} = e^{-1/t}`. -/
private theorem exp_neg_I_div_I_mul (t : ℝ) : exp (-I / (t * I)) = Real.exp (-t⁻¹) := by
  rcases eq_or_ne t 0 with rfl | _
  · simp
  rw [ofReal_exp]
  congr 1
  push_cast
  field_simp

/-- `|e^{-i/z}|` at `z = t + i t²` is `e^{-1/(1 + t²)}`. -/
private theorem norm_exp_neg_I_div_parabola {t : ℝ} (ht : t ≠ 0) :
    ‖exp (-I / (t + (t ^ 2 : ℝ) * I))‖ = Real.exp (-(1 + t ^ 2)⁻¹) := by
  rw [norm_exp_neg_I_div, normSq_add_mul_I]
  congr 2
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one, zero_add]
  field_simp
  ring

/-- **`e^{-i/z}` has no limit at `0` within the upper half-plane**: it tends to `0` along the
imaginary axis, while its modulus tends to `e^{-1}` along the parabola `t + i t²`. -/
theorem not_tendsto_exp_neg_I_div_zero (c : ℂ) :
    ¬ Tendsto (fun z ↦ exp (-I / z)) (𝓝[upperHalfPlaneSet] 0) (𝓝 c) := by
  intro hc
  have hpath {γ : ℝ → ℂ} (hγ : Continuous γ) (h0 : γ 0 = 0) (hpos : ∀ t > 0, 0 < (γ t).im) :
      Tendsto γ (𝓝[>] 0) (𝓝[upperHalfPlaneSet] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0 ▸ (hγ.tendsto 0).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun t ht ↦ hpos t ht⟩
  -- along the imaginary axis the limit is `0`
  have h1 : Tendsto (fun t : ℝ ↦ exp (-I / (t * I))) (𝓝[>] 0) (𝓝 0) := by
    simp_rw [exp_neg_I_div_I_mul]
    have := (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero))
    exact (continuous_ofReal.tendsto' 0 0 ofReal_zero).comp
      (by simpa [Function.comp_def] using this)
  have hc0 : c = 0 := tendsto_nhds_unique (hc.comp (hpath (by fun_prop) (by simp)
    fun t ht ↦ by simpa using ht)) h1
  -- along the parabola the modulus tends to `e^{-1}`
  have h2 : Tendsto (fun t : ℝ ↦ ‖exp (-I / (t + (t ^ 2 : ℝ) * I))‖) (𝓝[>] 0)
      (𝓝 (Real.exp (-1))) := by
    refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun t ht ↦
      (norm_exp_neg_I_div_parabola (ne_of_gt ht)).symm) ?_
    have : Continuous fun t : ℝ ↦ Real.exp (-(1 + t ^ 2)⁻¹) :=
      Real.continuous_exp.comp ((continuous_const.add (continuous_pow 2)).inv₀
        fun t ↦ (by positivity : (0 : ℝ) < 1 + t ^ 2).ne').neg
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hpar := (hc.comp (hpath (γ := fun t : ℝ ↦ (t : ℂ) + (t ^ 2 : ℝ) * I) (by fun_prop) (by simp)
    fun t ht ↦ by
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add]
      positivity)).norm
  rw [hc0, norm_zero] at hpar
  exact (Real.exp_pos (-1)).ne' (tendsto_nhds_unique h2 hpar)

/-- The boundary function of `e^{-i/z}` is `e^{-i/x}` away from `0`. -/
theorem upperHalfPlaneBoundaryFun_exp_neg_I_div {x : ℝ} (hx : x ≠ 0) :
    upperHalfPlaneBoundaryFun (fun z ↦ exp (-I / z)) x = exp (-I / x) :=
  upperHalfPlaneBoundaryFun_eq_of_continuousWithinAt (by fun_prop (disch := exact_mod_cast hx))

/-- `e^{-i/z} = P[e^{-i/x}](z)` on the upper half-plane, although `e^{-i/z}` is not continuous at
`0`. -/
theorem exp_neg_I_div_eq_upperHalfPlanePoissonIntegralFun {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    exp (-I / z) = upperHalfPlanePoissonIntegralFun (fun x : ℝ ↦ exp (-I / x)) z := by
  rw [eq_upperHalfPlanePoissonIntegralFun_upperHalfPlaneBoundaryFun (S := 1)
    differentiableOn_exp_neg_I_div (fun w hw ↦ norm_exp_neg_I_div_le_one hw) hz,
    upperHalfPlanePoissonIntegralFun_def, upperHalfPlanePoissonIntegralFun_def]
  refine integral_congr_ae ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  rw [upperHalfPlaneBoundaryFun_exp_neg_I_div hx]

/-- The Cayley transform of `e^{-i/z}`: at `z = i (1 + w) / (1 - w)`, `e^{-i/z}` is
`g(w) = exp(-(1 - w) / (1 + w))`. -/
theorem exp_neg_I_div_I_mul_one_add_div_one_sub (w : ℂ) :
    exp (-I / (I * (1 + w) / (1 - w))) = exp (-((1 - w) / (1 + w))) := by
  rw [div_div_eq_mul_div, neg_mul, neg_div, mul_div_mul_left _ _ I_ne_zero]

/-- The Cayley transform `g(w) = exp(-(1 - w) / (1 + w))` of `e^{-i/z}` has no limit at `w = -1`
within the open unit disc. -/
theorem not_tendsto_exp_neg_one_sub_div_one_add_neg_one (c : ℂ) :
    ¬ Tendsto (fun w ↦ exp (-((1 - w) / (1 + w)))) (𝓝[Metric.ball 0 1] (-1)) (𝓝 c) := by
  intro hc
  refine not_tendsto_exp_neg_I_div_zero c
    ((hc.comp (f := fun z : ℂ ↦ (z - I) / (z + I)) ?_).congr' ?_)
  · refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz ↦
      bijOn_sub_I_div_add_I_upperHalfPlaneSet.mapsTo hz⟩
    have : ContinuousAt (fun z : ℂ ↦ (z - I) / (z + I)) 0 :=
      (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const)
        (by simp)
    simpa [ContinuousAt, I_ne_zero] using this.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hzI : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg (le_of_lt hz)
    simp only [Function.comp_apply]
    rw [← exp_neg_I_div_I_mul_one_add_div_one_sub, I_mul_one_add_sub_I_div_add_I_div_one_sub hzI]

/-- `log|g| < 0` on the open unit disc for the Cayley transform `g(w) = exp(-(1 - w) / (1 + w))`
of `e^{-i/z}`; in particular `log|g| ≤ 0` on every circle of radius `r < 1`. -/
theorem log_norm_exp_neg_one_sub_div_one_add_lt_zero {w : ℂ} (hw : w ∈ Metric.ball 0 1) :
    Real.log ‖exp (-((1 - w) / (1 + w)))‖ < 0 := by
  obtain ⟨z, hz, rfl⟩ := bijOn_sub_I_div_add_I_upperHalfPlaneSet.surjOn hw
  have hzI : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg (le_of_lt hz)
  have hz0 : z ≠ 0 := ne_of_apply_ne im (ne_of_gt hz)
  rw [← exp_neg_I_div_I_mul_one_add_div_one_sub, I_mul_one_add_sub_I_div_add_I_div_one_sub hzI,
    norm_exp_neg_I_div, Real.log_exp, neg_lt_zero]
  exact div_pos hz (normSq_pos.2 hz0)

/-- `log|e^{-i/z}|` at `z = i` is `-1`. -/
theorem log_norm_exp_neg_I_div_I : Real.log ‖exp (-I / I)‖ = -1 := by
  rw [norm_exp_neg_I_div, Real.log_exp]
  simp

/-- `P[log|F*|](i) = 0` for `F(z) = e^{-i/z}`: `|F*| = 1` almost everywhere. With
`log_norm_exp_neg_I_div_I` the logarithmic bound `log|F(i)| ≤ P[log|F*|](i)` is strict,
`-1 < 0`. -/
theorem upperHalfPlanePoissonIntegralFun_log_norm_exp_neg_I_div :
    upperHalfPlanePoissonIntegralFun
      (fun x ↦ (Real.log ‖upperHalfPlaneBoundaryFun (fun z ↦ exp (-I / z)) x‖ : ℂ)) I = 0 := by
  rw [← upperHalfPlanePoissonIntegralFun_const 0 (z := I) (by simp),
    upperHalfPlanePoissonIntegralFun_def, upperHalfPlanePoissonIntegralFun_def]
  refine integral_congr_ae ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  rw [upperHalfPlaneBoundaryFun_exp_neg_I_div hx, norm_exp_neg_I_div, Real.log_exp]
  simp

end TauCeti.Examples.BoundaryFunction
