/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Atoms
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic integrals on the imaginary axis

For a finite real measure, differentiating the regularized logarithmic integral in the
height gives the imaginary part of the resolvent transform. For a probability measure,
subtracting the logarithm of the height gives a function tending to zero at infinity.
At height zero, the logarithmic integral is recovered when the transform is bounded
near zero and the measure has an integrable logarithmic moment at infinity.
-/

public section

open Filter Set
open scoped Topology

namespace MeasureTheory

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- A finite second moment implies integrability of the nonnegative logarithm of one plus
the square. -/
theorem integrable_log_sq_add_one (h : Integrable (fun x : ℝ ↦ x ^ 2) μ) :
    Integrable (fun x ↦ Real.log (x ^ 2 + 1)) μ := by
  refine h.mono ((Real.measurable_log.comp (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun x ↦ ?_)
  have hle := Real.log_le_sub_one_of_pos (show 0 < x ^ 2 + 1 by positivity)
  have hnonneg := Real.log_nonneg (le_add_of_nonneg_left (sq_nonneg x))
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (sq_nonneg x)]
  linarith

omit [IsFiniteMeasure μ] in
private theorem measurable_half_log_add_sq (t : ℝ) :
    Measurable (fun x : ℝ ↦ Real.log (x ^ 2 + t ^ 2) / 2) :=
  (Real.measurable_log.comp (by fun_prop)).div_const 2

private theorem hasDerivAt_half_log_add_sq (x : ℝ) {η : ℝ} (hη : η ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ Real.log (x ^ 2 + t ^ 2) / 2)
      (η / (x ^ 2 + η ^ 2)) η := by
  have hd := (hasDerivAt_pow 2 η).const_add (x ^ 2)
  convert (hd.log (by positivity : x ^ 2 + η ^ 2 ≠ 0)).div_const 2 using 1
  simp only [Nat.cast_two, Nat.reduceSub, pow_one]
  ring

/-- The assumption of a logarithmic moment at infinity suffices for integrability at every
positive height. -/
theorem integrable_half_log_add_sq (hlog : Integrable (fun x ↦ Real.log (x ^ 2 + 1)) μ)
    {η : ℝ} (hη : η ≠ 0) :
    Integrable (fun x ↦ Real.log (x ^ 2 + η ^ 2) / 2) μ := by
  refine (hlog.add (integrable_const |Real.log (η ^ 2)|)).mono
    (measurable_half_log_add_sq η).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  have hpos : 0 < x ^ 2 + η ^ 2 := by positivity
  have hlo := Real.log_le_log (by positivity : 0 < η ^ 2)
    (le_add_of_nonneg_left (sq_nonneg x) : η ^ 2 ≤ x ^ 2 + η ^ 2)
  have hhi := Real.log_le_log hpos (y := (x ^ 2 + 1) * max 1 (η ^ 2)) (by
    calc
      x ^ 2 + η ^ 2 ≤ x ^ 2 * max 1 (η ^ 2) + max 1 (η ^ 2) :=
        add_le_add (le_mul_of_one_le_right (sq_nonneg _) (le_max_left _ _)) (le_max_right _ _)
      _ = _ := by ring)
  rw [Real.log_mul (by positivity) (by positivity)] at hhi
  have hmax : Real.log (max 1 (η ^ 2)) ≤ |Real.log (η ^ 2)| := by
    rcases le_total 1 (η ^ 2) with h | h
    · rw [max_eq_right h]
      exact le_abs_self _
    · simp [max_eq_left h]
  have hx : 0 ≤ Real.log (x ^ 2 + 1) := Real.log_nonneg (by nlinarith [sq_nonneg x])
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (add_nonneg hx (abs_nonneg _))]
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log (η ^ 2)), abs_nonneg (Real.log (η ^ 2))],
    by linarith [abs_nonneg (Real.log (η ^ 2))]⟩

/-- The vertical derivative of the regularized logarithmic integral at a nonzero height is
the imaginary part of the resolvent transform. -/
theorem hasDerivAt_integral_half_log_add_sq
    (hlog : Integrable (fun x ↦ Real.log (x ^ 2 + 1)) μ) {η : ℝ} (hη : η ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, Real.log (x ^ 2 + t ^ 2) / 2 ∂μ)
      (resolventTransform μ (η * Complex.I)).im η := by
  rw [im_resolventTransform]
  simp only [Complex.mul_I_im, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, sub_zero]
  have hη₀ := abs_pos.mpr hη
  have hlocal : {t : ℝ | |η| / 2 < |t|} ∈ 𝓝 η :=
    continuous_abs.continuousAt (Ioi_mem_nhds (half_lt_self hη₀))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x : ℝ ↦ Real.log (x ^ 2 + t ^ 2) / 2)
    (F' := fun t x : ℝ ↦ t / (x ^ 2 + t ^ 2)) (bound := fun _ ↦ (|η| / 2)⁻¹)
    hlocal (Eventually.of_forall (fun t ↦ (measurable_half_log_add_sq t).aestronglyMeasurable))
    (integrable_half_log_add_sq hlog hη)
    ((by fun_prop : Measurable (fun x : ℝ ↦ η / (x ^ 2 + η ^ 2))).aestronglyMeasurable)
    ?_ (integrable_const _) ?_).2
  · refine ae_of_all _ fun x t (ht : |η| / 2 < |t|) ↦ ?_
    have ht₀ : 0 < |t| := (half_pos hη₀).trans ht
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : 0 ≤ x ^ 2 + t ^ 2)]
    calc
      |t| / (x ^ 2 + t ^ 2) ≤ |t| / t ^ 2 :=
        by
          rw [← sq_abs t]
          exact div_le_div_of_nonneg_left ht₀.le (sq_pos_of_pos ht₀)
            (le_add_of_nonneg_left (sq_nonneg x))
      _ = |t|⁻¹ := by rw [← sq_abs]; field_simp
      _ ≤ (|η| / 2)⁻¹ := inv_anti₀ (half_pos hη₀) ht.le
  · exact ae_of_all _ fun x t ht ↦ hasDerivAt_half_log_add_sq x
      (abs_pos.mp ((half_pos hη₀).trans ht))

omit [IsFiniteMeasure μ] in
/-- At large heights, the regularized logarithmic integral of a probability measure is
asymptotic to the logarithm of the height with a difference tending to zero. -/
theorem tendsto_integral_half_log_add_sq_sub_log [IsProbabilityMeasure μ]
    (hlog : Integrable (fun x ↦ Real.log (x ^ 2 + 1)) μ) :
    Tendsto (fun η : ℝ ↦ (∫ x, Real.log (x ^ 2 + η ^ 2) / 2 ∂μ) - Real.log η)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun η : ℝ ↦ ∫ x, Real.log (x ^ 2 / η ^ 2 + 1) / 2 ∂μ)
      atTop (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ Real.log (x ^ 2 + 1))
      (Eventually.of_forall fun t ↦ (Measurable.div_const (Real.measurable_log.comp
        (by fun_prop : Measurable (fun x : ℝ ↦ x ^ 2 / t ^ 2 + 1))) 2).aestronglyMeasurable)
      ?_ hlog ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with η hη
      refine ae_of_all _ fun x ↦ ?_
      have hlo : 0 ≤ Real.log (x ^ 2 / η ^ 2 + 1) :=
        Real.log_nonneg (le_add_of_nonneg_left (by positivity))
      rw [Real.norm_of_nonneg (div_nonneg hlo (by norm_num))]
      have hsq : 1 ≤ η ^ 2 := by nlinarith
      have hx := Real.log_le_log (by positivity : 0 < x ^ 2 / η ^ 2 + 1)
        (add_le_add_left (div_le_self (sq_nonneg x) hsq) 1)
      linarith [Real.log_nonneg (show 1 ≤ x ^ 2 + 1 by nlinarith)]
    · refine ae_of_all _ fun x ↦ ?_
      have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
      have hh := ((hinv.pow 2).const_mul (x ^ 2)).add_const 1
      have hq : Tendsto (fun η : ℝ ↦ x ^ 2 / η ^ 2 + 1) atTop (𝓝 1) := by
        simpa [div_eq_mul_inv] using hh
      have hh' := ((Real.continuousAt_log one_ne_zero).tendsto.comp hq).div_const 2
      simpa using hh'
  rw [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with η hη
  have hconst : (∫ _ : ℝ, Real.log η ∂μ) = Real.log η := by simp
  rw [← hconst, ← integral_sub (integrable_half_log_add_sq hlog hη.ne') (integrable_const _)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have hquot : (x ^ 2 + η ^ 2) / η ^ 2 = x ^ 2 / η ^ 2 + 1 := by field_simp
  dsimp only
  rw [← hquot, Real.log_div (by positivity) (by positivity), Real.log_pow]
  ring

private theorem ae_ne_zero_of_im_resolventTransform_le {C : ℝ}
    (h : ∀ η ∈ Ioo (0 : ℝ) 1, (resolventTransform μ (η * Complex.I)).im ≤ C) :
    ∀ᵐ x ∂μ, x ≠ 0 := by
  have ht := tendsto_mul_im_resolventTransform (μ := μ) 0
  simp only [Complex.ofReal_zero, zero_add] at ht
  have hupper : ∀ᶠ η : ℝ in 𝓝[>] 0,
      η * (resolventTransform μ (η * Complex.I)).im ≤ η * C := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
    exact mul_le_mul_of_nonneg_left (h η hη) hη.1.le
  have hC : Tendsto (fun η : ℝ ↦ η * C) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).mul_const C
  have hzero : μ.real {0} = 0 := le_antisymm (le_of_tendsto_of_tendsto ht hC hupper)
    (by positivity)
  have hnull : μ {0} = 0 := (measureReal_eq_zero_iff (by finiteness)).mp hzero
  exact ae_iff.mpr (by simpa using hnull)

private theorem tendsto_half_log_add_sq_nhdsGT_zero {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun t : ℝ ↦ Real.log (x ^ 2 + t ^ 2) / 2) (𝓝[>] 0) (𝓝 (Real.log x)) := by
  have ht : ContinuousAt (fun t : ℝ ↦ Real.log (x ^ 2 + t ^ 2) / 2) 0 := by
    apply ContinuousAt.div_const
    exact (by fun_prop : ContinuousAt (fun t : ℝ ↦ x ^ 2 + t ^ 2) 0).log
      (by simpa using pow_ne_zero 2 hx)
  simpa [Real.log_pow] using ht.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)

private theorem abs_integral_half_log_add_sq_le
    (hlog : Integrable (fun x ↦ Real.log (x ^ 2 + 1)) μ) {C : ℝ}
    (h : ∀ η ∈ Ioo (0 : ℝ) 1, (resolventTransform μ (η * Complex.I)).im ≤ C)
    {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) :
    |(∫ x, Real.log (x ^ 2 + η ^ 2) / 2 ∂μ) -
      ∫ x, Real.log (x ^ 2 + (1 / 2 : ℝ) ^ 2) / 2 ∂μ| ≤ C * (1 / 2 - η) := by
  have hbound := (convex_Ioo (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (ht : t ∈ Ioo (0 : ℝ) 1) ↦
      (hasDerivAt_integral_half_log_add_sq hlog ht.1.ne').hasDerivWithinAt)
    (fun t ht ↦ by
      rw [Real.norm_of_nonneg]
      · exact h t ht
      · rw [im_resolventTransform]
        exact integral_nonneg fun x ↦ div_nonneg (by simpa using ht.1.le) (by positivity))
    (x := (1 / 2 : ℝ)) (y := η) (by norm_num) ⟨hη, hη'.trans (by norm_num)⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hη'), neg_sub] at hbound
  exact hbound

private theorem integral_norm_half_log_add_sq_le
    (hlog : Integrable (fun x ↦ Real.log (x ^ 2 + 1)) μ) {C : ℝ}
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, (resolventTransform μ (t * Complex.I)).im ≤ C)
    {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) :
    (∫ x, ‖Real.log (x ^ 2 + η ^ 2) / 2‖ ∂μ) ≤ (∫ x, Real.log (x ^ 2 + 1) ∂μ) -
      (∫ x, Real.log (x ^ 2 + (1 / 2 : ℝ) ^ 2) / 2 ∂μ) + C := by
  have hint := integrable_half_log_add_sq hlog hη.ne'
  have hC : 0 ≤ C := by
    refine le_trans ?_ (h (1 / 2) (by norm_num))
    rw [im_resolventTransform]
    exact integral_nonneg fun _ ↦ div_nonneg (by simp) (by positivity)
  have habs (x : ℝ) : ‖Real.log (x ^ 2 + η ^ 2) / 2‖ ≤
      Real.log (x ^ 2 + 1) - Real.log (x ^ 2 + η ^ 2) / 2 := by
    rw [Real.norm_eq_abs, abs_le]
    have h₁ := Real.log_nonneg (le_add_of_nonneg_left (sq_nonneg x))
    have h₂ := Real.log_le_log (by positivity : 0 < x ^ 2 + η ^ 2)
      (show x ^ 2 + η ^ 2 ≤ x ^ 2 + 1 by nlinarith)
    constructor <;> linarith
  calc
    ∫ x, ‖Real.log (x ^ 2 + η ^ 2) / 2‖ ∂μ ≤
        ∫ x, Real.log (x ^ 2 + 1) - Real.log (x ^ 2 + η ^ 2) / 2 ∂μ :=
      integral_mono hint.norm (hlog.sub hint) habs
    _ ≤ _ := by
      rw [integral_sub hlog hint]
      have hmul : C * (1 / 2 - η) ≤ C := by nlinarith [mul_nonneg hC hη.le]
      have hb := (abs_integral_half_log_add_sq_le hlog h hη hη').trans hmul
      linarith [neg_le_of_abs_le hb]

/-- A finite measure with a logarithmic moment at infinity and a bounded imaginary resolvent
near zero has an integrable logarithm. Its regularized logarithmic integrals converge to the
logarithmic integral as the height decreases to zero. -/
theorem integrable_log_and_tendsto_integral_half_log_add_sq
    (hlog : Integrable (fun x ↦ Real.log (x ^ 2 + 1)) μ) {C : ℝ}
    (h : ∀ η ∈ Ioo (0 : ℝ) 1, (resolventTransform μ (η * Complex.I)).im ≤ C) :
    Integrable Real.log μ ∧
      Tendsto (fun η : ℝ ↦ ∫ x, Real.log (x ^ 2 + η ^ 2) / 2 ∂μ) (𝓝[>] 0)
        (𝓝 (∫ x, Real.log x ∂μ)) := by
  let F (η x : ℝ) := Real.log (x ^ 2 + η ^ 2) / 2
  have hnonzero := ae_ne_zero_of_im_resolventTransform_le h
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun η ↦ F η x) (𝓝[>] 0) (𝓝 (Real.log x)) :=
    hnonzero.mono fun _ hx ↦
      tendsto_half_log_add_sq_nhdsGT_zero hx
  have hmeas (t : ℝ) : AEStronglyMeasurable (F t) μ :=
    (measurable_half_log_add_sq t).aestronglyMeasurable
  have hfi (t : ℝ) (ht : t ≠ 0) : Integrable (F t) μ := integrable_half_log_add_sq hlog ht
  have hlog' : Integrable Real.log μ := by
    let t (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
    have ht : Tendsto t atTop (𝓝[>] 0) := tendsto_inv_atTop_nhdsGT_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    refine integrable_of_tendsto (G := fun n ↦ F (t n)) (hpoint.mono fun x hx ↦ hx.comp ht)
      (fun n ↦ hmeas (t n)) ?_
    let M := (∫ x, Real.log (x ^ 2 + 1) ∂μ) - (∫ x, F (1 / 2) x ∂μ) + C
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := M))
      (liminf_le_of_frequently_le' ?_)
    apply Eventually.frequently
    filter_upwards [ht.eventually (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
    rw [← ofReal_integral_norm_eq_lintegral_eNorm (hfi (t n) hn.1.ne')]
    exact ENNReal.ofReal_le_ofReal (integral_norm_half_log_add_sq_le hlog h hn.1 hn.2)
  refine ⟨hlog', tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ |Real.log x| + Real.log (x ^ 2 + 1)) (.of_forall hmeas) ?_
    (hlog'.abs.add hlog) hpoint⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact hnonzero.mono fun x hx ↦ by
    have hlo := Real.log_le_log (sq_pos_of_ne_zero hx)
      (le_add_of_nonneg_right (sq_nonneg t) : x ^ 2 ≤ x ^ 2 + t ^ 2)
    have hhi := Real.log_le_log (by positivity : 0 < x ^ 2 + t ^ 2)
      (show x ^ 2 + t ^ 2 ≤ x ^ 2 + 1 by nlinarith [ht.1, ht.2])
    norm_num [Real.log_pow] at hlo
    rw [Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le (Real.log x), Real.log_nonneg (le_add_of_nonneg_left (sq_nonneg x))]
    · linarith [abs_nonneg (Real.log x), Real.log_nonneg (le_add_of_nonneg_left (sq_nonneg x))]

end MeasureTheory
