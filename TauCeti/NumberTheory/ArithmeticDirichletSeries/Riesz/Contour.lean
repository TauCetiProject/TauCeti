/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Inversion
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Coordinates
import TauCeti.Analysis.Contour.Residue.Rectangle
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Finite-height contour shift for first Riesz sums

The Perron–Riesz kernel has a simple pole at one. Moving the finite part of the line of
integration to the left of one yields the main term and three integrals, without imposing
any growth condition outside the rectangle on the continued Dirichlet series.

See Montgomery and Vaughan, *Multiplicative Number Theory I*, Chapter 5, for the use of
Perron inversion and contour shifts.
-/

public section

open Complex MeasureTheory Set
open scoped Real Interval

namespace TauCeti

private lemma perronRiesz_integrand_residue {F : ℂ → ℂ} {y : ℝ} (hy : 0 < y)
    (hF : AnalyticAt ℂ F 1) :
    let f := fun s : ℂ ↦ F s * ((y : ℂ) ^ s / (s * (s - 1)))
    MeromorphicAt f 1 ∧ Contour.residue f 1 = F 1 * y := by
  let g := fun s : ℂ ↦ F s * ((y : ℂ) ^ s / s)
  have hp : AnalyticAt ℂ (fun s : ℂ ↦ (y : ℂ) ^ s) 1 :=
    Differentiable.analyticAt (fun _ ↦ differentiableAt_id.const_cpow
      (.inl (ofReal_ne_zero.mpr hy.ne'))) _
  have hg : AnalyticAt ℂ g 1 := hF.mul (hp.div analyticAt_id one_ne_zero)
  have heq (s : ℂ) : F s * ((y : ℂ) ^ s / (s * (s - 1))) = g s / (s - 1) := by
    simp [g, div_mul_eq_div_div, mul_div_assoc]
  refine ⟨?_, ?_⟩
  · simp_rw [heq]
    exact hg.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt
  · simpa [g, cpow_one] using
      Contour.residue_eq_of_eventuallyEq_div_sub hg (Filter.Eventually.of_forall heq)

/-- **Finite-height Perron–Riesz shift.** If a Dirichlet series on `Re s = c` has a holomorphic
continuation `F` to the rectangle down to `Re s = σ`, with `0 < σ < 1 < c`, its first Riesz sum
is `y F(1)` plus the integral on the shifted edge, the two horizontal edges and the tails. -/
theorem rieszSum_eq_residue_add_contour {a : ℕ → ℂ} {F : ℂ → ℂ} {y σ c T : ℝ}
    (hy : 0 ≤ y) (hσ : 0 < σ) (hσ₁ : σ < 1) (hc : 1 < c) (hT : 0 < T)
    (ha : LSeriesSummable a c) (hFc : ContinuousOn F (Icc σ c ×ℂ Icc (-T) T))
    (hFd : DifferentiableOn ℂ F (Ioo σ c ×ℂ Ioo (-T) T))
    (hline : ∀ t : ℝ, LSeries a (c + t * I) = F (c + t * I)) :
    let v := fun x t : ℝ ↦ F (x + t * I) * perronRieszKernel y x t
    rieszSum a y = F 1 * y + ((2 * π : ℝ) : ℂ)⁻¹ *
      ((∫ t in {t : ℝ | T < |t|}, v c t) + (∫ t in (-T)..T, v σ t) +
        ((∫ x in σ..c, v x T) - (∫ x in σ..c, v x (-T))) / I) := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [rieszSum_eq_zero_of_le_one]
  let f := fun s : ℂ ↦ F s * ((y : ℂ) ^ s / (s * (s - 1)))
  have h1 : (1 : ℂ) ∈ Ioo σ c ×ℂ Ioo (-T) T := by
    simp [mem_reProdIm, hσ₁, hc, hT]
  have hkernel (s : ℂ) (hs : σ ≤ s.re) (hs₁ : s ≠ 1) :
      AnalyticAt ℂ (fun w : ℂ ↦ (y : ℂ) ^ w / (w * (w - 1))) s := by
    have hs₀ : s ≠ 0 := fun h ↦ by simp [h, hσ.not_ge] at hs
    have hp : AnalyticAt ℂ (fun w : ℂ ↦ (y : ℂ) ^ w) s :=
      Differentiable.analyticAt (fun _ ↦ differentiableAt_id.const_cpow
        (.inl (ofReal_ne_zero.mpr hy.ne'))) _
    exact hp.div (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
      (mul_ne_zero hs₀ (sub_ne_zero.mpr hs₁))
  have hfc : ContinuousOn f (Icc σ c ×ℂ Icc (-T) T \ {1}) := fun s hs ↦
    ((hFc s hs.1).mono sdiff_subset).mul
      (hkernel s hs.1.1.1 hs.2).continuousAt.continuousWithinAt
  have hfd : DifferentiableOn ℂ f (Ioo σ c ×ℂ Ioo (-T) T \ {1}) := fun s hs ↦
    ((hFd s hs.1).mono sdiff_subset).mul
      (hkernel s hs.1.1.1.le hs.2).differentiableAt.differentiableWithinAt
  have heq (t : ℝ) : LSeries a (c + t * I) * perronRieszKernel y c t = f (c + t * I) := by
    rw [hline, perronRieszKernel_def]
  have hint := (integrable_LSeries_mul_perronRieszKernel a hy.le
    (zero_lt_one.trans hc).ne' (ne_of_gt hc)).congr (Filter.Eventually.of_forall heq)
  obtain ⟨hmer, hres⟩ := perronRiesz_integrand_residue hy
    (hFd.analyticAt ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds h1))
  have hshift := Contour.integral_vertical_eq_uShaped_symm_add_two_pi_mul_sum_residue
    (P := {1}) (hσ₁.trans hc).le hT.le (by simpa using h1)
    (by simpa only [Finset.coe_singleton] using hfc)
    (by simpa only [Finset.coe_singleton] using hfd) (by simpa using hmer) hint
  rw [Finset.sum_singleton, hres] at hshift
  have hsum := inv_mul_integral_LSeries_mul_perronRieszKernel_eq_rieszSum hy.le hc ha
  simp_rw [heq] at hsum
  have hπ : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hmain (E : ℂ) : ((2 * π : ℝ) : ℂ)⁻¹ * (E + 2 * π * (F 1 * y)) =
      F 1 * y + ((2 * π : ℝ) : ℂ)⁻¹ * E := by
    push_cast
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul, add_comm]
  rw [← hsum, hshift, hmain]
  simp only [f, perronRieszKernel_def, ofReal_neg, neg_mul, ← sub_eq_add_neg]

private lemma norm_perronRieszKernel_sub_le_slope {z η σ : ℝ} (hz : 0 < z) (hη : 0 ≤ η)
    (hσ : 0 < σ) (hσ₁ : σ < 1) (t : ℝ) :
    ‖perronRieszKernel (z * (1 + η)) σ t - perronRieszKernel z σ t‖ ≤
      η * z ^ σ / ‖(σ : ℂ) + t * I - 1‖ := by
  rcases hη.eq_or_lt with rfl | hη
  · simp
  let s : ℂ := σ + t * I
  have hs : s.re = σ := by simp [s]
  have hs₀ : s ≠ 0 := Complex.ofReal_add_mul_I_ne_zero hσ.ne' t
  have hbase : 0 < z * η := mul_pos hz hη
  have hM := norm_ofReal_add_one_cpow_neg_sub_le (w := -s)
    (y := η⁻¹) (by simp [hs]; linarith) (inv_pos.mpr hη)
  have hscale : ((z * (1 + η) : ℝ) : ℂ) ^ s - (z : ℂ) ^ s =
      ((z * η : ℝ) : ℂ) ^ s * (((η⁻¹ : ℝ) : ℂ) + 1) ^ s -
        ((z * η : ℝ) : ℂ) ^ s * ((η⁻¹ : ℝ) : ℂ) ^ s := by
    have h₁ : z * η * (η⁻¹ + 1) = z * (1 + η) := by field_simp
    have h₂ : z * η * η⁻¹ = z := by simp [hη.ne']
    congr 1
    · rw [← h₁, ofReal_mul, ofReal_mul_cpow hbase.le, ofReal_add, ofReal_one]
    · conv_lhs => rw [← h₂, ofReal_mul, ofReal_mul_cpow hbase.le]
  rw [perronRieszKernel_def, perronRieszKernel_def, ← sub_div, hscale, ← mul_sub,
    norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hbase, hs]
  have hM' : ‖(((η⁻¹ : ℝ) : ℂ) + 1) ^ s - ((η⁻¹ : ℝ) : ℂ) ^ s‖ ≤
      ‖s‖ * (η⁻¹) ^ (σ - 1) := by simpa only [neg_neg, norm_neg, neg_re, hs] using hM
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM' (by positivity))
    (by positivity)).trans_eq ?_
  rw [Real.mul_rpow hz.le hη.le, Real.inv_rpow hη.le, mul_comm ‖s‖, ← mul_assoc,
    mul_assoc (z ^ σ) (η ^ σ), ← div_eq_mul_inv, ← Real.rpow_sub hη,
    sub_sub_cancel, Real.rpow_one, mul_comm (z ^ σ), mul_comm ‖(σ : ℂ) + t * I‖]
  exact mul_div_mul_right _ _ (norm_ne_zero_iff.mpr hs₀)

private lemma norm_perronRieszKernel_sub_le_sq {z η c t : ℝ} (hz : 1 ≤ z)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hc : c ≤ 2) (ht : t ≠ 0) :
    ‖perronRieszKernel (z * (1 + η)) c t - perronRieszKernel z c t‖ ≤ 5 * z ^ 2 / t ^ 2 := by
  have hz₀ : 0 ≤ z := by linarith
  have hw : 1 ≤ z * (1 + η) := le_trans hz (le_mul_of_one_le_right hz₀ (by linarith))
  have hker (x : ℝ) (hx : 1 ≤ x) : ‖perronRieszKernel x c t‖ ≤ x ^ 2 / t ^ 2 := by
    refine (norm_perronRieszKernel_le (by linarith) c t).trans ?_
    have hpow : x ^ c ≤ x ^ (2 : ℕ) := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hx hc
    exact div_le_div₀ (by positivity) hpow (sq_pos_of_ne_zero ht)
      (le_add_of_nonneg_left (sq_nonneg _))
  calc
    _ ≤ ‖perronRieszKernel (z * (1 + η)) c t‖ + ‖perronRieszKernel z c t‖ := norm_sub_le _ _
    _ ≤ (z * (1 + η)) ^ 2 / t ^ 2 + z ^ 2 / t ^ 2 := add_le_add (hker _ hw) (hker _ hz)
    _ ≤ _ := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + η) (by linarith : 1 + η ≤ 2) 2) (sq_nonneg z)]

private lemma norm_integral_perronRiesz_sub_tail_le {F : ℂ → ℂ} {z η T B : ℝ} (hz : 1 ≤ z)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hT : 0 < T)
    (hF : ∀ t : ℝ, T < |t| → ‖F (2 + t * I)‖ ≤ B) :
    ‖∫ t in {t : ℝ | T < |t|}, F (2 + t * I) *
      (perronRieszKernel (z * (1 + η)) 2 t - perronRieszKernel z 2 t)‖ ≤ 10 * B * z ^ 2 / T := by
  let S := (Metric.closedBall (0 : ℝ) T)ᶜ
  have hS : {t : ℝ | T < |t|} = S := by ext t; simp [S]
  have hInt : IntegrableOn (fun t : ℝ ↦ ‖t‖ ^ (-2 : ℝ)) S :=
    (integrableOn_norm_rpow_compl_closedBall_iff (mu := volume) (E := ℝ) hT).2 (by simp)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF (T + 1) (by rw [abs_of_pos (by linarith)]; linarith))
  rw [hS]
  refine (norm_integral_le_of_norm_le (hInt.const_mul (5 * B * z ^ 2)) ?_).trans_eq ?_
  · have hmeas : MeasurableSet S := Metric.isClosed_closedBall.measurableSet.compl
    filter_upwards [ae_restrict_mem hmeas] with t ht
    have ht' : T < |t| := by simpa [← hS] using ht
    have ht₀ : t ≠ 0 := fun h ↦ by simp [h, hT.not_gt] at ht'
    rw [norm_mul]
    calc
      _ ≤ B * (5 * z ^ 2 / t ^ 2) := mul_le_mul (hF t ht')
        (norm_perronRieszKernel_sub_le_sq hz hη hη₁ le_rfl ht₀) (norm_nonneg _) hB
      _ = _ := by rw [Real.norm_eq_abs, Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs]; ring
  · rw [integral_const_mul, integral_norm_rpow_compl_closedBall
      (E := ℝ) (mu := volume) (s := -2) (by simp) hT]
    norm_num [Real.ball_eq_Ioo, measureReal_def, Real.volume_Ioo, Real.rpow_neg_one]
    ring

private lemma norm_intervalIntegral_perronRiesz_sub_vertical_le {F : ℂ → ℂ}
    {z η σ T A : ℝ} (hz : 0 < z) (hη : 0 ≤ η) (hσ : 0 < σ) (hσ₁ : σ < 1)
    (hT : 0 ≤ T) (hA : ∀ t ∈ Icc (-T) T, ‖F (σ + t * I)‖ ≤ A) :
    ‖∫ t in (-T)..T, F (σ + t * I) *
        (perronRieszKernel (z * (1 + η)) σ t - perronRieszKernel z σ t)‖ ≤
      4 * A * η * z ^ σ * Real.log (1 + T / (1 - σ)) := by
  let d := 1 - σ
  have hd : 0 < d := sub_pos.mpr hσ₁
  have hA₀ := (norm_nonneg _).trans (hA 0 ⟨by linarith, hT⟩)
  have hC : Continuous (fun t : ℝ ↦ (d + |t|)⁻¹) := by
    apply (continuous_const.add continuous_abs).inv₀
    exact fun t ↦ (add_pos_of_pos_of_nonneg hd (abs_nonneg t)).ne'
  have hwt : (∫ t in (-T)..T, (d + |t|)⁻¹) = 2 * Real.log (1 + T / d) := by
    have hreflect : (∫ t in (-T)..0, (d + |t|)⁻¹) = ∫ t in 0..T, (d + |t|)⁻¹ := by
      simpa only [neg_zero, abs_neg] using
        (intervalIntegral.integral_comp_neg (a := 0) (b := T) (fun t : ℝ ↦ (d + |t|)⁻¹)).symm
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hC.intervalIntegrable (-T) 0) (hC.intervalIntegrable 0 T), hreflect]
    have heq : (∫ t in 0..T, (d + |t|)⁻¹) = Real.log (1 + T / d) := by
      calc
        _ = ∫ t in 0..T, (t + d)⁻¹ :=
          intervalIntegral.integral_congr fun t ht ↦ by
            rw [uIcc_of_le hT] at ht
            rw [abs_of_nonneg ht.1, add_comm]
        _ = _ := by
          rw [intervalIntegral.integral_comp_add_right (fun x : ℝ ↦ x⁻¹), zero_add,
            integral_inv_of_pos hd (by linarith)]
          congr 1
          field_simp
          ring
    rw [heq]
    ring
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hInt := (hC.const_mul (2 * A * η * z ^ σ)).intervalIntegrable (μ := volume) (-T) T
  refine (norm_integral_le_of_norm_le hInt.1 ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hden : (d + |t|) / 2 ≤ ‖(σ : ℂ) + t * I - 1‖ := by
      have hr := Complex.abs_re_le_norm ((σ : ℂ) + t * I - 1)
      have hi := Complex.abs_im_le_norm ((σ : ℂ) + t * I - 1)
      simp [abs_of_neg (sub_neg.mpr hσ₁)] at hr
      simp at hi
      dsimp [d]
      linarith
    rw [norm_mul]
    calc
      _ ≤ A * (η * z ^ σ / ‖(σ : ℂ) + t * I - 1‖) := mul_le_mul
        (hA t (Ioc_subset_Icc_self ht)) (norm_perronRieszKernel_sub_le_slope hz hη hσ hσ₁ t)
        (norm_nonneg _) hA₀
      _ ≤ A * (η * z ^ σ / ((d + |t|) / 2)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
          (half_pos (add_pos_of_pos_of_nonneg hd (abs_nonneg t))) hden) hA₀
      _ = (2 * A * η * z ^ σ) * (d + |t|)⁻¹ := by rw [div_div_eq_mul_div]; ring
  · rw [integral_const_mul, ← intervalIntegral.integral_of_le (by linarith : -T ≤ T), hwt]
    ring

private lemma norm_intervalIntegral_perronRiesz_sub_horizontal_le {F : ℂ → ℂ} {z η σ t A : ℝ}
    (hz : 1 ≤ z) (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hσ : σ ≤ 2) (ht : t ≠ 0)
    (hF : ∀ x ∈ Icc σ 2, ‖F (x + t * I)‖ ≤ A) :
    ‖∫ x in σ..2, F (x + t * I) *
        (perronRieszKernel (z * (1 + η)) x t - perronRieszKernel z x t)‖ ≤
      5 * A * z ^ 2 / t ^ 2 * (2 - σ) := by
  have hA := (norm_nonneg _).trans (hF 2 ⟨hσ, le_rfl⟩)
  rw [← abs_of_nonneg (sub_nonneg.mpr hσ)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [uIoc_of_le hσ] at hx
  rw [norm_mul]
  calc
    _ ≤ A * (5 * z ^ 2 / t ^ 2) := mul_le_mul (hF x (Ioc_subset_Icc_self hx))
      (norm_perronRieszKernel_sub_le_sq hz hη hη₁ hx.2 ht) (norm_nonneg _) hA
    _ = _ := by ring

private lemma rieszSum_sub_sub_mul_eq_contour {a : ℕ → ℂ} {F : ℂ → ℂ} {w z σ T : ℝ}
    (hw : 0 < w) (hz : 0 < z) (hσ : 0 < σ) (hσ₁ : σ < 1) (hT : 0 < T)
    (ha : LSeriesSummable a 2) (hFc : ContinuousOn F (Icc σ 2 ×ℂ Icc (-T) T))
    (hFd : DifferentiableOn ℂ F (Ioo σ 2 ×ℂ Ioo (-T) T))
    (hline : ∀ t : ℝ, LSeries a (2 + t * I) = F (2 + t * I)) :
    let v := fun c t : ℝ ↦ F (c + t * I) * (perronRieszKernel w c t - perronRieszKernel z c t)
    rieszSum a w - rieszSum a z - F 1 * ((w : ℂ) - z) = ((2 * π : ℝ) : ℂ)⁻¹ *
      ((∫ t in {t : ℝ | T < |t|}, v 2 t) + (∫ t in (-T)..T, v σ t) +
        ((∫ x in σ..2, v x T) - (∫ x in σ..2, v x (-T))) / I) := by
  dsimp only
  have hσ₂ : σ ≤ 2 := by linarith
  have hR (y : ℝ) (hy : 0 < y) : Integrable
      (fun t : ℝ ↦ F (((2 : ℝ) : ℂ) + t * I) * perronRieszKernel y 2 t) := by
    simp_rw [ofReal_ofNat, ← hline]
    exact integrable_LSeries_mul_perronRieszKernel a hy.le (by norm_num) (by norm_num)
  have hV (y : ℝ) : IntervalIntegrable
      (fun t : ℝ ↦ F (σ + t * I) * perronRieszKernel y σ t) volume (-T) T := by
    refine ((hFc.comp (by fun_prop) ?_).mul
      (continuous_perronRieszKernel y hσ.ne' hσ₁.ne).continuousOn).intervalIntegrable_of_Icc
        (by linarith)
    intro t ht
    simpa [mem_reProdIm, hσ₂] using ht
  have hH (y : ℝ) (hy : 0 < y) (t : ℝ) (ht : t ∈ Icc (-T) T) (ht₀ : t ≠ 0) :
      IntervalIntegrable (fun x : ℝ ↦ F (x + t * I) * perronRieszKernel y x t) volume σ 2 := by
    have hne (x : ℝ) (b : ℝ) : (x : ℂ) + t * I ≠ b := fun h ↦
      ht₀ (by simpa using congrArg Complex.im h)
    refine ((hFc.comp (by fun_prop) (fun x hx ↦ by simpa [mem_reProdIm, ht] using hx)).mul
      ?_).intervalIntegrable_of_Icc hσ₂
    simp only [perronRieszKernel_def]
    have hy₀ := ofReal_ne_zero.mpr hy.ne'
    have hp : Continuous fun x : ℝ ↦ (y : ℂ) ^ ((x : ℂ) + t * I) := by fun_prop
    exact hp.continuousOn.div (by fun_prop) (fun x _ ↦ mul_ne_zero (by simpa using hne x 0)
        (sub_ne_zero.mpr (by simpa using hne x 1)))
  have hpos : T ∈ Icc (-T) T := ⟨by linarith, le_rfl⟩
  have hneg : -T ∈ Icc (-T) T := ⟨le_rfl, by linarith⟩
  have hc : 1 < (2 : ℝ) := by norm_num
  rw [rieszSum_eq_residue_add_contour hw.le hσ hσ₁ hc hT ha hFc hFd hline,
    rieszSum_eq_residue_add_contour hz.le hσ hσ₁ hc hT ha hFc hFd hline]
  dsimp only
  simp only [mul_sub, intervalIntegral.integral_sub (hV w) (hV z),
    intervalIntegral.integral_sub (hH w hw T hpos hT.ne') (hH z hz T hpos hT.ne'),
    intervalIntegral.integral_sub (hH w hw (-T) hneg (neg_ne_zero.mpr hT.ne'))
      (hH z hz (-T) hneg (neg_ne_zero.mpr hT.ne'))]
  rw [integral_sub ((hR w hw).integrableOn (s := {t | T < |t|})) (hR z hz).integrableOn]
  ring

/-- **First Riesz increments with a finite-height bound.** A Dirichlet series on `Re s = 2`
continued to `[σ,2] × [-T,T]` has a Riesz increment from `z` to `z(1+η)` with main term
`zη F(1)`. If `A` bounds the continuation on the rectangle and `B` on the two tails, the
shifted edge costs `O(A η z^σ log(1 + T/(1-σ)))` and the other edges and tails cost
`O((A+B) z²/T)` for `T ≥ 1`. -/
theorem norm_rieszSum_sub_sub_mul_le_of_box_bound {a : ℕ → ℂ} {F : ℂ → ℂ} {z η σ T A B : ℝ}
    (hz : 1 ≤ z) (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hσ : 0 < σ) (hσ₁ : σ < 1) (hT : 1 ≤ T)
    (ha : LSeriesSummable a 2) (hFc : ContinuousOn F (Icc σ 2 ×ℂ Icc (-T) T))
    (hFd : DifferentiableOn ℂ F (Ioo σ 2 ×ℂ Ioo (-T) T))
    (hline : ∀ t : ℝ, LSeries a (2 + t * I) = F (2 + t * I))
    (hA : ∀ s ∈ Icc σ 2 ×ℂ Icc (-T) T, ‖F s‖ ≤ A)
    (hB : ∀ t : ℝ, T < |t| → ‖F (2 + t * I)‖ ≤ B) :
    ‖rieszSum a (z * (1 + η)) - rieszSum a z - F 1 * (z * η : ℝ)‖ ≤
      (4 * A * η * z ^ σ * Real.log (1 + T / (1 - σ)) + (20 * A + 10 * B) * z ^ 2 / T) /
        (2 * π) := by
  have hz₀ : 0 < z := by linarith
  have hT₀ : 0 < T := by linarith
  have hσ₂ : σ ≤ 2 := by linarith
  have hinc : ((z * (1 + η) : ℝ) : ℂ) - z = (z * η : ℝ) := by push_cast; ring
  rw [← hinc, rieszSum_sub_sub_mul_eq_contour (mul_pos hz₀ (by linarith)) hz₀ hσ hσ₁ hT₀
    ha hFc hFd hline]
  dsimp only
  rw [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hv := norm_intervalIntegral_perronRiesz_sub_vertical_le hz₀ hη hσ hσ₁ hT₀.le
    (fun t ht ↦ hA (σ + t * I) (by simpa [mem_reProdIm, hσ₂] using ht))
  have hh (t : ℝ) (ht : |t| = T) (ht₀ : t ≠ 0) :=
    norm_intervalIntegral_perronRiesz_sub_horizontal_le hz hη hη₁ hσ₂ ht₀
      (fun x hx ↦ hA (x + t * I) (by simpa [mem_reProdIm, ← abs_le, ht] using hx))
  have hp := hh T (abs_of_pos hT₀) hT₀.ne'
  have hm := hh (-T) (by simp [abs_of_pos hT₀]) (neg_ne_zero.mpr hT₀.ne')
  have htail := norm_integral_perronRiesz_sub_tail_le hz hη hη₁ hT₀ hB
  have hA₀ := (norm_nonneg _).trans (hA (σ : ℂ) (by simp [mem_reProdIm, hσ₂, hT₀.le]))
  have herr : 5 * A * z ^ 2 / T ^ 2 * (2 - σ) ≤ 10 * A * z ^ 2 / T := by
    calc
      _ ≤ 5 * A * z ^ 2 / T ^ 2 * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 10 * A * z ^ 2 / T ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hT₀ (by nlinarith)
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ (10 * B * z ^ 2 / T + 4 * A * η * z ^ σ * Real.log (1 + T / (1 - σ))) +
        (10 * A * z ^ 2 / T + 10 * A * z ^ 2 / T) := by
      refine add_le_add ((norm_add_le _ _).trans (add_le_add htail hv)) ?_
      rw [norm_div, norm_I, div_one]
      exact (norm_sub_le _ _).trans (add_le_add (hp.trans herr) (hm.trans (by simpa using herr)))
    _ = _ := by ring

end TauCeti
