/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import TauCeti.Analysis.SpecialFunctions.Integrals.ExponentialSqrt
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.SummatoryTail
import TauCeti.NumberTheory.Chebyshev.DeLaValleePoussin

/-!
# The conductor-one Riesz remainder from the prime number theorem

The Riesz remainder of the trivial primitive Dirichlet character is `-y` times the integral
of `(ψ(t) - t) / t²` above `y`. Its constant term comes from the finite part of the logarithmic
zeta derivative at one. The classical de la Vallée Poussin bound on `ψ(t) - t` then gives
square-root logarithmic exponential decay of the normalized Riesz remainder, unconditionally.

The Riesz normalization is that of Levent Alpöge's `Formalism.Gz` in the formalization of the
Riemann hypothesis for Dirichlet L-functions (<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open ArithmeticFunction Complex Filter MeasureTheory Set
open scoped Chebyshev Topology

namespace Chebyshev

/-- Extend the de la Vallée Poussin bound to the entire integration range above one. -/
private theorem exists_abs_psi_sub_le_mul_exp_neg_mul_sqrt_log_one_le :
    ∃ c > 0, ∃ C > 0, ∀ t : ℝ, 1 ≤ t → |ψ t - t| ≤ C * t * Real.exp (-c * √(Real.log t)) := by
  obtain ⟨c, hc, C, hC⟩ := exists_abs_psi_sub_le_mul_exp_neg_mul_sqrt_log
  let D := (ψ 3 + 3) / Real.exp (-c * √(Real.log 3))
  have hD : 0 < D := div_pos (by linarith [psi_nonneg 3]) (Real.exp_pos _)
  refine ⟨c, hc, max C D, hD.trans_le (le_max_right ..), fun t ht ↦ ?_⟩
  rcases le_or_gt 3 t with ht₃ | ht₃
  · exact (hC t ht₃).trans (by gcongr; exact le_max_left ..)
  have hexp : Real.exp (-c * √(Real.log 3)) ≤ Real.exp (-c * √(Real.log t)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (Real.log_le_log (by linarith) ht₃.le))
      (neg_nonpos.mpr hc.le)
  calc
    |ψ t - t| ≤ ψ 3 + 3 := by
      rw [abs_le]
      constructor <;> linarith [psi_nonneg t, psi_nonneg 3, psi_mono ht₃.le]
    _ = D * Real.exp (-c * √(Real.log 3)) := by dsimp [D]; field_simp
    _ ≤ D * (t * Real.exp (-c * √(Real.log t))) :=
      mul_le_mul_of_nonneg_left (hexp.trans (le_mul_of_one_le_left (Real.exp_pos _).le ht)) hD.le
    _ ≤ _ := by rw [mul_assoc]; gcongr; exact le_max_right ..

/-- Integrability and decay of the tail of the weighted Chebyshev error above one. -/
private theorem exists_abs_integral_psi_sub_div_sq_le :
    ∃ c > 0, ∃ C > 0, IntegrableOn (fun t : ℝ ↦ (ψ t - t) / t ^ 2) (Ioi 1) ∧
      ∀ y : ℝ, 1 ≤ y → |∫ t in Ioi y, (ψ t - t) / t ^ 2| ≤ C * Real.exp (-c * √(Real.log y)) := by
  obtain ⟨c, hc, C, hC, hψ⟩ := exists_abs_psi_sub_le_mul_exp_neg_mul_sqrt_log_one_le
  have hg₀ : IntegrableOn (fun v : ℝ ↦ Real.exp (-c * √v)) (Ioi 0) := by
    simpa only [← Real.sqrt_eq_rpow, Real.rpow_zero, one_mul, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 / 2 : ℝ)) (s := 0) (by norm_num)
        (by norm_num) hc
  have hg : IntegrableOn (fun t : ℝ ↦ t⁻¹ * Real.exp (-c * √(Real.log t))) (Ioi 1) := by
    rw [← Real.log_one] at hg₀
    exact (integrableOn_comp_log_Ioi _ zero_lt_one).mpr hg₀
  have hpoint {t : ℝ} (ht : 1 ≤ t) : ‖(ψ t - t) / t ^ 2‖ ≤
      C * (t⁻¹ * Real.exp (-c * √(Real.log t))) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
    apply (div_le_iff₀ (sq_pos_of_pos (zero_lt_one.trans_le ht))).mpr
    convert hψ t ht using 1
    field_simp
  have hE : IntegrableOn (fun t : ℝ ↦ (ψ t - t) / t ^ 2) (Ioi 1) := by
    have hm := (psi_mono.measurable.sub measurable_id).div (measurable_id.pow_const 2)
    exact (hg.const_mul C).mono' hm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht ↦ hpoint ht.le)
  refine ⟨c / 2, by positivity, C * (4 / c ^ 2), by positivity, hE, fun y hy ↦ ?_⟩
  rw [← Real.norm_eq_abs]
  have hgy := (hg.mono_set (Ioi_subset_Ioi hy)).const_mul C
  calc
    _ ≤ ∫ t in Ioi y, C * (t⁻¹ * Real.exp (-c * √(Real.log t))) :=
      norm_integral_le_of_norm_le hgy (ae_restrict_of_forall_mem measurableSet_Ioi
        fun _ ht ↦ hpoint (hy.trans ht.le))
    _ = C * ∫ v in Ioi (Real.log y), Real.exp (-c * √v) := by
      rw [integral_const_mul]
      congr 1
      exact integral_comp_log_Ioi (fun v ↦ Real.exp (-c * √v)) (zero_lt_one.trans_le hy)
    _ ≤ _ := by
      rw [TauCeti.integral_Ioi_exp_neg_mul_sqrt hc (Real.log_nonneg hy)]
      let u := c / 2 * √(Real.log y)
      have hu : c * √(Real.log y) = 2 * u := by dsimp [u]; ring
      simp only [neg_mul, hu]
      calc
        _ ≤ C * (2 / c ^ 2 * (2 * Real.exp u) * Real.exp (-(2 * u))) := by
          gcongr
          linarith [Real.add_one_le_exp u]
        _ = _ := by
          have he : u + -(2 * u) = -u := by ring
          rw [← mul_assoc (2 / c ^ 2) 2, mul_assoc (2 / c ^ 2 * 2), ← Real.exp_add, he]
          simp only [u, ← neg_mul]
          ring

/-- The weighted Chebyshev error is absolutely integrable above every positive cutoff. -/
theorem integrableOn_psi_sub_div_sq {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t : ℝ ↦ (ψ t - t) / t ^ 2) (Ioi y) := by
  obtain ⟨_, _, _, _, hE, _⟩ := exists_abs_integral_psi_sub_div_sq_le
  rcases le_or_gt 1 y with h | h
  · exact hE.mono_set (Ioi_subset_Ioi h)
  have hsmall : IntegrableOn (fun t : ℝ ↦ (ψ t - t) / t ^ 2) (Ioc y 1) := by
    have hc : ContinuousOn (fun t : ℝ ↦ -t⁻¹) (Icc y 1) :=
      (continuousOn_id.inv₀ fun _ (ht : _ ∈ Icc y 1) ↦ (hy.trans_le ht.1).ne').neg
    refine (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun ?_ measurableSet_Ioc
    intro t ht
    simp only [psi_eq_zero_of_le_one ht.2, zero_sub]
    field_simp [(hy.trans ht.1).ne']
  rw [← Ioc_union_Ioi_eq_Ioi h.le]
  exact hsmall.union hE

/-- The Dirichlet series of `Λ`, after removing the compensating linear main term, tends to
`-1 - γ` as the real argument approaches one from above. -/
private theorem tendsto_vonMangoldt_sub_linear_pole :
    Tendsto (fun σ : ℝ ↦ LSeries (fun n ↦ (Λ n : ℂ)) (σ : ℂ) - (σ : ℂ) / ((σ : ℂ) - 1))
      (𝓝[>] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - 1)) := by
  have hlim : Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simpa using (mem_Ioi.mp hσ).ne'
  have hzero := log_deriv_riemannZeta_add_inv_sub_sub_isLittleO.tendsto_zero_of_tendsto
    (tendsto_const_nhds (x := (1 : ℂ)))
  have hreg : Tendsto (fun s : ℂ ↦ logDeriv riemannZeta s + (s - 1)⁻¹) (𝓝[≠] 1)
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    simpa only [← logDeriv_apply, sub_add_cancel, zero_add] using
      hzero.add_const (Real.eulerMascheroniConstant : ℂ)
  refine ((hreg.comp hlim).neg.sub_const 1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hs : 1 < (σ : ℂ).re := by simpa using (mem_Ioi.mp hσ)
  have hne : (σ : ℂ) - 1 ≠ 0 := Complex.ne_zero_of_re_pos (by simpa using sub_pos.mpr hs)
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div, ← logDeriv_apply]
  simp only [Function.comp_apply]
  field_simp
  ring

/-- The weighted summatory error of the von Mangoldt Dirichlet series in real coordinates. -/
private theorem sum_vonMangoldt_sub_div_sq (t : ℝ) :
    ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (Λ n : ℂ)) - (t : ℂ)) / (t : ℂ) ^ 2 =
      (((ψ t - t) / t ^ 2 : ℝ) : ℂ) := by
  simp [psi, ← Finset.Icc_add_one_left_eq_Ioc]

/-- The integral of the Chebyshev error against `dt/t²` from one to infinity is `-1 - γ`. -/
theorem integral_psi_sub_div_sq :
    (∫ t in Ioi (1 : ℝ), (ψ t - t) / t ^ 2) = -Real.eulerMascheroniConstant - 1 := by
  have hsum : ∀ᶠ σ : ℝ in 𝓝[>] 1, LSeriesSummable (fun n ↦ (Λ n : ℂ)) (σ : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact LSeriesSummable_vonMangoldt (by simpa using (mem_Ioi.mp hσ))
  have hE : IntegrableOn (fun t : ℝ ↦ (((ψ t - t) / t ^ 2 : ℝ) : ℂ)) (Ioi 1) :=
    (integrableOn_psi_sub_div_sq one_pos).ofReal
  have h := TauCeti.LSeries.tendsto_sub_linear_pole_of_integrable_summatory_error 1 hsum
    (by simpa only [one_mul, sum_vonMangoldt_sub_div_sq] using hE)
  simp only [one_mul, sum_vonMangoldt_sub_div_sq, integral_complex_ofReal] at h
  have heq := tendsto_nhds_unique h tendsto_vonMangoldt_sub_linear_pole
  simpa only [← ofReal_one,
    ← ofReal_neg, ← ofReal_sub, ofReal_inj] using heq

end Chebyshev

namespace TauCeti.PrimitiveDirichletCharacter

/-- The conductor-one Riesz remainder is `-y` times the weighted tail of the Chebyshev error.
The tail is integrable for `y > 0`; at `y = 0` both sides vanish. -/
theorem rieszRemainder_one_eq_neg_mul_integral_psi_sub_div_sq {y : ℝ} (hy : 0 ≤ y) :
    (1 : PrimitiveDirichletCharacter).rieszRemainder y =
      ((-y * ∫ t in Ioi y, (ψ t - t) / t ^ 2 : ℝ) : ℂ) := by
  rw [rieszRemainder_one]
  rcases hy.eq_or_lt with rfl | hy
  · simp
  rcases le_or_gt 1 y with hy₁ | hy₁
  · have h := rieszSum_div_sub_log_eq_integral (fun n ↦ (Λ n : ℂ)) 1 hy₁
    simp only [one_mul, Chebyshev.sum_vonMangoldt_sub_div_sq, integral_complex_ofReal] at h
    rw [← intervalIntegral.integral_of_le hy₁,
      ← intervalIntegral.integral_Ioi_sub_Ioi (Chebyshev.integrableOn_psi_sub_div_sq one_pos) hy₁,
      Chebyshev.integral_psi_sub_div_sq] at h
    push_cast at h ⊢
    linear_combination (norm := (field_simp [hy.ne']; ring)) (y : ℂ) * h
  · have hsmall : (∫ t in y..1, (ψ t - t) / t ^ 2) = Real.log y := by
      rw [intervalIntegral.integral_congr (g := fun t : ℝ ↦ -(t⁻¹)) (fun t ht ↦ ?_),
        intervalIntegral.integral_neg, integral_inv_of_pos hy zero_lt_one, one_div, Real.log_inv,
        neg_neg]
      rw [uIcc_of_le hy₁.le] at ht
      simp only [Chebyshev.psi_eq_zero_of_le_one ht.2, zero_sub]
      field_simp [(hy.trans_le ht.1).ne']
    rw [← intervalIntegral.integral_Ioi_sub_Ioi (Chebyshev.integrableOn_psi_sub_div_sq hy) hy₁.le,
      Chebyshev.integral_psi_sub_div_sq] at hsmall
    rw [rieszSum_eq_zero_of_le_one _ hy₁.le]
    have hsmall' := congrArg Complex.ofReal hsmall
    push_cast at hsmall' ⊢
    linear_combination (y : ℂ) * hsmall'

/-- The principal Riesz remainder satisfies the de la Vallée Poussin type bound
`C * y * exp (-c * √(log y))`, uniformly for `y ≥ 1`. -/
theorem exists_norm_rieszRemainder_one_le_mul_exp_neg_mul_sqrt_log :
    ∃ c > 0, ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      ‖(1 : PrimitiveDirichletCharacter).rieszRemainder y‖ ≤
        C * y * Real.exp (-c * √(Real.log y)) := by
  obtain ⟨c, hc, C, hC, _, htail⟩ := Chebyshev.exists_abs_integral_psi_sub_div_sq_le
  refine ⟨c, hc, C, hC, fun y hy ↦ ?_⟩
  have hy₀ := zero_lt_one.trans_le hy
  rw [rieszRemainder_one_eq_neg_mul_integral_psi_sub_div_sq hy₀.le,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hy₀.le]
  calc
    _ ≤ y * (C * Real.exp (-c * √(Real.log y))) := mul_le_mul_of_nonneg_left (htail y hy) hy₀.le
    _ = _ := by ring

end TauCeti.PrimitiveDirichletCharacter
