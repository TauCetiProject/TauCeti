/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.SpecialFunctions.Integrals.ExponentialSqrt
import TauCeti.NumberTheory.LSeries.CompensatedSummatoryMellin
import TauCeti.NumberTheory.Chebyshev.DeLaValleePoussin
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.VonMangoldt

/-!
# The Chebyshev error weighted by `t⁻²`

The weighted error `(ψ(t) - t) / t²` of Chebyshev's function is integrable on every ray
`(y, ∞)` with `y > 0`. Its integral over `(1, ∞)` is `-1 - γ`, read off from the finite part of
`ζ′/ζ` at one, and by the de la Vallée Poussin bound its tail above `y ≥ 1` is
`O(exp(-c √(log y)))`.

## Main results

* `Chebyshev.psi_sub_div_sq_eq_neg_inv_of_le_one`: `(ψ t - t) / t² = -t⁻¹` for `t ≤ 1`.
* `Chebyshev.exists_abs_integral_psi_sub_div_sq_le`: integrability above one and the tail bound.
* `Chebyshev.integrableOn_psi_sub_div_sq`: integrability above every positive cutoff.
* `Chebyshev.integral_psi_sub_div_sq`: `∫_{1}^{∞} (ψ(t) - t) / t² dt = -1 - γ`.
-/

public section

open ArithmeticFunction Complex Filter MeasureTheory Set
open scoped Chebyshev Topology

namespace Chebyshev

/-- The weighted Chebyshev error `(ψ t - t) / t²` is integrable above one, and its tail above
`y ≥ 1` decays like `exp (-c √(log y))`. -/
theorem exists_abs_integral_psi_sub_div_sq_le :
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
          have he : Real.exp u * Real.exp (-(2 * u)) = Real.exp (-(c / 2 * √(Real.log y))) := by
            rw [← Real.exp_add]
            congr 1
            dsimp only [u]
            ring
          linear_combination (C * (4 / c ^ 2)) * he

/-- Below one the Chebyshev function vanishes, so the weighted error is `-t⁻¹`. -/
theorem psi_sub_div_sq_eq_neg_inv_of_le_one {t : ℝ} (ht : t ≤ 1) :
    (ψ t - t) / t ^ 2 = -t⁻¹ := by
  rw [psi_eq_zero_of_le_one ht, zero_sub]
  rcases eq_or_ne t 0 with rfl | h
  · simp
  · field_simp

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
    exact fun t ht ↦ (psi_sub_div_sq_eq_neg_inv_of_le_one ht.2).symm
  rw [← Ioc_union_Ioi_eq_Ioi h.le]
  exact hsmall.union hE

/-- The weighted summatory error of the von Mangoldt Dirichlet series in real coordinates. -/
theorem sum_vonMangoldt_sub_div_sq (t : ℝ) :
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
  have heq := tendsto_nhds_unique h TauCeti.LSeries.tendsto_LSeries_vonMangoldt_sub_div_sub_one
  simpa only [← ofReal_one,
    ← ofReal_neg, ← ofReal_sub, ofReal_inj] using heq

end Chebyshev
