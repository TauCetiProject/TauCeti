/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.SummatoryMellin
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mellin transform after subtraction of a linear summatory main term

Subtracting `A * x` from a Dirichlet series' summatory function subtracts `A / (s - 1)`
from its Mellin transform. If the Dirichlet series converges for real `s` sufficiently
close to `1` from above and the summatory error weighted by `x⁻²` is integrable on `(1, ∞)`,
this transform has a right-hand limit at `1`. This identifies the constant term in smoothed
summation formulas with the right-hand limit at `1` of the compensated Dirichlet series.
-/

public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.LSeries

/-- The compensated Dirichlet series divided by its parameter is the Mellin transform of
the summatory error. Here the pole is subtracted as `A / (s - 1)` after division by `s`. -/
theorem integral_summatory_sub_linear_mul_cpow {a : ℕ → ℂ} (A : ℂ) {s : ℂ}
    (ha : LSeriesSummable a s) (hs : 1 < s.re) :
    (∫ t in Ioi (1 : ℝ), ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) * (t : ℂ) ^ (-(s + 1))) =
      LSeries a s / s - A / (s - 1) := by
  have hQ : (-s).re < -1 := by simpa using hs
  have hlin : (fun t : ℝ ↦ A * (t : ℂ) * (t : ℂ) ^ (-(s + 1))) =ᵐ[volume.restrict (Ioi 1)]
      fun t ↦ A * (t : ℂ) ^ (-s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    rw [mul_assoc]
    congr 1
    calc
      (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (1 + -(s + 1)) := by
        rw [cpow_add _ _ ht₀, cpow_one]
      _ = (t : ℂ) ^ (-s) := by ring_nf
  simp_rw [sub_mul]
  rw [integral_sub (ha.integrableOn_summatory_mul_cpow (zero_lt_one.trans hs))
    (((integrableOn_Ioi_cpow_of_lt hQ zero_lt_one).const_mul A).congr hlin.symm),
    ha.integral_summatory_mul_cpow (zero_lt_one.trans hs), integral_congr_ae hlin,
    integral_const_mul, integral_Ioi_cpow_of_lt hQ zero_lt_one, ofReal_one, one_cpow]
  have he : -s + 1 = -(s - 1) := by ring
  rw [he, neg_div_neg_eq, mul_one_div]

/-- If the Dirichlet series of `a` is summable for real parameters sufficiently close to `1`
from above and the summatory error divided by `x²` is integrable on `(1, ∞)`, the compensated
Dirichlet series has a right-hand limit at `1` given by the integral of that weighted error. -/
theorem tendsto_sub_linear_pole_of_integrable_summatory_error {a : ℕ → ℂ} (A : ℂ)
    (ha : ∀ᶠ σ : ℝ in 𝓝[>] 1, LSeriesSummable a (σ : ℂ))
    (hE : IntegrableOn (fun t : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2)
      (Ioi 1)) :
    Tendsto (fun σ : ℝ ↦ LSeries a (σ : ℂ) - A * σ / ((σ : ℂ) - 1)) (𝓝[>] 1)
      (𝓝 (∫ t in Ioi (1 : ℝ), ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2)) := by
  let E (t : ℝ) : ℂ := ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2
  let K (σ t : ℝ) : ℂ := (t : ℂ) ^ (1 - (σ : ℂ))
  have hLim : Tendsto (fun σ : ℝ ↦ ∫ t in Ioi (1 : ℝ), E t * K σ t) (𝓝[>] 1)
      (𝓝 (∫ t in Ioi (1 : ℝ), E t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t ↦ ‖E t‖) ?_ ?_ hE.norm ?_
    · exact .of_forall fun σ ↦ hE.aestronglyMeasurable.mul
        ((measurable_ofReal.pow_const (1 - (σ : ℂ))).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin (s := Ioi (1 : ℝ))] with σ hσ
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hK : ‖K σ t‖ ≤ 1 := by
        dsimp only [K]
        rw [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), sub_re, one_re, ofReal_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos ht.le (sub_nonpos.mpr hσ.le)
      simpa only [norm_mul, mul_one] using mul_le_mul_of_nonneg_left hK (norm_nonneg (E t))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht₀ : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
      have h : ContinuousAt (fun σ : ℝ ↦ E t * K σ t) 1 := by
        have hpow := continuous_const_cpow' ht₀
        exact (hpow.comp (by fun_prop : Continuous fun σ : ℝ ↦ 1 - (σ : ℂ))).const_mul (E t)
          |>.continuousAt
      simpa [K] using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
  have hId : Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] 1) (𝓝 1) := by
    simpa using (continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
  refine (by simpa only [one_mul] using hId.mul hLim : Tendsto (fun σ : ℝ ↦
    (σ : ℂ) * (∫ t in Ioi (1 : ℝ), E t * K σ t)) (𝓝[>] 1) (𝓝 (∫ t in Ioi (1 : ℝ), E t)))
    |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin (s := Ioi (1 : ℝ)), ha] with σ hσ hsum
  have hσ₀ : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans hσ).ne'
  have hInt : (∫ t in Ioi (1 : ℝ), E t * K σ t) =
      LSeries a (σ : ℂ) / (σ : ℂ) - A / ((σ : ℂ) - 1) := by
    refine (setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_).trans
      (integral_summatory_sub_linear_mul_cpow A hsum (by simpa using hσ))
    have ht₀ : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    dsimp only [E, K]
    rw [div_eq_mul_inv, mul_assoc, ← cpow_two, ← cpow_neg, ← cpow_add _ _ ht₀]
    ring_nf
  rw [hInt, mul_sub, mul_div_cancel₀ _ hσ₀, ← mul_div_assoc, mul_comm (σ : ℂ) A]

end TauCeti.LSeries
