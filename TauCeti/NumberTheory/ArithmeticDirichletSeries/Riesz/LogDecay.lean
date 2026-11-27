/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.SummatoryTail
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.AbelSummation

/-!
# Logarithmic moments of the first Riesz remainder

A summatory error of order `t / (log t)^(B+2)` makes the `B`-th logarithmic moment of its
`t⁻²`-weighted tail absolutely integrable. The integral of this moment over `(y, ∞)`
tends to zero and bounds the centered normalized Riesz sum multiplied by `(log y)^B`.
-/

public section

open Asymptotics Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- The `B`-th logarithmic moment of the weighted summatory error is integrable on a tail;
the unweighted error is integrable all the way down to `1`. -/
private theorem integrableOn_riesz_log_moment {a : ℕ → ℂ} {A : ℂ} (B : ℕ)
    (hE : (fun t : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) =O[atTop]
      fun t ↦ t / log t ^ (B + 2)) :
    let E (t : ℝ) : ℂ := ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2
    IntegrableOn E (Ioi 1) ∧ ∃ U > 1, IntegrableOn (fun t ↦ log t ^ B • E t) (Ioi U) := by
  intro E
  obtain ⟨C, hC⟩ := hE.exists_nonneg
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC.2.bound
  let U := max (exp 1) T
  have hU : 1 < U := (one_lt_exp_iff.mpr zero_lt_one).trans_le (le_max_left ..)
  have hU₀ : 0 < U := zero_lt_one.trans hU
  have hsum : Measurable (fun t : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) :=
    (measurable_of_countable (fun m : ℕ ↦ ∑ n ∈ Finset.Icc 1 m, a n)).comp Nat.measurable_floor
  have hmeas : Measurable E :=
    (hsum.sub (measurable_const.mul Complex.continuous_ofReal.measurable)).div
      (Complex.continuous_ofReal.measurable.pow_const 2)
  have hmom : IntegrableOn (fun t ↦ log t ^ B • E t) (Ioi U) := by
    rw [← exp_log hU₀, ← integrableOn_comp_exp_Ioi]
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num)
      (log_pos hU)).const_mul C) ?_ ?_
    · have hm := ((measurable_log.pow_const B).smul hmeas).comp continuous_exp.measurable
      exact (continuous_exp.measurable.smul hm).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv₀ : 0 < v := (log_pos hU).trans hv
    have hUv : U < exp v := (log_lt_iff_lt_exp hU₀).mp hv
    have h := hT (exp v) ((le_max_right ..).trans hUv.le)
    rw [log_exp, Real.norm_of_nonneg (by positivity : 0 ≤ exp v / v ^ (B + 2))] at h
    simp only [E, norm_smul, log_exp, norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (exp_pos v).le, Real.norm_of_nonneg (pow_nonneg hv₀.le B),
      rpow_neg hv₀.le, rpow_two]
    calc
      exp v * (v ^ B * (‖(∑ n ∈ Finset.Icc 1 ⌊exp v⌋₊, a n) - A * ↑(exp v)‖ / exp v ^ 2))
        ≤ exp v * (v ^ B * ((C * (exp v / v ^ (B + 2))) / exp v ^ 2)) := by gcongr
      _ = C * (v ^ 2)⁻¹ := by field_simp; ring
  refine ⟨?_, U, hU, hmom⟩
  have htail : IntegrableOn E (Ioi U) := by
    refine Integrable.mono' (Integrable.norm hmom) hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hlog : 1 ≤ log t := by
      rw [← log_exp 1]
      exact log_le_log (exp_pos _) ((le_max_left .. : exp 1 ≤ U).trans ht.le)
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hlog) _)]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hlog)
  have hF : ContinuousOn (fun t : ℝ ↦ ((t : ℂ) ^ 2)⁻¹) (Icc 1 U) :=
    (Complex.continuous_ofReal.pow 2).continuousOn.inv₀ fun t ht ↦
      pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le ht.1).ne')
  have hi₁ := integrableOn_mul_sum_Icc (m := 1) a zero_le_one hF.integrableOn_Icc
  have hi₂ := (hF.mul (Complex.continuous_ofReal.const_mul A).continuousOn).integrableOn_Icc
    (μ := volume)
  have hfin : IntegrableOn E (Icc 1 U) := hi₁.sub hi₂ |>.congr_fun
    (fun t _ ↦ by simp only [E, Pi.sub_apply, Pi.mul_apply, div_eq_mul_inv]; ring)
    measurableSet_Icc
  exact (hfin.union htail).mono_set fun t ht ↦
    if ht' : t ≤ U then Or.inl ⟨ht.le, ht'⟩ else Or.inr (lt_of_not_ge ht')

/-- The normalized first Riesz sum, centered at its limit after removal of the logarithmic
main term, is little-o of `(log y)⁻ᴮ` if the unsmoothed error is `O(y / (log y)^(B+2))`.
The conclusion is written as convergence of the logarithmically rescaled remainder. -/
theorem tendsto_log_pow_smul_rieszSum_div_sub_log_sub {a : ℕ → ℂ} {A c : ℂ} (B : ℕ)
    (hE : (fun t : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) =O[atTop]
      fun t ↦ t / log t ^ (B + 2))
    (hc : Tendsto (fun y : ℝ ↦ rieszSum a y / (y : ℂ) - A * (log y : ℂ)) atTop (𝓝 c)) :
    Tendsto (fun y : ℝ ↦ log y ^ B • (rieszSum a y / (y : ℂ) - A * (log y : ℂ) - c))
      atTop (𝓝 0) := by
  let E (t : ℝ) : ℂ := ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, a n) - A * t) / (t : ℂ) ^ 2
  obtain ⟨hi, U, hU, hmom⟩ := integrableOn_riesz_log_moment B hE
  rw [tendsto_nhds_unique hc (tendsto_rieszSum_div_sub_log a A hi)]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_integral_Ioi_zero (μ := volume) (f := fun t ↦ ‖log t ^ B • E t‖) tendsto_id)
  filter_upwards [eventually_ge_atTop U] with y hy
  rw [rieszSum_div_sub_log_sub_integral_eq_neg_integral a A hi (hU.le.trans hy),
    smul_neg, norm_neg, ← integral_smul]
  have htail : IntegrableOn E (Ioi y) := hi.mono_set (Ioi_subset_Ioi (hU.le.trans hy))
  refine (norm_integral_le_integral_norm _).trans <|
    setIntegral_mono_on (Integrable.norm (Integrable.smul (log y ^ B) htail))
      (Integrable.norm (hmom.mono_set (Ioi_subset_Ioi hy))) measurableSet_Ioi fun t ht ↦ ?_
  have hy₀ : 0 ≤ log y := (log_pos (hU.trans_le hy)).le
  have hlog := log_le_log (zero_lt_one.trans (hU.trans_le hy)) ht.le
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg hy₀ _),
    Real.norm_of_nonneg (pow_nonneg (hy₀.trans hlog) _)]
  gcongr

end TauCeti
