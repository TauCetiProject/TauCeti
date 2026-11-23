/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Exp.Taylor
import TauCeti.Analysis.SpecialFunctions.Log.InvLog

/-!
# Principal value and integral representations of `li`

This file records the exponential principal value and absolutely convergent integral representations
of the unoffset logarithmic integral `TauCeti.Real.unoffsetLogIntegral`:

* `Real.eulerMascheroniConstant_eq_integral_sub_integral`:
  `γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`.
* `TauCeti.Real.integral_Iic_exp_div`: for `y < 0`, `∫ u in Iic y, exp u / u = li (exp y)`.
* `TauCeti.Real.tendsto_principalValue_exp_div`,
  `TauCeti.Real.tendsto_principalValue_exp_div_log`: for `y > 0`, the Cauchy principal value
  `∫ u in (-1 / ε)..(-ε), exp u / u + ∫ u in ε..y, exp u / u →`
  `γ + log y + ∫ u in 0..y, (exp u - 1) / u`, which equals `li x` at `y = log x` (`x > 1`).
* `TauCeti.Real.unoffsetLogIntegral_eq_log_abs_sub_one_add_integral`: for `x > 0`, `x ≠ 1`,
  `li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)`.
* `TauCeti.Real.unoffsetLogIntegral_two_eq_integral`,
  `TauCeti.Real.abs_inv_log_one_add_add_inv_log_one_sub_le`:
  `li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)` and the bound
  `|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3` on `(0, 1 / 2]`.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Real

/-- For every `a > 0`, `t ↦ exp (-t) / t` is integrable on `(a, ∞)`. -/
theorem integrableOn_Ioi_exp_neg_div {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) / t) (Ioi a) := by
  have hexp : IntegrableOn (fun t : ℝ ↦ a⁻¹ * Real.exp (-t)) (Ioi a) :=
    (integrableOn_exp_neg_Ioi a).const_mul a⁻¹
  refine hexp.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp continuous_neg).measurable.div
      measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ha.trans ht
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) ht0)]
    calc Real.exp (-t) / t
        = t⁻¹ * Real.exp (-t) := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ a⁻¹ * Real.exp (-t) := by
          gcongr
          exact ht.le

/-- **Integral formula for Euler's constant**:
`γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`. -/
theorem eulerMascheroniConstant_eq_integral_sub_integral :
    Real.eulerMascheroniConstant =
      (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) -
        ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t := by
  have h01 := TauCeti.Real.integral_one_sub_exp_neg_div_eq_sub_integral (z := 1) zero_le_one
  simp only [Real.log_one, mul_zero, zero_sub] at h01
  have hibp : ∀ b : ℝ, 1 ≤ b →
      ∫ t in (1 : ℝ)..b, Real.exp (-t) / t =
        Real.exp (-b) * Real.log b + ∫ t in (1 : ℝ)..b, Real.log t * Real.exp (-t) := by
    intro b hb
    let f (t : ℝ) : ℝ := -Real.exp (-t) * Real.log t
    let f' (t : ℝ) : ℝ := Real.exp (-t) * Real.log t - Real.exp (-t) / t
    have hderiv : ∀ t ∈ uIcc (1 : ℝ) b, HasDerivAt f (f' t) t := by
      intro t ht
      rw [uIcc_of_le hb] at ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht.1
      have h1 : HasDerivAt (fun s : ℝ ↦ -Real.exp (-s)) (Real.exp (-t)) t := by
        simpa using ((hasDerivAt_neg t).exp).fun_neg
      have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0.ne'
      refine (h1.mul h2).congr_deriv ?_
      simp only [f', div_eq_mul_inv]
      ring
    have hint_log : IntervalIntegrable (fun t : ℝ ↦ Real.log t * Real.exp (-t)) volume 1 b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
      exact TauCeti.Real.integrableOn_Ioi_log_mul_exp_neg.mono_set
        (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one))
    have hint_exp : IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) / t) volume 1 b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
      exact (integrableOn_Ioi_exp_neg_div zero_lt_one).mono_set Ioc_subset_Ioi_self
    have hint_mul : IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) * Real.log t) volume 1 b := by
      simpa only [mul_comm] using hint_log
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint_mul.sub hint_exp)
    rw [intervalIntegral.integral_sub hint_mul hint_exp] at hFTC
    have hf1 : f 1 = 0 := by simp [f]
    have hcomm : (∫ t in (1 : ℝ)..b, Real.exp (-t) * Real.log t) =
        ∫ t in (1 : ℝ)..b, Real.log t * Real.exp (-t) :=
      intervalIntegral.integral_congr fun t _ ↦ mul_comm _ _
    dsimp only [f] at hFTC
    linarith
  have htend_exp : Tendsto (fun b : ℝ ↦ ∫ t in (1 : ℝ)..b, Real.exp (-t) / t) atTop
      (𝓝 (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t)) :=
    intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_Ioi_exp_neg_div zero_lt_one) tendsto_id
  have htend_b : Tendsto (fun b : ℝ ↦ Real.exp (-b) * Real.log b) atTop (𝓝 0) := by
    have hpoly : Tendsto (fun b : ℝ ↦ b * Real.exp (-b)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero' (g := fun b : ℝ ↦ b * Real.exp (-b)) ?_ ?_ hpoly
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      exact mul_nonneg (Real.exp_pos _).le (Real.log_nonneg hb)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.log_le_self (by positivity)) (Real.exp_pos _).le
  have hint_Ioi1 : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 1) :=
    TauCeti.Real.integrableOn_Ioi_log_mul_exp_neg.mono_set (Ioi_subset_Ioi zero_le_one)
  have htend_log : Tendsto (fun b : ℝ ↦ ∫ t in (1 : ℝ)..b, Real.log t * Real.exp (-t)) atTop
      (𝓝 (∫ t in Ioi (1 : ℝ), Real.log t * Real.exp (-t))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hint_Ioi1 tendsto_id
  have heq_Ioi1 : (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t) =
      ∫ t in Ioi (1 : ℝ), Real.log t * Real.exp (-t) := by
    refine tendsto_nhds_unique htend_exp ?_
    have hsum := htend_b.add htend_log
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
    exact (hibp b hb).symm
  have hunion : (∫ t in Ioc (0 : ℝ) 1, Real.log t * Real.exp (-t)) +
      ∫ t in Ioi (1 : ℝ), Real.log t * Real.exp (-t) =
        ∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t) := by
    have h01_int : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioc 0 1) :=
      TauCeti.Real.integrableOn_Ioi_log_mul_exp_neg.mono_set Ioc_subset_Ioi_self
    rw [← MeasureTheory.setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h01_int hint_Ioi1,
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [h01, heq_Ioi1, intervalIntegral.integral_of_le zero_le_one,
    Real.eulerMascheroniConstant_eq_neg_integral_log]
  linarith

end Real

namespace TauCeti.Real

/-! ### Auxiliary filled-in integrands -/

private theorem continuous_one_sub_exp_neg_div :
    Continuous fun t : ℝ ↦ if t = 0 then (1 : ℝ) else (1 - Real.exp (-t)) / t := by
  have heq : (fun t : ℝ ↦ if t = 0 then (1 : ℝ) else (1 - Real.exp (-t)) / t) =
      fun t : ℝ ↦ if -t = 0 then (1 : ℝ) else (Real.exp (-t) - 1) / (-t) := by
    ext t
    by_cases ht : t = 0
    · simp [ht]
    · have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
      simp only [ht, ↓reduceIte, hnt]
      ring
  rw [heq]
  exact continuous_exp_sub_one_div.comp continuous_neg

private theorem intervalIntegrable_one_sub_exp_neg_div (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) volume a b := by
  refine (continuous_one_sub_exp_neg_div.intervalIntegrable a b).congr_ae ?_
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [ae_restrict_of_ae hne] with t ht
  simp [ht]

private theorem intervalIntegrable_exp_sub_one_div (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ (Real.exp u - 1) / u) volume a b := by
  refine (continuous_exp_sub_one_div.intervalIntegrable a b).congr_ae ?_
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [ae_restrict_of_ae hne] with u hu
  simp [hu]

private theorem intervalIntegrable_exp_neg_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) / t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id fun t ht ↦ ?_
  rw [mem_uIcc] at ht
  rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact (ha.trans_le h1).ne'
  · exact (hb.trans_le h1).ne'

private theorem intervalIntegrable_inv_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_id.inv₀ fun t ht ↦ ?_
  rw [mem_uIcc] at ht
  rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact (ha.trans_le h1).ne'
  · exact (hb.trans_le h1).ne'

/-! ### Exponential form of the principal value -/

/-- For every `y < 0`, `u ↦ exp u / u` is integrable on `(-∞, y]`. -/
theorem integrableOn_Iic_exp_div {y : ℝ} (hy : y < 0) :
    IntegrableOn (fun u : ℝ ↦ Real.exp u / u) (Iic y) := by
  have hexp : IntegrableOn (fun u : ℝ ↦ (-y)⁻¹ * Real.exp u) (Iic y) :=
    (integrableOn_exp_Iic y).const_mul (-y)⁻¹
  refine hexp.mono' ?_ ?_
  · exact (Real.continuous_exp.measurable.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    have hu0 : u < 0 := hu.trans_lt hy
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos u), abs_of_neg hu0, div_eq_mul_inv,
      mul_comm]
    exact mul_le_mul_of_nonneg_right
      (inv_anti₀ (neg_pos.mpr hy) (neg_le_neg (mem_Iic.mp hu))) (Real.exp_pos u).le

/-- For `y < 0`, `∫ u in Iic y, exp u / u = li (exp y)`. -/
theorem integral_Iic_exp_div {y : ℝ} (hy : y < 0) :
    ∫ u in Iic y, Real.exp u / u = unoffsetLogIntegral (Real.exp y) := by
  set z : ℝ := -y
  have hz : 0 < z := neg_pos.mpr hy
  have htend_lhs : Tendsto (fun a : ℝ ↦ ∫ u in a..y, Real.exp u / u) atBot
      (𝓝 (∫ u in Iic y, Real.exp u / u)) :=
    intervalIntegral_tendsto_integral_Iic y (integrableOn_Iic_exp_div hy) tendsto_id
  have htend_rhs : Tendsto (fun a : ℝ ↦ -∫ t in z..(-a), Real.exp (-t) / t) atBot
      (𝓝 (-∫ t in Ioi z, Real.exp (-t) / t)) :=
    (intervalIntegral_tendsto_integral_Ioi z (Real.integrableOn_Ioi_exp_neg_div hz)
      tendsto_neg_atBot_atTop).neg
  have heq_Ioi : (∫ u in Iic y, Real.exp u / u) = -∫ t in Ioi z, Real.exp (-t) / t := by
    refine tendsto_nhds_unique htend_lhs ?_
    refine htend_rhs.congr' ?_
    filter_upwards with a
    have hcomp := intervalIntegral.integral_comp_neg (f := fun u : ℝ ↦ Real.exp u / u) (a := z)
      (b := -a)
    have hneg : (fun t : ℝ ↦ Real.exp (-t) / (-t)) = fun t : ℝ ↦ -(Real.exp (-t) / t) := by
      ext t; ring
    rw [hneg, intervalIntegral.integral_neg, neg_neg] at hcomp
    simpa [z] using hcomp
  have hsub_Ioi : ∫ t in (1 : ℝ)..z, Real.exp (-t) / t =
      (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t) - ∫ t in Ioi z, Real.exp (-t) / t :=
    (intervalIntegral.integral_Ioi_sub_Ioi'
      (Real.integrableOn_Ioi_exp_neg_div zero_lt_one)
      (Real.integrableOn_Ioi_exp_neg_div hz)).symm
  have h1z_inv : ∫ t in (1 : ℝ)..z, t⁻¹ = Real.log z := by
    rw [integral_inv_of_pos zero_lt_one hz, div_one]
  have h1z_diff : ∫ t in (1 : ℝ)..z, (1 - Real.exp (-t)) / t =
      Real.log z - ∫ t in (1 : ℝ)..z, Real.exp (-t) / t := by
    have hint1 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume 1 z :=
      intervalIntegrable_inv_pos zero_lt_one hz
    have hint2 : IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) / t) volume 1 z :=
      intervalIntegrable_exp_neg_div zero_lt_one hz
    have hcongr : (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) =
        fun t : ℝ ↦ t⁻¹ - Real.exp (-t) / t := by
      ext t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp [ht]
    rw [hcongr, intervalIntegral.integral_sub hint1 hint2, h1z_inv]
  have h0z : ∫ t in (0 : ℝ)..z, (1 - Real.exp (-t)) / t =
      (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) +
        ∫ t in (1 : ℝ)..z, (1 - Real.exp (-t)) / t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_one_sub_exp_neg_div 0 1)
      (intervalIntegrable_one_sub_exp_neg_div 1 z)).symm
  have hgamma := Real.eulerMascheroniConstant_eq_integral_sub_integral
  have h0z_tsum := integral_one_sub_exp_neg_div_eq z
  simp only [show -z = y by simp [z]] at h0z_tsum
  rw [unoffsetLogIntegral_def, Real.log_exp y]
  have hlogabs : Real.log y = Real.log z := by
    simp [z]
  rw [hlogabs]
  linarith

/-- **Exponential form of the Cauchy principal value** (`y > 0`):
`lim_{ε → 0⁺} (∫ u in (-1/ε)..(-ε), eᵘ/u du + ∫ u in ε..y, eᵘ/u du) =`
`γ + log y + ∫₀^y (eᵘ - 1)/u du`. -/
theorem tendsto_principalValue_exp_div {y : ℝ} (hy : 0 < y) :
    Tendsto (fun ε : ℝ ↦ (∫ u in (-1 / ε)..(-ε), Real.exp u / u) +
        ∫ u in ε..y, Real.exp u / u)
      (𝓝[>] 0) (𝓝 (Real.eulerMascheroniConstant + Real.log y +
        ∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u)) := by
  let f₁ (t : ℝ) : ℝ := if t = 0 then 1 else (1 - Real.exp (-t)) / t
  let f₂ (u : ℝ) : ℝ := if u = 0 then 1 else (Real.exp u - 1) / u
  have hcont₁ : Continuous (fun a : ℝ ↦ ∫ t in a..1, f₁ t) := by
    have hprim := intervalIntegral.continuous_primitive (μ := volume)
      (fun a b ↦ continuous_one_sub_exp_neg_div.intervalIntegrable a b) 1
    refine hprim.neg.congr fun a ↦ ?_
    simp [intervalIntegral.integral_symm 1 a, f₁]
  have htend₁ : Tendsto (fun ε : ℝ ↦ ∫ t in ε..1, (1 - Real.exp (-t)) / t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t)) := by
    have h1 := (hcont₁.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have heq : ∀ a : ℝ, ∫ t in a..1, f₁ t = ∫ t in a..1, (1 - Real.exp (-t)) / t := by
      intro a
      refine intervalIntegral.integral_congr_ae ?_
      have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := ae_iff.mpr (by simp)
      filter_upwards [hne] with t ht _
      simp [f₁, ht]
    simpa [heq] using h1
  have htend₂ : Tendsto (fun ε : ℝ ↦ ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t)) :=
    (intervalIntegral_tendsto_integral_Ioi 1 (Real.integrableOn_Ioi_exp_neg_div zero_lt_one)
      tendsto_id).comp tendsto_inv_nhdsGT_zero
  have hcont₃ : Continuous (fun a : ℝ ↦ ∫ u in a..y, f₂ u) := by
    have hprim := intervalIntegral.continuous_primitive (μ := volume)
      (fun a b ↦ continuous_exp_sub_one_div.intervalIntegrable a b) y
    refine hprim.neg.congr fun a ↦ ?_
    simp [intervalIntegral.integral_symm y a, f₂]
  have htend₃ : Tendsto (fun ε : ℝ ↦ ∫ u in ε..y, (Real.exp u - 1) / u) (𝓝[>] 0)
      (𝓝 (∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u)) := by
    have h1 := (hcont₃.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have heq : ∀ a : ℝ, ∫ u in a..y, f₂ u = ∫ u in a..y, (Real.exp u - 1) / u := by
      intro a
      refine intervalIntegral.integral_congr_ae ?_
      have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
      filter_upwards [hne] with u hu _
      simp [f₂, hu]
    simpa [heq] using h1
  have hlim : Tendsto (fun ε : ℝ ↦
      ((∫ t in ε..1, (1 - Real.exp (-t)) / t) - ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t) +
        Real.log y + ∫ u in ε..y, (Real.exp u - 1) / u) (𝓝[>] 0)
      (𝓝 (((∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) -
          ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t) + Real.log y +
        ∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u)) :=
    ((htend₁.sub htend₂).add tendsto_const_nhds).add htend₃
  rw [← Real.eulerMascheroniConstant_eq_integral_sub_integral] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one hy)] with ε hε
  have hε0 : 0 < ε := hε.1
  have hinv_pos : 0 < ε⁻¹ := inv_pos.mpr hε0
  have hcomp := intervalIntegral.integral_comp_neg (f := fun u : ℝ ↦ Real.exp u / u)
    (a := ε) (b := ε⁻¹)
  have hneg : (fun t : ℝ ↦ Real.exp (-t) / (-t)) = fun t : ℝ ↦ -(Real.exp (-t) / t) := by
    ext t; ring
  have hneg_a : -ε⁻¹ = -1 / ε := by ring
  rw [hneg, hneg_a, intervalIntegral.integral_neg] at hcomp
  have hleft_split : ∫ t in ε..ε⁻¹, Real.exp (-t) / t =
      (∫ t in ε..1, Real.exp (-t) / t) + ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_neg_div hε0 zero_lt_one)
      (intervalIntegrable_exp_neg_div zero_lt_one hinv_pos)).symm
  have hε1_inv : ∫ t in ε..1, t⁻¹ = -Real.log ε := by
    rw [integral_inv_of_pos hε0 zero_lt_one, one_div, Real.log_inv]
  have hε1_diff : ∫ t in ε..1, (1 - Real.exp (-t)) / t =
      -Real.log ε - ∫ t in ε..1, Real.exp (-t) / t := by
    have hint1 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume ε 1 :=
      intervalIntegrable_inv_pos hε0 zero_lt_one
    have hint2 : IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) / t) volume ε 1 :=
      intervalIntegrable_exp_neg_div hε0 zero_lt_one
    have hcongr : (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) =
        fun t : ℝ ↦ t⁻¹ - Real.exp (-t) / t := by
      ext t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp [ht]
    rw [hcongr, intervalIntegral.integral_sub hint1 hint2, hε1_inv]
  have hεy_inv : ∫ u in ε..y, u⁻¹ = Real.log y - Real.log ε := by
    rw [integral_inv_of_pos hε0 hy, Real.log_div hy.ne' hε0.ne']
  have hεy_exp : ∫ u in ε..y, Real.exp u / u =
      (Real.log y - Real.log ε) + ∫ u in ε..y, (Real.exp u - 1) / u := by
    have hint1 : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume ε y :=
      intervalIntegrable_inv_pos hε0 hy
    have hint2 : IntervalIntegrable (fun u : ℝ ↦ (Real.exp u - 1) / u) volume ε y :=
      intervalIntegrable_exp_sub_one_div ε y
    have hcongr : (fun u : ℝ ↦ Real.exp u / u) = fun u : ℝ ↦ u⁻¹ + (Real.exp u - 1) / u := by
      ext u
      by_cases hu : u = 0
      · simp [hu]
      · field_simp [hu]
        ring
    rw [hcongr, intervalIntegral.integral_add hint1 hint2, hεy_inv]
  linarith

/-- For `x > 1`, `lim_{ε → 0⁺} (∫ u in (-1/ε)..(-ε), eᵘ/u du + ∫ u in ε..(log x), eᵘ/u du) =`
`li x`. -/
theorem tendsto_principalValue_exp_div_log {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ ↦ (∫ u in (-1 / ε)..(-ε), Real.exp u / u) +
        ∫ u in ε..(Real.log x), Real.exp u / u)
      (𝓝[>] 0) (𝓝 (unoffsetLogIntegral x)) := by
  have h := tendsto_principalValue_exp_div (Real.log_pos hx)
  rw [integral_exp_sub_one_div_eq_tsum (Real.log x), ← unoffsetLogIntegral_def] at h
  exact h

/-! ### Absolutely convergent integral representations -/

private theorem tendsto_exp_sub_one_sub_div_sq :
    Tendsto (fun h : ℝ ↦ (Real.exp h - 1 - h) / h ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hbound : ∀ h : ℝ, |h| ≤ 1 / 2 →
      |(∫ s in (0 : ℝ)..1, (1 - s) * Real.exp (h * s)) - 1 / 2| ≤ 2 * |h| := by
    intro h hh
    have hint1 : IntervalIntegrable (fun s : ℝ ↦ (1 - s) * Real.exp (h * s)) volume 0 1 :=
      (by fun_prop : Continuous fun s : ℝ ↦ (1 - s) * Real.exp (h * s)).intervalIntegrable 0 1
    have hint2 : IntervalIntegrable (fun s : ℝ ↦ (1 - s)) volume 0 1 :=
      (by fun_prop : Continuous fun s : ℝ ↦ (1 - s)).intervalIntegrable 0 1
    have hhalf : ∫ s in (0 : ℝ)..1, (1 - s) = (1 / 2 : ℝ) := by
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s : ℝ ↦ s - s ^ 2 / 2) (f' := fun s : ℝ ↦ 1 - s)
        (fun s _ ↦ by
          simpa using (hasDerivAt_id s).fun_sub ((hasDerivAt_pow 2 s).div_const 2))
        hint2
      norm_num at hFTC
      exact hFTC
    have hdiff : (∫ s in (0 : ℝ)..1, (1 - s) * Real.exp (h * s)) - 1 / 2 =
        ∫ s in (0 : ℝ)..1, (1 - s) * (Real.exp (h * s) - 1) := by
      rw [← hhalf, ← intervalIntegral.integral_sub hint1 hint2]
      refine intervalIntegral.integral_congr fun s _ ↦ ?_
      ring
    rw [hdiff]
    have hpt : ∀ s ∈ Icc (0 : ℝ) 1, ‖(1 - s) * (Real.exp (h * s) - 1)‖ ≤ 2 * |h| := by
      intro s hs
      have h1s : |1 - s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hneg : -|h| ≤ h * s := by
        rcases le_total 0 h with hh0 | hh0
        · rw [abs_of_nonneg hh0]
          nlinarith [hs.1, hs.2]
        · rw [abs_of_nonpos hh0]
          nlinarith [hs.1, hs.2]
      have hpos : h * s ≤ |h| := by
        calc h * s ≤ |h * s| := le_abs_self _
          _ = |h| * |s| := abs_mul h s
          _ ≤ |h| * 1 := by gcongr; exact abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
          _ = |h| := mul_one _
      have hexp_lo : 1 - |h| ≤ Real.exp (h * s) := by
        calc 1 - |h| = -|h| + 1 := by ring
          _ ≤ Real.exp (-|h|) := Real.add_one_le_exp (-|h|)
          _ ≤ Real.exp (h * s) := Real.exp_le_exp.mpr hneg
      have hexp_hi : Real.exp (h * s) ≤ 1 + 2 * |h| := by
        have h1m : 1 - |h| ≤ Real.exp (-|h|) := by linarith [Real.add_one_le_exp (-|h|)]
        have hpos_m : 0 < 1 - |h| := by linarith
        have hinv : Real.exp |h| ≤ (1 - |h|)⁻¹ := by
          calc Real.exp |h| = (Real.exp (-|h|))⁻¹ := by rw [Real.exp_neg, inv_inv]
            _ = 1 / Real.exp (-|h|) := inv_eq_one_div _
            _ ≤ 1 / (1 - |h|) := one_div_le_one_div_of_le hpos_m h1m
            _ = (1 - |h|)⁻¹ := (inv_eq_one_div _).symm
        calc Real.exp (h * s) ≤ Real.exp |h| := Real.exp_le_exp.mpr hpos
          _ ≤ (1 - |h|)⁻¹ := hinv
          _ ≤ 1 + 2 * |h| := by
              rw [inv_le_iff_one_le_mul₀ hpos_m]
              nlinarith [abs_nonneg h]
      have hexp_abs : |Real.exp (h * s) - 1| ≤ 2 * |h| :=
        abs_le.mpr ⟨by linarith [abs_nonneg h], by linarith⟩
      rw [Real.norm_eq_abs, abs_mul]
      calc |1 - s| * |Real.exp (h * s) - 1|
          ≤ 1 * (2 * |h|) := mul_le_mul h1s hexp_abs (abs_nonneg _) zero_le_one
        _ = 2 * |h| := one_mul _
    calc |∫ s in (0 : ℝ)..1, (1 - s) * (Real.exp (h * s) - 1)|
        = ‖∫ s in (0 : ℝ)..1, (1 - s) * (Real.exp (h * s) - 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ (2 * |h|) * |1 - 0| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
          rw [uIoc_of_le zero_le_one] at hs
          exact hpt s ⟨hs.1.le, hs.2⟩
      _ = 2 * |h| := by norm_num
  have htend_int : Tendsto (fun h : ℝ ↦ ∫ s in (0 : ℝ)..1, (1 - s) * Real.exp (h * s))
      (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨min (1 / 2) (ε / 2), lt_min (by norm_num) (half_pos hε), fun h _ hd ↦ ?_⟩
    rw [Real.dist_eq, sub_zero] at hd
    rw [Real.dist_eq]
    exact (hbound h (hd.le.trans (min_le_left _ _))).trans_lt
      (by linarith [hd.trans_le (min_le_right _ _)])
  refine htend_int.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := mem_compl_singleton_iff.mp hh
  have hrem := Real.exp_sub_sum_range_succ_eq_integral 1 h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, pow_succ, one_mul] at hrem
  have hrem' : Real.exp h - 1 - h = h ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * Real.exp (h * s) := by
    calc Real.exp h - 1 - h = Real.exp h - (1 + h) := by ring
      _ = h * h * ∫ s in (0 : ℝ)..1, (1 - s) * Real.exp (h * s) := hrem
      _ = h ^ 2 * ∫ s in (0 : ℝ)..1, (1 - s) * Real.exp (h * s) := by ring
  rw [hrem']
  exact (mul_div_cancel_left₀ _ (pow_ne_zero 2 hh0)).symm

/-- As `t → 0⁺`, `(log t)⁻¹ - (t - 1)⁻¹ → 1`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsGT_zero :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.log_zero] using Real.continuousAt_inv_log_zero.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t : ℝ ↦ (t - 1)⁻¹) (𝓝[>] 0) (𝓝 (-1)) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (t - 1)⁻¹) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa using h1.sub h2

/-- As `t → 1` (`t ≠ 1`), `(log t)⁻¹ - (t - 1)⁻¹ → 1 / 2`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsNE_one :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[≠] 1) (𝓝 (1 / 2 : ℝ)) := by
  have hlog : Tendsto Real.log (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds zero_lt_one)] with t ht ht0
      exact Real.log_ne_zero_of_pos_of_ne_one ht0 ht
  have hden : Tendsto (fun h : ℝ ↦ (Real.exp h - 1) / h) (𝓝[≠] 0) (𝓝 1) := by
    simpa using Real.tendsto_exp_mul_sub_one_div 1
  have hq : Tendsto (fun h : ℝ ↦ ((Real.exp h - 1 - h) / h ^ 2) / ((Real.exp h - 1) / h))
      (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
    convert tendsto_exp_sub_one_sub_div_sq.div hden one_ne_zero using 2
    norm_num
  refine (hq.comp hlog).congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_gt_nhds zero_lt_one)] with t ht1 ht0
  have hlog_ne : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht0 ht1
  have htsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  dsimp only [Function.comp_def]
  rw [Real.exp_log ht0]
  field_simp [hlog_ne, htsub]

/-- Continuous extension of `(log t)⁻¹ - (t - 1)⁻¹` on `[0, ∞)` with value `1` at `0`
and `1 / 2` at `1`. -/
private theorem continuousOn_inv_log_sub_inv_sub_one_ext :
    ContinuousOn
      (fun t : ℝ ↦ if t = 0 then 1 else if t = 1 then (1 / 2 : ℝ) else (Real.log t)⁻¹ - (t - 1)⁻¹)
      (Ici 0) := by
  intro t ht
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt]
    simp only [↓reduceIte]
    have hsub : Tendsto (fun u : ℝ ↦ (Real.log u)⁻¹ - (u - 1)⁻¹) (𝓝[Ici 0 \ {0}] 0) (𝓝 1) :=
      tendsto_inv_log_sub_inv_sub_one_nhdsGT_zero.mono_left
        (nhdsWithin_mono _ fun u hu ↦ lt_of_le_of_ne hu.1 (Ne.symm hu.2))
    refine hsub.congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds zero_lt_one)] with u hu hu1
    have hu0 : u ≠ 0 := hu.2
    simp [hu0, hu1.ne]
  · have htpos : 0 < t := lt_of_le_of_ne ht ht0.symm
    rcases eq_or_ne t 1 with rfl | ht1
    · rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt]
      simp only [one_ne_zero, ↓reduceIte]
      have hsub : Tendsto (fun u : ℝ ↦ (Real.log u)⁻¹ - (u - 1)⁻¹) (𝓝[Ici 0 \ {1}] 1)
          (𝓝 (1 / 2 : ℝ)) :=
        tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.mono_left
          (nhdsWithin_mono _ fun _ hu ↦ hu.2)
      refine hsub.congr' ?_
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_ne_nhds one_ne_zero)] with u hu1 hu0
      have hu1' : u ≠ 1 := hu1.2
      simp [hu0, hu1']
    · have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one htpos ht1
      have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
      have hcont : ContinuousAt (fun u : ℝ ↦ (Real.log u)⁻¹ - (u - 1)⁻¹) t := by
        fun_prop (disch := first | exact ht0 | exact hlog | exact hsub)
      refine (hcont.congr ?_).continuousWithinAt
      filter_upwards [eventually_ne_nhds ht0, eventually_ne_nhds ht1] with u hu0 hu1
      simp [hu0, hu1]

/-- The integrand `(log t)⁻¹ - (t - 1)⁻¹` is interval integrable on `[0, x]` for every `x ≥ 0`. -/
theorem intervalIntegrable_inv_log_sub_inv_sub_one {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) volume 0 x := by
  let g (t : ℝ) : ℝ :=
    if t = 0 then 1 else if t = 1 then (1 / 2 : ℝ) else (Real.log t)⁻¹ - (t - 1)⁻¹
  have hg : IntervalIntegrable g volume 0 x :=
    (continuousOn_inv_log_sub_inv_sub_one_ext.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hx
  refine hg.congr_ae ?_
  have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := ae_iff.mpr (by simp)
  have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := ae_iff.mpr (by simp)
  filter_upwards [ae_restrict_of_ae (hne0.and hne1)] with t ⟨ht0, ht1⟩
  simp [g, ht0, ht1]

/-- **Absolutely convergent integral for `li x`** (`0 < x`, `x ≠ 1`):
`li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)`. -/
theorem unoffsetLogIntegral_eq_log_abs_sub_one_add_integral {x : ℝ} (hx₀ : 0 < x) (hx₁ : x ≠ 1) :
    unoffsetLogIntegral x =
      Real.log |x - 1| + ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  rcases hx₁.lt_or_gt with hx_lt | hx_gt
  · have hlog_abs : Real.log |x - 1| = Real.log (1 - x) := by
      rw [abs_of_neg (sub_neg.mpr hx_lt), neg_sub]
    have hsub_int : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 0 x := by
      refine ContinuousOn.intervalIntegrable_of_Icc hx₀.le fun t ht ↦ ?_
      have hne : t - 1 ≠ 0 := by linarith [ht.2]
      exact (ContinuousAt.inv₀
        (continuous_id.sub continuous_const).continuousAt hne).continuousWithinAt
    have hsub_val : ∫ t in (0 : ℝ)..x, (t - 1)⁻¹ = Real.log (1 - x) := by
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ ↦ Real.log (1 - t)) (f' := fun t : ℝ ↦ (t - 1)⁻¹)
        (fun t ht ↦ by
          rw [uIcc_of_le hx₀.le] at ht
          have h1t : 1 - t ≠ 0 := by linarith [ht.2]
          have ht1 : t - 1 ≠ 0 := by linarith [ht.2]
          have hlin : HasDerivAt (fun s : ℝ ↦ (1 : ℝ) - s) (-1) t :=
            (hasDerivAt_id t).const_sub 1
          exact ((Real.hasDerivAt_log h1t).comp t hlin).congr_deriv (by
            have hinv : (1 - t)⁻¹ * (-1) = (t - 1)⁻¹ := by
              field_simp [h1t, ht1]
              ring
            exact hinv))
        hsub_int
      simpa using hFTC
    rw [hlog_abs, ← hsub_val,
      intervalIntegral.integral_sub (intervalIntegrable_inv_log_of_Ico hx₀.le hx_lt) hsub_int,
      ← unoffsetLogIntegral_eq_integral hx₀ hx_lt]
    ring
  · have hlog_abs : Real.log |x - 1| = Real.log (x - 1) := by
      rw [abs_of_pos (sub_pos.mpr hx_gt)]
    let g (t : ℝ) : ℝ :=
      if t = 0 then 1 else if t = 1 then (1 / 2 : ℝ) else (Real.log t)⁻¹ - (t - 1)⁻¹
    have hg_cont : ContinuousOn g (Icc 0 x) :=
      continuousOn_inv_log_sub_inv_sub_one_ext.mono Icc_subset_Ici_self
    have hg_int_on : IntegrableOn g (uIcc 0 x) := by
      rw [uIcc_of_le hx₀.le]
      exact hg_cont.integrableOn_Icc
    have hg_int : IntervalIntegrable g volume 0 x := hg_cont.intervalIntegrable_of_Icc hx₀.le
    have hprim_cont : ContinuousOn (fun a : ℝ ↦ ∫ t in (0 : ℝ)..a, g t) (Icc 0 x) := by
      simpa only [uIcc_of_le hx₀.le] using
        intervalIntegral.continuousOn_primitive_interval hg_int_on
    have hmid_tend : Tendsto (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), g t) +
        ∫ t in (1 + ε)..x, g t) (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..x, g t)) := by
      have hF1 : Tendsto (fun ε : ℝ ↦ ∫ t in (0 : ℝ)..(1 - ε), g t) (𝓝[>] 0)
          (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
        refine (hprim_cont 1 ⟨zero_le_one, hx_gt.le⟩).tendsto.comp ?_
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have h1 : ContinuousAt (fun ε : ℝ ↦ (1 : ℝ) - ε) 0 := by fun_prop
          simpa using h1.tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
          exact ⟨by linarith [hε.2], by linarith [hε.1, hx_gt]⟩
      have hF2 : Tendsto (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..x, g t) - ∫ t in (0 : ℝ)..(1 + ε), g t)
          (𝓝[>] 0) (𝓝 ((∫ t in (0 : ℝ)..x, g t) - ∫ t in (0 : ℝ)..1, g t)) := by
        refine tendsto_const_nhds.sub ((hprim_cont 1 ⟨zero_le_one, hx_gt.le⟩).tendsto.comp ?_)
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have h1 : ContinuousAt (fun ε : ℝ ↦ (1 : ℝ) + ε) 0 := by fun_prop
          simpa using h1.tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hx_gt)] with ε hε
          exact ⟨by linarith [hε.1], by linarith [hε.2]⟩
      have hadd := hF1.add hF2
      have hsimp : (∫ t in (0 : ℝ)..1, g t) +
          ((∫ t in (0 : ℝ)..x, g t) - ∫ t in (0 : ℝ)..1, g t) = ∫ t in (0 : ℝ)..x, g t := by
        ring
      rw [hsimp] at hadd
      refine hadd.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one (sub_pos.mpr hx_gt))] with ε hε
      have h1p : 1 + ε ∈ uIcc 0 x := by
        rw [uIcc_of_le hx₀.le]
        exact ⟨by linarith [hε.1], by linarith [hε.2.trans_le (min_le_right _ _)]⟩
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (hg_int.mono_set (uIcc_subset_uIcc left_mem_uIcc h1p))
        (hg_int.mono_set (uIcc_subset_uIcc h1p right_mem_uIcc))
      linarith
    have hrhs_tend : Tendsto (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), g t) +
        ∫ t in (1 + ε)..x, g t) (𝓝[>] 0) (𝓝 (unoffsetLogIntegral x - Real.log (x - 1))) := by
      have h1 := (tendsto_principalValue_inv_log hx_gt).sub
        (tendsto_const_nhds (x := Real.log (x - 1)))
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one (sub_pos.mpr hx_gt))] with ε hε
      have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
      have hεx : 1 + ε < x := by linarith [hε.2.trans_le (min_le_right _ _)]
      have hsub1_int : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 0 (1 - ε) := by
        refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) fun t ht ↦ ?_
        have hne : t - 1 ≠ 0 := by linarith [ht.2, hε.1]
        exact (ContinuousAt.inv₀
          (continuous_id.sub continuous_const).continuousAt hne).continuousWithinAt
      have hsub2_int : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume (1 + ε) x := by
        refine ContinuousOn.intervalIntegrable_of_Icc hεx.le fun t ht ↦ ?_
        have hne : t - 1 ≠ 0 := by linarith [ht.1, hε.1]
        exact (ContinuousAt.inv₀
          (continuous_id.sub continuous_const).continuousAt hne).continuousWithinAt
      have hsub1_val : ∫ t in (0 : ℝ)..(1 - ε), (t - 1)⁻¹ = Real.log ε := by
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun t : ℝ ↦ Real.log (1 - t)) (f' := fun t : ℝ ↦ (t - 1)⁻¹)
          (fun t ht ↦ by
            rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ 1 - ε)] at ht
            have h1t : 1 - t ≠ 0 := by linarith [ht.2, hε.1]
            have ht1 : t - 1 ≠ 0 := by linarith [ht.2, hε.1]
            have hlin : HasDerivAt (fun s : ℝ ↦ (1 : ℝ) - s) (-1) t :=
              (hasDerivAt_id t).const_sub 1
            exact ((Real.hasDerivAt_log h1t).comp t hlin).congr_deriv (by
              have hinv : (1 - t)⁻¹ * (-1) = (t - 1)⁻¹ := by
                field_simp [h1t, ht1]
                ring
              exact hinv))
          hsub1_int
        simpa using hFTC
      have hsub2_val : ∫ t in (1 + ε)..x, (t - 1)⁻¹ = Real.log (x - 1) - Real.log ε := by
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun t : ℝ ↦ Real.log (t - 1)) (f' := fun t : ℝ ↦ (t - 1)⁻¹)
          (fun t ht ↦ by
            rw [uIcc_of_le hεx.le] at ht
            have ht1 : t - 1 ≠ 0 := by linarith [ht.1, hε.1]
            have hlin : HasDerivAt (fun s : ℝ ↦ s - (1 : ℝ)) 1 t :=
              (hasDerivAt_id t).sub_const 1
            exact (hlin.log ht1).congr_deriv (by rw [one_div]))
          hsub2_int
        simpa using hFTC
      have hcongr1 : ∫ t in (0 : ℝ)..(1 - ε), g t =
          ∫ t in (0 : ℝ)..(1 - ε), ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
        refine intervalIntegral.integral_congr_ae ?_
        have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := ae_iff.mpr (by simp)
        filter_upwards [hne0] with t ht0 ht_mem
        rw [uIoc_of_le (by linarith : (0 : ℝ) ≤ 1 - ε)] at ht_mem
        have ht1 : t ≠ 1 := by linarith [ht_mem.2, hε.1]
        simp [g, ht0, ht1]
      have hcongr2 : ∫ t in (1 + ε)..x, g t =
          ∫ t in (1 + ε)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
        refine intervalIntegral.integral_congr fun t ht_mem ↦ ?_
        rw [uIcc_of_le hεx.le] at ht_mem
        have ht0 : t ≠ 0 := by linarith [ht_mem.1, hε.1]
        have ht1 : t ≠ 1 := by linarith [ht_mem.1, hε.1]
        simp [g, ht0, ht1]
      have hlog1 : IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume 0 (1 - ε) :=
        intervalIntegrable_inv_log_of_Ico (sub_nonneg.mpr hε1.le) (by linarith [hε.1])
      have hlog2 : IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume (1 + ε) x := by
        simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith [hε.1]) hx_gt
      rw [hcongr1, hcongr2, intervalIntegral.integral_sub hlog1 hsub1_int,
        intervalIntegral.integral_sub hlog2 hsub2_int, hsub1_val, hsub2_val]
      ring
    have heq_g : ∫ t in (0 : ℝ)..x, g t = unoffsetLogIntegral x - Real.log (x - 1) :=
      tendsto_nhds_unique hmid_tend hrhs_tend
    have heq_main : ∫ t in (0 : ℝ)..x, g t =
        ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := ae_iff.mpr (by simp)
      have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := ae_iff.mpr (by simp)
      filter_upwards [hne0.and hne1] with t ⟨ht0, ht1⟩ _
      simp [g, ht0, ht1]
    rw [hlog_abs, ← heq_main]
    linarith

/-- As `u → 0⁺`, `(log (1 + u))⁻¹ + (log (1 - u))⁻¹ → 1`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsGT_zero :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ - u⁻¹) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    have hmap : Tendsto (fun u : ℝ ↦ (1 : ℝ) + u) (𝓝[>] 0) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun u : ℝ ↦ (1 : ℝ) + u) 0 := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact (by linarith [mem_Ioi.mp hu] : (1 : ℝ) + u ≠ 1)
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp hmap).congr fun u ↦ by
      simp
  have h2 : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹ + u⁻¹) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    have hmap : Tendsto (fun u : ℝ ↦ (1 : ℝ) - u) (𝓝[>] 0) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun u : ℝ ↦ (1 : ℝ) - u) 0 := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact (by linarith [mem_Ioi.mp hu] : (1 : ℝ) - u ≠ 1)
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp hmap).congr fun u ↦ by
      simp only [Function.comp_def]
      ring
  have hadd := h1.add h2
  norm_num at hadd
  refine hadd.congr fun u ↦ by ring

/-- As `u → 1⁻`, `(log (1 + u))⁻¹ + (log (1 - u))⁻¹ → (log 2)⁻¹`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsLT_one :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹)
      (𝓝[<] 1) (𝓝 (Real.log 2)⁻¹) := by
  have h1 : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) (𝓝[<] 1) (𝓝 (Real.log 2)⁻¹) := by
    have hlog2 : Real.log (1 + (1 : ℝ)) ≠ 0 :=
      (Real.log_pos (by norm_num : (1 : ℝ) < 1 + 1)).ne'
    have hc : ContinuousAt (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) 1 := by
      fun_prop (disch := first | norm_num | exact hlog2)
    simpa [show (1 : ℝ) + 1 = 2 by norm_num] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) (𝓝[<] 1) (𝓝 0) := by
    have hmap : Tendsto (fun u : ℝ ↦ (1 : ℝ) - u) (𝓝[<] 1) (𝓝 0) := by
      have hc : ContinuousAt (fun u : ℝ ↦ (1 : ℝ) - u) 1 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hcomp : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) (𝓝[<] 1) (𝓝 (Real.log 0)⁻¹) :=
      Real.continuousAt_inv_log_zero.tendsto.comp hmap
    simpa [Real.log_zero] using hcomp
  simpa using h1.add h2

/-- Continuous extension of `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` on `[0, 1]`. -/
private theorem continuousOn_inv_log_one_add_add_inv_log_one_sub_ext :
    ContinuousOn (fun u : ℝ ↦ if u = 0 then 1 else if u = 1 then (Real.log 2)⁻¹ else
      (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) (Icc 0 1) := by
  intro u hu
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt]
    simp only [↓reduceIte]
    have hsub_set : Icc (0 : ℝ) 1 \ {0} ⊆ Ioi 0 :=
      fun v hv ↦ lt_of_le_of_ne hv.1.1 (Ne.symm hv.2)
    have hsub := tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsGT_zero.mono_left
      (nhdsWithin_mono _ hsub_set)
    refine hsub.congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds zero_lt_one)] with v hv hv1
    have hv0 : v ≠ 0 := hv.2
    simp [hv0, hv1.ne]
  · rcases eq_or_ne u 1 with rfl | hu1
    · rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt]
      simp only [one_ne_zero, ↓reduceIte]
      have hsub_set : Icc (0 : ℝ) 1 \ {1} ⊆ Iio 1 :=
        fun v hv ↦ lt_of_le_of_ne hv.1.2 hv.2
      have hsub := tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsLT_one.mono_left
        (nhdsWithin_mono _ hsub_set)
      refine hsub.congr' ?_
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_ne_nhds one_ne_zero)] with v hv1 hv0
      have hv1' : v ≠ 1 := hv1.2
      simp [hv0, hv1']
    · have hu_pos : 0 < u := lt_of_le_of_ne hu.1 hu0.symm
      have hu_lt : u < 1 := lt_of_le_of_ne hu.2 hu1
      have h1p : Real.log (1 + u) ≠ 0 := (Real.log_pos (by linarith)).ne'
      have h1m : Real.log (1 - u) ≠ 0 := (Real.log_neg (by linarith) (by linarith)).ne
      have hc : ContinuousAt (fun v : ℝ ↦ (Real.log (1 + v))⁻¹ + (Real.log (1 - v))⁻¹) u := by
        fun_prop (disch := first | linarith | exact h1p | exact h1m)
      refine (hc.congr ?_).continuousWithinAt
      filter_upwards [eventually_ne_nhds hu0, eventually_ne_nhds hu1] with v hv0 hv1
      simp [hv0, hv1]

/-- `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_inv_log_one_add_add_inv_log_one_sub :
    IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) volume 0 1 := by
  refine (continuousOn_inv_log_one_add_add_inv_log_one_sub_ext.intervalIntegrable_of_Icc
    zero_le_one).congr_ae ?_
  have hne0 : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
  have hne1 : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := ae_iff.mpr (by simp)
  filter_upwards [ae_restrict_of_ae (hne0.and hne1)] with u ⟨hu0, hu1⟩
  simp [hu0, hu1]

/-- Concavity inequality: `-log (1 - v) ≤ 4 * log (4 / 3) * v` for all `v ∈ [0, 1 / 4]`. -/
private theorem neg_log_one_sub_le_mul {v : ℝ} (hv0 : 0 ≤ v) (hv4 : v ≤ 1 / 4) :
    -Real.log (1 - v) ≤ 4 * Real.log (4 / 3) * v := by
  let φ (t : ℝ) : ℝ := 4 * Real.log (4 / 3) * t + Real.log (1 - t)
  by_contra hneg
  push Not at hneg
  have hv_pos : 0 < v := by
    rcases hv0.eq_or_lt with rfl | h
    · norm_num at hneg
    · exact h
  have hv_lt4 : v < 1 / 4 := by
    rcases hv4.eq_or_lt with rfl | h
    · have hlog : -Real.log (1 - (1 / 4 : ℝ)) = Real.log (4 / 3) := by
        rw [show (1 : ℝ) - 1 / 4 = (4 / 3)⁻¹ by norm_num, Real.log_inv, neg_neg]
      linarith
    · exact h
  have hφ_lt : φ v < 0 := by simp only [φ]; linarith
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hφ4 : φ (1 / 4) = 0 := by
    simp only [φ]
    rw [show (1 : ℝ) - 1 / 4 = (4 / 3)⁻¹ by norm_num, Real.log_inv]
    ring
  have hderiv : ∀ t ∈ Icc (0 : ℝ) (1 / 4),
      HasDerivAt φ (4 * Real.log (4 / 3) - (1 - t)⁻¹) t := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ ↦ (1 : ℝ) - s) (-1) t := (hasDerivAt_id t).const_sub 1
    have hlog : HasDerivAt (fun s : ℝ ↦ Real.log (1 - s)) (-(1 - t)⁻¹) t := by
      exact ((Real.hasDerivAt_log (by linarith [ht.2] : (1 : ℝ) - t ≠ 0)).comp t hlin).congr_deriv
        (by ring)
    have hmul : HasDerivAt (fun s : ℝ ↦ 4 * Real.log (4 / 3) * s) (4 * Real.log (4 / 3)) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.log (4 / 3))
    exact (hmul.add hlog).congr_deriv (by ring)
  have hcont : ContinuousOn φ (Icc 0 (1 / 4)) := fun t ht ↦
    (hderiv t ht).continuousAt.continuousWithinAt
  obtain ⟨a, ha, ha_eq⟩ := exists_hasDerivAt_eq_slope φ (fun t ↦ 4 * Real.log (4 / 3) - (1 - t)⁻¹)
    hv_pos (hcont.mono (Icc_subset_Icc_right hv4)) fun t ht ↦
      hderiv t ⟨ht.1.le, ht.2.le.trans hv4⟩
  obtain ⟨b, hb, hb_eq⟩ := exists_hasDerivAt_eq_slope φ (fun t ↦ 4 * Real.log (4 / 3) - (1 - t)⁻¹)
    hv_lt4 (hcont.mono (Icc_subset_Icc_left hv0)) fun t ht ↦
      hderiv t ⟨hv0.trans ht.1.le, ht.2.le⟩
  have ha_neg : 4 * Real.log (4 / 3) - (1 - a)⁻¹ < 0 := by
    rw [ha_eq, hφ0, sub_zero]
    exact div_neg_of_neg_of_pos hφ_lt (sub_pos.mpr hv_pos)
  have hb_pos : 0 < 4 * Real.log (4 / 3) - (1 - b)⁻¹ := by
    rw [hb_eq, hφ4, zero_sub]
    exact div_pos (neg_pos.mpr hφ_lt) (sub_pos.mpr hv_lt4)
  have hab : a < b := ha.2.trans hb.1
  have h1b_pos : 0 < 1 - b := by linarith [hb.2]
  have hinv_lt : (1 - a)⁻¹ < (1 - b)⁻¹ := inv_strictAnti₀ h1b_pos (by linarith)
  linarith

/-- Uniform bound on `(0, 1 / 2]` for the symmetric integrand:
`|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3`. -/
theorem abs_inv_log_one_add_add_inv_log_one_sub_le {u : ℝ} (hu₀ : 0 < u) (hu₂ : u ≤ 1 / 2) :
    |(Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹| ≤ 16 * Real.log (4 / 3) / 3 := by
  have h1pu : 1 < 1 + u := by linarith
  have h1mu_pos : 0 < 1 - u := by linarith
  have hlogp : 0 < Real.log (1 + u) := Real.log_pos h1pu
  have hlogm : 0 < -Real.log (1 - u) := neg_pos.mpr (Real.log_neg h1mu_pos (by linarith))
  have hnum_eq : -Real.log (1 - u) - Real.log (1 + u) = -Real.log (1 - u ^ 2) := by
    have hmul : (1 - u) * (1 + u) = 1 - u ^ 2 := by ring
    rw [← neg_add', ← Real.log_mul h1mu_pos.ne' (zero_lt_one.trans h1pu).ne', hmul]
  have h1mu2_pos : 0 < 1 - u ^ 2 := by nlinarith
  have hnum_nn : 0 ≤ -Real.log (1 - u ^ 2) :=
    neg_nonneg.mpr (Real.log_nonpos h1mu2_pos.le (by nlinarith))
  have hlogp_lb : (3 / 4 : ℝ) * u ≤ Real.log (1 + u) := by
    let ψ (t : ℝ) : ℝ := Real.log (1 + t) - (t - t ^ 2 / 2)
    have hderiv : ∀ t ∈ Icc (0 : ℝ) u, HasDerivAt ψ ((1 + t)⁻¹ - (1 - t)) t := by
      intro t ht
      have hlin : HasDerivAt (fun s : ℝ ↦ (1 : ℝ) + s) 1 t := (hasDerivAt_id t).const_add 1
      have h1 : HasDerivAt (fun s : ℝ ↦ Real.log (1 + s)) (1 + t)⁻¹ t :=
        (hlin.log (by linarith [ht.1] : (1 : ℝ) + t ≠ 0)).congr_deriv (by rw [one_div])
      have h2 : HasDerivAt (fun s : ℝ ↦ s - s ^ 2 / 2) (1 - t) t := by
        simpa using (hasDerivAt_id t).fun_sub ((hasDerivAt_pow 2 t).div_const 2)
      exact h1.fun_sub h2
    have hψ_mono : MonotoneOn ψ (Icc 0 u) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
        (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
        (fun t ht ↦ (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
        fun t ht ↦ ?_
      rw [interior_Icc] at ht
      rw [(hderiv t ⟨ht.1.le, ht.2.le⟩).deriv]
      have hpos1 : 0 < 1 + t := by linarith [ht.1]
      rw [sub_nonneg, inv_eq_one_div, le_div_iff₀ hpos1]
      nlinarith [ht.1]
    have hψ0 : ψ 0 ≤ ψ u := hψ_mono (left_mem_Icc.mpr hu₀.le) (right_mem_Icc.mpr hu₀.le) hu₀.le
    have hψ_val : ψ 0 = 0 := by simp [ψ]
    rw [hψ_val] at hψ0
    dsimp only [ψ] at hψ0
    nlinarith
  have hlogm_lb : u ≤ -Real.log (1 - u) := by
    have hle := Real.log_le_sub_one_of_pos h1mu_pos
    linarith
  have hnum_ub : -Real.log (1 - u ^ 2) ≤ 4 * Real.log (4 / 3) * u ^ 2 :=
    neg_log_one_sub_le_mul (sq_nonneg u) (by nlinarith)
  have hden_lb : (3 / 4 : ℝ) * u ^ 2 ≤ Real.log (1 + u) * (-Real.log (1 - u)) := by
    calc (3 / 4 : ℝ) * u ^ 2 = ((3 / 4 : ℝ) * u) * u := by ring
      _ ≤ Real.log (1 + u) * (-Real.log (1 - u)) :=
          mul_le_mul hlogp_lb hlogm_lb hu₀.le hlogp.le
  have hden_pos : 0 < Real.log (1 + u) * (-Real.log (1 - u)) := mul_pos hlogp hlogm
  have hlogm_ne : Real.log (1 - u) ≠ 0 := neg_ne_zero.mp hlogm.ne'
  have hid : (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ =
      (-Real.log (1 - u ^ 2)) / (Real.log (1 + u) * (-Real.log (1 - u))) := by
    rw [← hnum_eq]
    field_simp [hlogp.ne', hlogm_ne]
    ring
  rw [hid, abs_of_nonneg (div_nonneg hnum_nn hden_pos.le)]
  calc (-Real.log (1 - u ^ 2)) / (Real.log (1 + u) * (-Real.log (1 - u)))
      ≤ (4 * Real.log (4 / 3) * u ^ 2) / ((3 / 4 : ℝ) * u ^ 2) := by
          gcongr
    _ = 16 * Real.log (4 / 3) / 3 := by
          have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu₀.ne'
          field_simp [hu2]
          norm_num

/-- **Symmetric integral for `li 2`**:
`li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)`. -/
theorem unoffsetLogIntegral_two_eq_integral :
    unoffsetLogIntegral 2 =
      ∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) := by
  let h (u : ℝ) : ℝ :=
    if u = 0 then 1 else if u = 1 then (Real.log 2)⁻¹ else
      (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹
  have hh_int_on : IntegrableOn h (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_inv_log_one_add_add_inv_log_one_sub_ext.integrableOn_Icc
  have hprim : ContinuousOn (fun a : ℝ ↦ ∫ u in a..1, h u) (Icc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      intervalIntegral.continuousOn_primitive_interval_left hh_int_on
  have htend_rhs : Tendsto (fun ε : ℝ ↦ ∫ u in ε..1, h u) (𝓝[>] 0)
      (𝓝 (∫ u in (0 : ℝ)..1, h u)) := by
    refine (hprim 0 ⟨le_rfl, zero_le_one⟩).tendsto.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact ⟨hε.1.le, hε.2.le⟩
  have heq_pv : Tendsto (fun ε : ℝ ↦ ∫ u in ε..1, h u) (𝓝[>] 0)
      (𝓝 (unoffsetLogIntegral 2)) := by
    refine (tendsto_principalValue_inv_log one_lt_two).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    have hleft : ∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹ = ∫ u in ε..1, (Real.log (1 - u))⁻¹ := by
      have hcomp := intervalIntegral.integral_comp_sub_left
        (f := fun t : ℝ ↦ (Real.log t)⁻¹) (a := ε) (b := 1) 1
      simpa using hcomp.symm
    have hright : ∫ t in (1 + ε)..2, (Real.log t)⁻¹ = ∫ u in ε..1, (Real.log (1 + u))⁻¹ := by
      have hcomp := intervalIntegral.integral_comp_add_left
        (f := fun t : ℝ ↦ (Real.log t)⁻¹) (a := ε) (b := 1) 1
      simp_rw [add_comm _ (1 : ℝ)] at hcomp
      simpa [show (1 : ℝ) + 1 = 2 by norm_num] using hcomp.symm
    have hi1 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) volume ε 1 := by
      refine ContinuousOn.intervalIntegrable_of_Icc hε.2.le fun u hu ↦ ?_
      have h1u : 1 + u ≠ 0 := by linarith [hu.1, hε.1]
      have hlog : Real.log (1 + u) ≠ 0 := (Real.log_pos (by linarith [hu.1, hε.1])).ne'
      have hc : ContinuousAt (fun v : ℝ ↦ 1 + v) u := by fun_prop
      exact ((Real.continuousAt_log h1u).comp hc |>.inv₀ hlog).continuousWithinAt
    have hi2 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) volume ε 1 := by
      refine ContinuousOn.intervalIntegrable_of_Icc hε.2.le fun u hu ↦ ?_
      rcases hu.2.eq_or_lt with rfl | hu1
      · have hc : ContinuousAt (fun v : ℝ ↦ 1 - v) 1 := by fun_prop
        exact (Real.continuousAt_inv_log_zero.comp_of_eq hc (sub_self 1)).continuousWithinAt
      · have hlog : Real.log (1 - u) ≠ 0 :=
          (Real.log_neg (sub_pos.mpr hu1) (by linarith [hu.1, hε.1])).ne
        have hc : ContinuousAt (fun v : ℝ ↦ 1 - v) u := by fun_prop
        exact ((Real.continuousAt_log (sub_pos.mpr hu1).ne').comp hc |>.inv₀
          hlog).continuousWithinAt
    have hcongr : ∫ u in ε..1, h u =
        ∫ u in ε..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hne1 : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := ae_iff.mpr (by simp)
      filter_upwards [hne1] with u hu1 hum
      rw [uIoc_of_le hε.2.le] at hum
      have hu0 : u ≠ 0 := (hε.1.trans hum.1).ne'
      simp [h, hu0, hu1]
    rw [hleft, hright, hcongr, intervalIntegral.integral_add hi1 hi2]
    ring
  have heq_main : ∫ u in (0 : ℝ)..1, h u =
      ∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne0 : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
    have hne1 : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := ae_iff.mpr (by simp)
    filter_upwards [hne0.and hne1] with u ⟨hu0, hu1⟩ _
    simp [h, hu0, hu1]
  rw [← heq_main]
  exact (tendsto_nhds_unique htend_rhs heq_pv).symm

end TauCeti.Real
