/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Log.InvLog

/-!
# Principal-value and regularized integral representations of `li`

This file proves the integral representations of the unoffset logarithmic integral
`TauCeti.Real.li`:

* On `(0, 1)`, `li x = ∫ t in 0..x, (log t)⁻¹` as an ordinary Lebesgue interval integral.
* On `(1, ∞)`, `li x` is the Cauchy principal value
  `lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹)`.
* In exponential-integral coordinates `t = e^u`, `∫ u in Iic y, exp u / u = li (exp y)` for
  `y < 0`, and `∫ u in (-ε⁻¹)..(-ε), exp u / u + ∫ u in ε..y, exp u / u → li (exp y)` as `ε → 0⁺`
  for `y > 0`.
* Subtracting `(t - 1)⁻¹` cancels the pole at `t = 1` and gives the absolutely convergent
  representation `li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)` for all `x > 0`,
  `x ≠ 1`.
* Folding around `t = 1` gives the symmetric integral
  `li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)` together with the boundary limits
  and explicit bound `|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3` on `(0, 1 / 2]`.

## Main declarations

* `TauCeti.Real.li_eq_integral_inv_log` — ordinary integral on `(0, 1)`.
* `TauCeti.Real.tendsto_li_one_add_sub_one_sub` and
  `TauCeti.Real.tendsto_integral_inv_log_principalValue` — Cauchy principal value on `(1, ∞)`.
* `TauCeti.Real.hasDerivAt_li_exp`, `TauCeti.Real.integral_Iic_exp_div_eq_li_exp`, and
  `TauCeti.Real.tendsto_integral_exp_div_principalValue` — exponential-integral forms.
* `TauCeti.Real.li_eq_log_abs_sub_one_add_integral` — absolutely convergent regularized integral.
* `TauCeti.Real.li_two_eq_integral_symm` and
  `TauCeti.Real.abs_inv_log_one_add_add_inv_log_one_sub_le` — symmetric integral for `li 2` and
  its explicit bound on `(0, 1 / 2]`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2 (Exponential,
  Logarithmic, Sine, and Cosine Integrals).
* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
-/

public section

namespace TauCeti.Real

open Filter MeasureTheory Set
open scoped Topology Nat

/-! ### Principal value and exponential-integral representations -/

/-- `(log t)⁻¹` is interval integrable on `[0, x]` whenever `0 ≤ x < 1`. -/
theorem intervalIntegrable_inv_log_of_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume 0 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
  rw [uIcc_of_le hx0] at ht
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · exact Real.continuousAt_inv_log_zero.continuousWithinAt
  · have hlt : Real.log t ≠ 0 := (Real.log_neg ht0 (ht.2.trans_lt hx1)).ne
    exact ((Real.continuousAt_log ht0.ne').inv₀ hlt).continuousWithinAt

/-- On `(0, 1)`, the unoffset logarithmic integral is the ordinary integral
`li x = ∫ t in 0..x, (log t)⁻¹`. -/
theorem li_eq_integral_inv_log {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    li x = ∫ t in (0 : ℝ)..x, (Real.log t)⁻¹ := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume 0 x :=
    intervalIntegrable_inv_log_of_lt_one hx0.le hx1
  have hi_uIcc : IntegrableOn (fun t : ℝ ↦ (Real.log t)⁻¹) (uIcc 0 x) volume := by
    rw [uIcc_of_le hx0.le]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx0.le).mp hi
  have h1 : Tendsto (fun ε : ℝ ↦ li x - li ε) (𝓝[>] 0) (𝓝 (li x)) := by
    simpa using tendsto_const_nhds.sub tendsto_li_nhdsGT_zero
  have h2 : Tendsto (fun ε : ℝ ↦ ∫ t in ε..x, (Real.log t)⁻¹) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..x, (Real.log t)⁻¹)) := by
    have hcont := intervalIntegral.continuousOn_primitive_interval_left hi_uIcc
    rw [uIcc_of_le hx0.le] at hcont
    have hlim := (hcont 0 ⟨le_rfl, hx0.le⟩).tendsto.mono_left
      (nhdsWithin_mono 0 fun t ht ↦ ⟨le_of_lt ht.1, le_of_lt ht.2⟩ : 𝓝[Ioo 0 x] 0 ≤ 𝓝[Icc 0 x] 0)
    rwa [nhdsWithin_Ioo_eq_nhdsGT hx0] at hlim
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hx0] with ε ⟨hε0, hεx⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ by
      rw [uIcc_of_le hεx.le] at ht
      exact hasDerivAt_li (hε0.trans_le ht.1) (ht.2.trans_lt hx1).ne)
    (hi.mono_set (by
      rw [uIcc_of_le hεx.le, uIcc_of_le hx0.le]
      exact Icc_subset_Icc hε0.le le_rfl))

/-- Symmetric cancellation of the logarithmic pole of `li` at `1`:
`li (1 + ε) - li (1 - ε) → 0` as `ε → 0⁺`. -/
theorem tendsto_li_one_add_sub_one_sub :
    Tendsto (fun ε : ℝ ↦ li (1 + ε) - li (1 - ε)) (𝓝[>] 0) (𝓝 0) := by
  have hlog_ratio : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε) / (-Real.log (1 - ε))) (𝓝[>] 0)
      (𝓝 1) := by
    have hp : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε) / ε) (𝓝[>] 0) (𝓝 1) := by
      have hd : HasDerivAt (fun t : ℝ ↦ Real.log (1 + t)) 1 0 := by
        simpa using ((hasDerivAt_id' (0 : ℝ)).const_add (1 : ℝ)).log (by norm_num)
      exact (hd.tendsto_slope_zero.congr fun ε ↦ by simp [Real.log_one, div_eq_inv_mul]).mono_left
        (nhdsWithin_mono 0 fun _ ht ↦ ne_of_gt ht)
    have hm : Tendsto (fun ε : ℝ ↦ -Real.log (1 - ε) / ε) (𝓝[>] 0) (𝓝 1) := by
      have hd : HasDerivAt (fun t : ℝ ↦ -Real.log (1 - t)) 1 0 := by
        simpa using (((hasDerivAt_id' (0 : ℝ)).const_sub (1 : ℝ)).log (by norm_num)).fun_neg
      exact (hd.tendsto_slope_zero.congr fun ε ↦ by simp [Real.log_one, div_eq_inv_mul]).mono_left
        (nhdsWithin_mono 0 fun _ ht ↦ ne_of_gt ht)
    have hdiv : Tendsto
        (fun ε : ℝ ↦ (Real.log (1 + ε) / ε) / (-Real.log (1 - ε) / ε)) (𝓝[>] 0) (𝓝 1) := by
      simpa [Pi.div_def] using hp.div hm one_ne_zero
    refine hdiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    field_simp [hε.ne']
  have hlog_diff : Tendsto (fun ε : ℝ ↦ Real.log (Real.log (1 + ε)) -
      Real.log (Real.log (1 - ε))) (𝓝[>] 0) (𝓝 0) := by
    have hcomp := (Real.continuousAt_log one_ne_zero).tendsto.comp hlog_ratio
    rw [Real.log_one] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε ⟨hε0, hε1⟩
    have h1 : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    have h2 : 0 < -Real.log (1 - ε) := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
    dsimp only [Function.comp_apply]
    rw [Real.log_div h1.ne' h2.ne', Real.log_neg_eq_log]
  have hser_diff : Tendsto
      (fun ε : ℝ ↦
        (∑' n : ℕ, Real.log (1 + ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
        (∑' n : ℕ, Real.log (1 - ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))))
      (𝓝[>] 0) (𝓝 0) := by
    have hc1 : ContinuousAt (fun ε : ℝ ↦
        ∑' n : ℕ, Real.log (1 + ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) 0 :=
      continuous_tsum_pow_div_mul_factorial.continuousAt.comp
        ((Real.continuousAt_log (by norm_num)).comp (by fun_prop))
    have hc2 : ContinuousAt (fun ε : ℝ ↦
        ∑' n : ℕ, Real.log (1 - ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) 0 :=
      continuous_tsum_pow_div_mul_factorial.continuousAt.comp
        ((Real.continuousAt_log (by norm_num)).comp (by fun_prop))
    simpa [Pi.sub_def] using (hc1.sub hc2).tendsto.mono_left nhdsWithin_le_nhds
  have hsum := hlog_diff.add hser_diff
  rw [add_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun ε ↦ ?_)
  dsimp only
  rw [li_def, li_def]
  ring

/-- **Cauchy principal value representation of `li` on `(1, ∞)`**:
`∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹ → li x` as `ε → 0⁺`. -/
theorem tendsto_integral_inv_log_principalValue {x : ℝ} (hx : 1 < x) :
    Tendsto
      (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) +
        ∫ t in (1 + ε)..x, (Real.log t)⁻¹)
      (𝓝[>] 0) (𝓝 (li x)) := by
  have hlim : Tendsto (fun ε : ℝ ↦ li x - (li (1 + ε) - li (1 - ε))) (𝓝[>] 0) (𝓝 (li x)) := by
    simpa using tendsto_const_nhds.sub tendsto_li_one_add_sub_one_sub
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (sub_pos.mpr hx))] with ε ⟨hε0, hεm⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
  have hεx : 1 + ε < x := by linarith [lt_of_lt_of_le hεm (min_le_right _ _)]
  rw [← li_eq_integral_inv_log (by linarith) (by linarith)]
  have hFTC : (∫ t in (1 + ε)..x, (Real.log t)⁻¹) = li x - li (1 + ε) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ by
        rw [uIcc_of_le hεx.le] at ht
        exact hasDerivAt_li (by linarith [ht.1]) (by linarith [ht.1]))
      (by simpa [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith) hx)
  rw [hFTC]
  ring

/-- In exponential coordinates, `t ↦ li (exp t)` has derivative `exp u / u` at every `u ≠ 0`. -/
theorem hasDerivAt_li_exp {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ li (Real.exp t)) (Real.exp u / u) u := by
  have hne : Real.exp u ≠ 1 := fun h ↦
    hu (by simpa [Real.log_exp] using congrArg Real.log h)
  have h := (hasDerivAt_li (Real.exp_pos u) hne).comp u (Real.hasDerivAt_exp u)
  simpa only [Function.comp_def, Real.log_exp, div_eq_mul_inv, mul_comm] using h

/-- `u ↦ exp u / u` is integrable on `(-∞, y]` whenever `y < 0`. -/
theorem integrableOn_exp_div_Iic {y : ℝ} (hy : y < 0) :
    IntegrableOn (fun u : ℝ ↦ Real.exp u / u) (Iic y) := by
  have hdom : IntegrableOn (fun u : ℝ ↦ Real.exp u / (-y)) (Iic y) :=
    (integrableOn_exp_Iic y).div_const (-y)
  refine Integrable.mono' hdom
    (Real.continuous_exp.measurable.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with u (hu : u ≤ y)
  have hu0 : u < 0 := hu.trans_lt hy
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_neg hu0]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (neg_pos.mpr hy) (neg_le_neg hu)

/-- Exponential-integral form of `li` on `(0, 1)`: for `y < 0`,
`∫ u in Iic y, exp u / u = li (exp y)`. -/
theorem integral_Iic_exp_div_eq_li_exp {y : ℝ} (hy : y < 0) :
    (∫ u in Iic y, Real.exp u / u) = li (Real.exp y) := by
  have hlim : Tendsto (fun t : ℝ ↦ li (Real.exp t)) atBot (𝓝 0) :=
    tendsto_li_nhdsGT_zero.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      Real.tendsto_exp_atBot (Eventually.of_forall Real.exp_pos))
  simpa using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun u hu ↦ hasDerivAt_li_exp (lt_of_le_of_lt hu hy).ne)
    (integrableOn_exp_div_Iic hy) hlim

/-- **Exponential-integral principal value representation of `li` on `(1, ∞)`**: for `y > 0`,
`∫ u in (-ε⁻¹)..(-ε), exp u / u + ∫ u in ε..y, exp u / u → li (exp y)` as `ε → 0⁺`. -/
theorem tendsto_integral_exp_div_principalValue {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun ε : ℝ ↦ (∫ u in (-ε⁻¹)..(-ε), Real.exp u / u) + ∫ u in ε..y, Real.exp u / u)
      (𝓝[>] 0) (𝓝 (li (Real.exp y))) := by
  have hneg_inv : Tendsto (fun ε : ℝ ↦ li (Real.exp (-ε⁻¹))) (𝓝[>] 0) (𝓝 0) :=
    tendsto_li_nhdsGT_zero.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero))
      (Eventually.of_forall fun _ ↦ Real.exp_pos _))
  have hsymm : Tendsto (fun ε : ℝ ↦ li (Real.exp (-ε)) - li (Real.exp ε)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt
        (fun ε : ℝ ↦
          (∑' n : ℕ, (-ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
          (∑' n : ℕ, ε ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))) 0 :=
      (continuous_tsum_pow_div_mul_factorial.comp continuous_neg).continuousAt.sub
        continuous_tsum_pow_div_mul_factorial.continuousAt
    have h0 : Tendsto
        (fun ε : ℝ ↦
          (∑' n : ℕ, (-ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
          (∑' n : ℕ, ε ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    refine h0.congr' (Eventually.of_forall fun ε ↦ ?_)
    dsimp only
    rw [li_def, li_def, Real.log_exp, Real.log_exp, Real.log_neg_eq_log]
    ring
  have hlim : Tendsto
      (fun ε : ℝ ↦ li (Real.exp y) - li (Real.exp (-ε⁻¹)) + (li (Real.exp (-ε)) - li (Real.exp ε)))
      (𝓝[>] 0) (𝓝 (li (Real.exp y))) := by
    simpa using (tendsto_const_nhds.sub hneg_inv).add hsymm
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hy)] with ε ⟨hε0, hεm⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
  have hεy : ε < y := lt_of_lt_of_le hεm (min_le_right _ _)
  have hle_neg : -ε⁻¹ ≤ -ε := by linarith [(one_le_inv₀ hε0).mpr hε1.le]
  have h1 : (∫ u in (-ε⁻¹)..(-ε), Real.exp u / u) =
      li (Real.exp (-ε)) - li (Real.exp (-ε⁻¹)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ li (Real.exp t))
      (fun u hu ↦ by
        rw [uIcc_of_le hle_neg] at hu
        exact hasDerivAt_li_exp (lt_of_le_of_lt hu.2 (neg_lt_zero.mpr hε0)).ne)
      (ContinuousOn.intervalIntegrable fun u hu ↦ by
        rw [uIcc_of_le hle_neg] at hu
        have hu0 : u ≠ 0 := (lt_of_le_of_lt hu.2 (neg_lt_zero.mpr hε0)).ne
        fun_prop (disch := assumption))
  have h2 : (∫ u in ε..y, Real.exp u / u) = li (Real.exp y) - li (Real.exp ε) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ li (Real.exp t))
      (fun u hu ↦ by
        rw [uIcc_of_le hεy.le] at hu
        exact hasDerivAt_li_exp (lt_of_lt_of_le hε0 hu.1).ne')
      (ContinuousOn.intervalIntegrable fun u hu ↦ by
        rw [uIcc_of_le hεy.le] at hu
        have hu0 : u ≠ 0 := (lt_of_lt_of_le hε0 hu.1).ne'
        fun_prop (disch := assumption))
  rw [h1, h2]
  ring

/-! ### Absolutely convergent integral representations -/

/-- `(log t)⁻¹ - (t - 1)⁻¹ → 1` as `t → 0⁺`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsGT_zero :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) 0 :=
    Real.continuousAt_inv_log_zero.sub (by fun_prop (disch := norm_num))
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- `(log t)⁻¹ - (t - 1)⁻¹ → 1 / 2` as `t → 1`, `t ≠ 1`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsNE_one :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
  -- Express as `((t - 1 - log t) / (t - 1)²) / (log t / (t - 1))`.
  have hnum : Tendsto (fun t : ℝ ↦ (t - 1 - Real.log t) / (t - 1) ^ 2) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
    have hbound : ∀ᶠ t in 𝓝[≠] (1 : ℝ),
        |(t - 1 - Real.log t) / (t - 1) ^ 2 - 1 / 2| ≤ |t - 1| / (1 - |t - 1|) := by
      have hnhds : Ioo (0 : ℝ) 2 ∈ 𝓝 (1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with t ⟨ht0, ht2⟩ ht1
      have ht1' : t ≠ 1 := ht1
      set u : ℝ := 1 - t
      have hu1 : |u| < 1 := by rw [abs_lt]; constructor <;> linarith
      have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1')
      have htaylor := Real.abs_log_sub_add_sum_range_le hu1 2
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        Nat.cast_zero, Nat.cast_one, pow_one, div_one] at htaylor
      have h1u : 1 - u = t := by ring
      rw [h1u] at htaylor
      have hrewrite : (t - 1 - Real.log t) / (t - 1) ^ 2 - 1 / 2 =
          -(u + u ^ 2 / 2 + Real.log t) / u ^ 2 := by
        have hsq : (t - 1) ^ 2 = u ^ 2 := by ring
        rw [hsq]
        field_simp [hu0]
        ring
      have habs_u : |u| = |t - 1| := by
        have hneg : u = -(t - 1) := by ring
        rw [hneg, abs_neg]
      rw [hrewrite, abs_div, abs_neg, abs_pow, habs_u]
      have hpos : 0 < |t - 1| ^ 2 := sq_pos_of_ne_zero (abs_ne_zero.mpr (sub_ne_zero.mpr ht1'))
      rw [div_le_iff₀ hpos]
      calc |u + u ^ 2 / 2 + Real.log t|
          ≤ |u| ^ 3 / (1 - |u|) := by
            have htwo : (1 : ℝ) + 1 = 2 := by norm_num
            simpa [htwo] using htaylor
        _ = |t - 1| / (1 - |t - 1|) * |t - 1| ^ 2 := by rw [habs_u]; ring
    have hzero : Tendsto (fun t : ℝ ↦ |t - 1| / (1 - |t - 1|)) (𝓝[≠] 1) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ ↦ |t - 1| / (1 - |t - 1|)) 1 :=
        (continuous_abs.comp (continuous_sub_right 1)).continuousAt.div
          (continuous_const.sub (continuous_abs.comp (continuous_sub_right 1))).continuousAt
          (by norm_num)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    rw [← tendsto_sub_nhds_zero_iff]
    exact squeeze_zero_norm' hbound hzero
  have hden : Tendsto (fun t : ℝ ↦ Real.log t / (t - 1)) (𝓝[≠] 1) (𝓝 1) := by
    have hd : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log one_ne_zero
    exact hd.tendsto_slope.congr fun t ↦ by simp [slope_def_field, Real.log_one]
  have hq : Tendsto
      (fun t : ℝ ↦ ((t - 1 - Real.log t) / (t - 1) ^ 2) / (Real.log t / (t - 1)))
      (𝓝[≠] 1) (𝓝 (1 / 2)) := by
    simpa [Pi.div_def] using hnum.div hden one_ne_zero
  refine hq.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds one_pos), self_mem_nhdsWithin] with t ht0 ht1
  have ht1' : t ≠ 1 := ht1
  have hlt : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht0 ht1'
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1'
  field_simp [hlt, hsub]

/-- The regularized integrand `(log t)⁻¹ - (t - 1)⁻¹` is interval integrable on `[0, x]` for every
`x ≥ 0`. -/
theorem intervalIntegrable_inv_log_sub_inv_sub_one {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) volume 0 x := by
  let g : ℝ → ℝ := fun t ↦ if t = 1 then 1 / 2 else (Real.log t)⁻¹ - (t - 1)⁻¹
  have hg_cont : ContinuousOn g (Icc 0 x) := by
    intro t ⟨ht0, _⟩
    by_cases h1 : t = 1
    · subst h1
      have hlim : Tendsto g (𝓝[≠] 1) (𝓝 (1 / 2)) := by
        refine tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u (hu1 : u ≠ 1)
        simp [g, hu1]
      have hca : ContinuousAt g 1 := by
        have hg1 : g 1 = 1 / 2 := by simp [g]
        rw [continuousAt_iff_punctured_nhds, hg1]
        exact hlim
      exact hca.continuousWithinAt
    · have hraw : ContinuousAt (fun u : ℝ ↦ (Real.log u)⁻¹ - (u - 1)⁻¹) t := by
        rcases eq_or_lt_of_le ht0 with rfl | htpos
        · exact Real.continuousAt_inv_log_zero.sub (by fun_prop (disch := norm_num))
        · have htne : t ≠ 0 := htpos.ne'
          have hlt : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one htpos h1
          have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr h1
          fun_prop (disch := assumption)
      have hca : ContinuousAt g t := by
        refine hraw.congr ?_
        filter_upwards [isOpen_ne.mem_nhds h1] with u hu1
        simp [g, hu1]
      exact hca.continuousWithinAt
  have hg_int : IntervalIntegrable g volume 0 x :=
    (hg_cont.mono (by rw [uIcc_of_le hx])).intervalIntegrable
  refine hg_int.congr_ae ?_
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht1
  simp [g, ht1]

/-- Excising `(1 - ε, 1 + ε)` from an interval-integrable integral over `[0, x]` (`x > 1`) recovers
the full integral as `ε → 0⁺`. -/
private theorem tendsto_integral_excise_one {f : ℝ → ℝ} {x : ℝ} (hx : 1 < x)
    (hf : IntervalIntegrable f volume 0 x) :
    Tendsto (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), f t) + ∫ t in (1 + ε)..x, f t)
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..x, f t)) := by
  have hx0 : 0 ≤ x := by linarith
  have hf_uIcc : IntegrableOn f (uIcc 0 x) volume := by
    rw [uIcc_of_le hx0]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx0).mp hf
  have hprim : ContinuousAt (fun a : ℝ ↦ ∫ t in (0 : ℝ)..a, f t) 1 := by
    have hcont : ContinuousOn (fun y : ℝ ↦ ∫ t in (0 : ℝ)..y, f t) (Icc 0 x) := by
      simpa [uIcc_of_le hx0] using intervalIntegral.continuousOn_primitive_interval hf_uIcc
    exact (hcont 1 ⟨zero_le_one, hx.le⟩).continuousAt (Icc_mem_nhds zero_lt_one hx)
  have ha1 : Tendsto (fun ε : ℝ ↦ ∫ t in (0 : ℝ)..(1 - ε), f t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) :=
    hprim.tendsto.comp <| by
      simpa using ((continuous_sub_left (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
  have ha2 : Tendsto (fun ε : ℝ ↦ ∫ t in (0 : ℝ)..(1 + ε), f t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) :=
    hprim.tendsto.comp <| by
      simpa using ((continuous_const_add (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), f t) +
        ((∫ t in (0 : ℝ)..x, f t) - ∫ t in (0 : ℝ)..(1 + ε), f t))
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..x, f t)) := by
    simpa using ha1.add (tendsto_const_nhds.sub ha2)
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (sub_pos.mpr hx))] with ε ⟨hε0, hεm⟩
  have h1ε : 1 + ε ≤ x := by linarith [lt_of_lt_of_le hεm (min_le_right _ _)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 1 + ε) (c := x)
    (hf.mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le hx0]; exact Icc_subset_Icc le_rfl h1ε))
    (hf.mono_set (by
      rw [uIcc_of_le h1ε, uIcc_of_le hx0]; exact Icc_subset_Icc (by linarith) le_rfl))
  linarith

/-- **Absolutely convergent integral representation of `li`**: for every `x > 0`, `x ≠ 1`,
`li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)`. -/
theorem li_eq_log_abs_sub_one_add_integral {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    li x = Real.log |x - 1| + ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  have hint_reg := intervalIntegrable_inv_log_sub_inv_sub_one hx0.le
  rcases lt_or_gt_of_ne hx1 with hx_lt | hx_gt
  · have hinv : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 0 x :=
      ContinuousOn.intervalIntegrable fun t ht ↦ by
        rw [uIcc_of_le hx0.le] at ht
        have : t - 1 ≠ 0 := by linarith [ht.2]
        fun_prop (disch := assumption)
    have hlog_int : (∫ t in (0 : ℝ)..x, (t - 1)⁻¹) = Real.log |x - 1| := by
      rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ ↦ u⁻¹) (1 : ℝ),
        integral_inv_of_neg (by norm_num) (by linarith)]
      rw [zero_sub, div_neg, div_one, Real.log_neg_eq_log, Real.log_abs]
    have hdiff := intervalIntegral.integral_sub
      (intervalIntegrable_inv_log_of_lt_one hx0.le hx_lt) hinv
    rw [← li_eq_integral_inv_log hx0 hx_lt, hlog_int] at hdiff
    linarith
  · have h1 := tendsto_integral_excise_one hx_gt hint_reg
    have h2 : Tendsto
        (fun ε : ℝ ↦
          (∫ t in (0 : ℝ)..(1 - ε), ((Real.log t)⁻¹ - (t - 1)⁻¹)) +
            ∫ t in (1 + ε)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))
        (𝓝[>] 0) (𝓝 (li x - Real.log |x - 1|)) := by
      refine ((tendsto_integral_inv_log_principalValue hx_gt).sub_const
        (Real.log |x - 1|)).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (sub_pos.mpr hx_gt))] with ε ⟨hε0, hεm⟩
      have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
      have hεx : 1 + ε < x := by linarith [lt_of_lt_of_le hεm (min_le_right _ _)]
      have hi1 : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 0 (1 - ε) :=
        ContinuousOn.intervalIntegrable fun t ht ↦ by
          rw [uIcc_of_le (by linarith)] at ht
          have : t - 1 ≠ 0 := by linarith [ht.2]
          fun_prop (disch := assumption)
      have hi2 : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume (1 + ε) x :=
        ContinuousOn.intervalIntegrable fun t ht ↦ by
          rw [uIcc_of_le hεx.le] at ht
          have : t - 1 ≠ 0 := by linarith [ht.1]
          fun_prop (disch := assumption)
      have hval1 : (∫ t in (0 : ℝ)..(1 - ε), (t - 1)⁻¹) = Real.log ε := by
        rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ ↦ u⁻¹) (1 : ℝ),
          integral_inv_of_neg (by norm_num) (by linarith)]
        simp [sub_sub_cancel_left]
      have hval2 : (∫ t in (1 + ε)..x, (t - 1)⁻¹) = Real.log |x - 1| - Real.log ε := by
        rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ ↦ u⁻¹) (1 : ℝ),
          integral_inv_of_pos (by linarith) (by linarith), add_sub_cancel_left,
          Real.log_div (by linarith) hε0.ne', abs_of_pos (sub_pos.mpr hx_gt)]
      rw [intervalIntegral.integral_sub
          (intervalIntegrable_inv_log_of_lt_one (by linarith) (by linarith)) hi1,
        intervalIntegral.integral_sub
          (by simpa [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith) hx_gt) hi2,
        hval1, hval2]
      ring
    linarith [tendsto_nhds_unique h1 h2]

/-! ### Symmetric integral representation for `li 2` -/

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` tends to `1` as `u → 0⁺`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsGT_zero :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have hp : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ - u⁻¹) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun u : ℝ ↦ 1 + u) (𝓝[>] 0) (𝓝[≠] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((continuous_const_add (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds)
        (by
          filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
          exact mem_compl_singleton_iff.mpr (by linarith))
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp h1).congr fun u ↦ ?_
    simp [Function.comp_apply]
  have hm : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹ + u⁻¹) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[>] 0) (𝓝[≠] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((continuous_sub_left (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds)
        (by
          filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
          exact mem_compl_singleton_iff.mpr (by linarith))
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp h1).congr fun u ↦ ?_
    simp only [Function.comp_apply, sub_sub_cancel_left, inv_neg, sub_neg_eq_add]
  have hsum : Tendsto
      (fun u : ℝ ↦ ((Real.log (1 + u))⁻¹ - u⁻¹) + ((Real.log (1 - u))⁻¹ + u⁻¹))
      (𝓝[>] 0) (𝓝 1) := by
    simpa only [add_halves] using hp.add hm
  exact hsum.congr fun u ↦ by ring

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` tends to `(log 2)⁻¹` as `u → 1⁻`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsLT_one :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) (𝓝[<] 1)
      (𝓝 (Real.log 2)⁻¹) := by
  have h1 : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) (𝓝[<] 1) (𝓝 (Real.log 2)⁻¹) := by
    have h11 : (1 : ℝ) + 1 = 2 := by norm_num
    have hc : ContinuousAt (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) 1 :=
      ((Real.continuousAt_log (by norm_num)).comp (by fun_prop)).inv₀ (by
        dsimp only [Function.comp_apply]
        rw [h11]
        exact (Real.log_pos one_lt_two).ne')
    simpa [h11] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) (𝓝[<] 1) (𝓝 0) := by
    have hsub : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] 1) (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((continuous_sub_left (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds)
        (by
          filter_upwards [self_mem_nhdsWithin] with u (hu : u < 1)
          exact mem_Ioi.mpr (by linarith))
    exact (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero).comp hsub
  simpa using h1.add h2

/-- Explicit bound on `(0, 1 / 2]` for the symmetric integrand of `li 2`:
`|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3`. -/
theorem abs_inv_log_one_add_add_inv_log_one_sub_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    |(Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹| ≤ 16 * Real.log (4 / 3) / 3 := by
  have h1u : 0 < 1 + u := by linarith
  have h1mu : 0 < 1 - u := by linarith
  have hlp : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
  have hlm : 0 < -Real.log (1 - u) := neg_pos.mpr (Real.log_neg h1mu (by linarith))
  -- Rewrite as `-log (1 - u^2) / (log (1 + u) * (-log (1 - u)))`.
  have hrew : (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ =
      -Real.log (1 - u ^ 2) / (Real.log (1 + u) * (-Real.log (1 - u))) := by
    have hmul : Real.log (1 + u) + Real.log (1 - u) = Real.log (1 - u ^ 2) := by
      rw [← Real.log_mul h1u.ne' h1mu.ne']; ring_nf
    have hlm_ne : Real.log (1 - u) ≠ 0 := (Real.log_neg h1mu (by linarith)).ne
    field_simp [hlp.ne', hlm_ne]
    linarith [hmul]
  have hnum_nonneg : 0 ≤ -Real.log (1 - u ^ 2) :=
    neg_nonneg.mpr (Real.log_nonpos (by nlinarith) (by nlinarith))
  rw [abs_of_nonneg (by rw [hrew]; positivity), hrew]
  -- Lower bound `log (1 + u) ≥ (3 / 4) * u` by concavity of `log` on `[1, 3 / 2]`.
  have hlp_ge : 3 / 4 * u ≤ Real.log (1 + u) := by
    have hlog32 : (3 / 8 : ℝ) ≤ Real.log (3 / 2) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have hb := Real.exp_bound' (x := (3 / 8 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by decide)
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hb
      norm_num at hb ⊢
      linarith
    have hconc : (1 - 2 * u) • Real.log 1 + (2 * u) • Real.log (3 / 2) ≤
        Real.log ((1 - 2 * u) • 1 + (2 * u) • (3 / 2)) :=
      strictConcaveOn_log_Ioi.concaveOn.2 (by norm_num) (by norm_num)
        (by linarith) (by linarith) (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hconc
    have hcomb : (1 - 2 * u) * 1 + 2 * u * (3 / 2) = 1 + u := by ring
    rw [hcomb] at hconc
    nlinarith
  have hlm_ge : u ≤ -Real.log (1 - u) := by linarith [Real.log_le_sub_one_of_pos h1mu]
  -- Upper bound `-log (1 - u^2) ≤ 4 * log (4 / 3) * u^2` by concavity of `log` on `[3 / 4, 1]`.
  have hnum_le : -Real.log (1 - u ^ 2) ≤ 4 * Real.log (4 / 3) * u ^ 2 := by
    have hconc : (1 - 4 * u ^ 2) • Real.log 1 + (4 * u ^ 2) • Real.log (3 / 4) ≤
        Real.log ((1 - 4 * u ^ 2) • 1 + (4 * u ^ 2) • (3 / 4)) :=
      strictConcaveOn_log_Ioi.concaveOn.2 (by norm_num) (by norm_num)
        (by nlinarith) (by positivity) (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hconc
    have hcomb : (1 - 4 * u ^ 2) * 1 + 4 * u ^ 2 * (3 / 4) = 1 - u ^ 2 := by ring
    have hlog34 : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3) := by rw [← Real.log_inv]; norm_num
    rw [hcomb, hlog34] at hconc
    linarith
  have hden_ge : 3 / 4 * u ^ 2 ≤ Real.log (1 + u) * (-Real.log (1 - u)) := by
    calc 3 / 4 * u ^ 2 = (3 / 4 * u) * u := by ring
      _ ≤ Real.log (1 + u) * (-Real.log (1 - u)) := mul_le_mul hlp_ge hlm_ge hu0.le hlp.le
  calc -Real.log (1 - u ^ 2) / (Real.log (1 + u) * (-Real.log (1 - u)))
      ≤ (4 * Real.log (4 / 3) * u ^ 2) / (3 / 4 * u ^ 2) :=
        div_le_div₀ (by have : 0 ≤ Real.log (4 / 3) := Real.log_nonneg (by norm_num); positivity)
          hnum_le (by positivity) hden_ge
    _ = 16 * Real.log (4 / 3) / 3 := by field_simp [hu0.ne']; ring

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` is interval integrable on
`[0, 1]`. -/
theorem intervalIntegrable_inv_log_one_add_add_inv_log_one_sub :
    IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) volume 0 1 := by
  have h1 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ - (1 + u - 1)⁻¹) volume 0 1 := by
    have h := (intervalIntegrable_inv_log_sub_inv_sub_one (x := 2) (by norm_num)).mono_set
      (by rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
          exact Icc_subset_Icc zero_le_one le_rfl)
    have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    simpa [add_comm, h21] using h.comp_add_left 1
  have h2 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 - u))⁻¹ - (1 - u - 1)⁻¹) volume 0 1 := by
    have h := intervalIntegrable_inv_log_sub_inv_sub_one (x := 1) zero_le_one
    simpa [sub_zero, sub_self] using (h.comp_sub_left 1).symm
  refine (h1.add h2).congr_ae ?_
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with u _
  simp only [add_sub_cancel_left, sub_sub_cancel_left, inv_neg]
  ring

/-- **Symmetric absolutely convergent integral for `li 2`**:
`li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)`. -/
theorem li_two_eq_integral_symm :
    li 2 = ∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) := by
  have hreg := li_eq_log_abs_sub_one_add_integral two_pos (by norm_num)
  norm_num [Real.log_one] at hreg
  have h21 : (2 : ℝ) - 1 = 1 := by norm_num
  have h11 : (1 : ℝ) + 1 = 2 := by norm_num
  have h1 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ - (1 + u - 1)⁻¹) volume 0 1 := by
    have h := (intervalIntegrable_inv_log_sub_inv_sub_one (x := 2) (by norm_num)).mono_set
      (by rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
          exact Icc_subset_Icc zero_le_one le_rfl)
    simpa [add_comm, h21] using h.comp_add_left 1
  have h2 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 - u))⁻¹ - (1 - u - 1)⁻¹) volume 0 1 := by
    have h := intervalIntegrable_inv_log_sub_inv_sub_one (x := 1) zero_le_one
    simpa [sub_zero, sub_self] using (h.comp_sub_left 1).symm
  have heq : (∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹)) =
      (∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ - (1 + u - 1)⁻¹)) +
        ∫ u in (0 : ℝ)..1, ((Real.log (1 - u))⁻¹ - (1 - u - 1)⁻¹) := by
    rw [← intervalIntegral.integral_add h1 h2]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [volume.ae_ne (0 : ℝ)] with u _ _
    simp only [add_sub_cancel_left, sub_sub_cancel_left, inv_neg]
    ring
  have hshift1 : (∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ - (1 + u - 1)⁻¹)) =
      ∫ t in (1 : ℝ)..2, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
    simpa [add_zero, h11] using
      intervalIntegral.integral_comp_add_left (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (1 : ℝ)
        (a := (0 : ℝ)) (b := 1)
  have hshift2 : (∫ u in (0 : ℝ)..1, ((Real.log (1 - u))⁻¹ - (1 - u - 1)⁻¹)) =
      ∫ t in (0 : ℝ)..1, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
    simpa [sub_zero, sub_self] using
      intervalIntegral.integral_comp_sub_left (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (1 : ℝ)
        (a := (0 : ℝ)) (b := 1)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log_sub_inv_sub_one (x := 1) zero_le_one)
    ((intervalIntegrable_inv_log_sub_inv_sub_one (x := 2) (by norm_num)).mono_set
      (by rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
          exact Icc_subset_Icc zero_le_one le_rfl))
  rw [heq, hshift1, hshift2, add_comm, hsplit, ← hreg]

end TauCeti.Real
