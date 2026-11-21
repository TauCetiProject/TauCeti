/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Log.InvLog
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.NumberTheory.Harmonic.GammaDeriv

/-!
# Principal-value and regularized integral representations of `li`

This file recovers the classical Cauchy principal-value and exponential-integral (`Ei (log x)`)
characterizations of `Real.li` from the globally convergent series definition in
`TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset`, and supplies pole-subtracted and
symmetrically folded Lebesgue integrals that avoid principal-value limits when evaluating `li x`
and `li 2`:

* On `(0, 1)`, `li x = ∫ t in 0..x, (log t)⁻¹` as an ordinary Lebesgue interval integral.
* On `(1, ∞)`, `li x` is the Cauchy principal value
  `lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹)`.
* In exponential-integral coordinates `t = e^u`, `∫ u in Iic y, exp u / u = li (exp y)` for
  `y < 0`, `li (exp y) = γ + log |y| + ∫ u in 0..y, (exp u - 1) / u` for all `y : ℝ`, and
  `∫ u in (-ε⁻¹)..(-ε), exp u / u + ∫ u in ε..y, exp u / u → li (exp y)` as `ε → 0⁺` for `y > 0`.
* Subtracting `(t - 1)⁻¹` cancels the pole at `t = 1` and gives the absolutely convergent
  representation `li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)` for all `x > 0`,
  `x ≠ 1`.
* Folding around `t = 1` gives the symmetric integral
  `li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)` together with the boundary limits
  and explicit bound `|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3` on `(0, 1 / 2]`.

## Main declarations

* `Real.intervalIntegrable_inv_log_of_lt_one` and `Real.li_eq_integral_inv_log` — ordinary
  integral on `(0, 1)`.
* `Real.tendsto_li_one_add_sub_one_sub` and `Real.tendsto_integral_inv_log_principalValue` —
  Cauchy principal value on `(1, ∞)`.
* `Real.hasDerivAt_li_exp`, `Real.integral_exp_div_eq_li_exp_sub`,
  `Real.integral_Iic_exp_div_eq_li_exp`, `Real.li_exp`, and
  `Real.tendsto_integral_exp_div_principalValue` — exponential-integral forms.
* `Real.intervalIntegrable_inv_log_sub_inv_sub_one`,
  `Real.exists_abs_inv_log_sub_inv_sub_one_le`, and
  `Real.li_eq_log_abs_sub_one_add_integral` — absolutely convergent regularized integral.
* `Real.tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsNE_zero`,
  `Real.continuousAt_inv_log_one_add_add_inv_log_one_sub_one`,
  `Real.abs_inv_log_one_add_add_inv_log_one_sub_le`,
  `Real.intervalIntegrable_inv_log_one_add_add_inv_log_one_sub`, and
  `Real.li_two_eq_integral_inv_log_one_add_add_inv_log_one_sub` — symmetric integral for `li 2`
  and its explicit bound on `(0, 1 / 2]`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2 (Exponential,
  Logarithmic, Sine, and Cosine Integrals).
* H. Davenport, *Multiplicative Number Theory*, Chapters 7 and 18.
-/

public section

open Filter MeasureTheory Set TauCeti.Real
open scoped Topology Nat

namespace Real

/-! ### Principal value and exponential-integral representations -/

/-- `(log t)⁻¹` is interval integrable on any interval contained in `[0, 1)`. -/
theorem intervalIntegrable_inv_log_of_lt_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    IntervalIntegrable (fun t : ℝ ↦ (log t)⁻¹) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
  have ht0 : 0 ≤ t := (le_min ha0 hb0).trans ht.1
  have ht1 : t < 1 := ht.2.trans_lt (max_lt ha1 hb1)
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · exact continuousAt_inv_log_zero.continuousWithinAt
  · exact ((continuousAt_log htpos.ne').inv₀ (log_neg htpos ht1).ne).continuousWithinAt

/-- On `(0, 1)`, the unoffset logarithmic integral is the ordinary integral
`li x = ∫ t in 0..x, (log t)⁻¹`. -/
theorem li_eq_integral_inv_log {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    li x = ∫ t in (0 : ℝ)..x, (log t)⁻¹ := by
  simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx0
    (fun t ht ↦ hasDerivAt_li ht.1 (ht.2.trans hx1).ne)
    (intervalIntegrable_inv_log_of_lt_one le_rfl one_pos hx0.le hx1)
    tendsto_li_nhdsGT_zero
    ((continuousAt_li hx0 hx1.ne).tendsto.mono_left nhdsWithin_le_nhds)).symm

/-- Symmetric cancellation of the logarithmic pole of `li` at `1`:
`li (1 + ε) - li (1 - ε) → 0` as `ε → 0⁺`. -/
theorem tendsto_li_one_add_sub_one_sub :
    Tendsto (fun ε : ℝ ↦ li (1 + ε) - li (1 - ε)) (𝓝[>] 0) (𝓝 0) := by
  have hlog_ratio : Tendsto (fun ε : ℝ ↦ log (1 + ε) / (-log (1 - ε))) (𝓝[>] 0) (𝓝 1) := by
    have hp : Tendsto (fun ε : ℝ ↦ log (1 + ε) / ε) (𝓝[>] 0) (𝓝 1) := by
      have hd : HasDerivAt (fun t : ℝ ↦ log (1 + t)) 1 0 := by
        simpa using ((hasDerivAt_id' (0 : ℝ)).const_add (1 : ℝ)).log (by norm_num)
      exact (hd.tendsto_slope_zero.congr fun ε ↦ by simp [log_one, div_eq_inv_mul]).mono_left
        (nhdsGT_le_nhdsNE 0)
    have hm : Tendsto (fun ε : ℝ ↦ -log (1 - ε) / ε) (𝓝[>] 0) (𝓝 1) := by
      have hd : HasDerivAt (fun t : ℝ ↦ -log (1 - t)) 1 0 := by
        simpa using (((hasDerivAt_id' (0 : ℝ)).const_sub (1 : ℝ)).log (by norm_num)).fun_neg
      exact (hd.tendsto_slope_zero.congr fun ε ↦ by simp [log_one, div_eq_inv_mul]).mono_left
        (nhdsGT_le_nhdsNE 0)
    have hdiv : Tendsto (fun ε : ℝ ↦ (log (1 + ε) / ε) / (-log (1 - ε) / ε)) (𝓝[>] 0) (𝓝 1) := by
      simpa [Pi.div_def] using hp.div hm one_ne_zero
    refine hdiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    field_simp [hε.ne']
  have hlog_diff : Tendsto (fun ε : ℝ ↦ log (log (1 + ε)) - log (log (1 - ε))) (𝓝[>] 0) (𝓝 0) := by
    have hcomp := (continuousAt_log one_ne_zero).tendsto.comp hlog_ratio
    rw [log_one] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε ⟨hε0, hε1⟩
    have h1 : 0 < log (1 + ε) := log_pos (by linarith)
    have h2 : 0 < -log (1 - ε) := neg_pos.mpr (log_neg (by linarith) (by linarith))
    dsimp only [Function.comp_apply]
    rw [log_div h1.ne' h2.ne', log_neg_eq_log]
  have hser_diff : Tendsto
      (fun ε : ℝ ↦
        (∑' n : ℕ, log (1 + ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
        (∑' n : ℕ, log (1 - ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))))
      (𝓝[>] 0) (𝓝 0) := by
    have hc1 : ContinuousAt (fun ε : ℝ ↦
        ∑' n : ℕ, log (1 + ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) 0 :=
      continuous_tsum_pow_div_mul_factorial.continuousAt.comp
        ((continuousAt_log (by norm_num)).comp (by fun_prop))
    have hc2 : ContinuousAt (fun ε : ℝ ↦
        ∑' n : ℕ, log (1 - ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) 0 :=
      continuous_tsum_pow_div_mul_factorial.continuousAt.comp
        ((continuousAt_log (by norm_num)).comp (by fun_prop))
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
      (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), (log t)⁻¹) + ∫ t in (1 + ε)..x, (log t)⁻¹)
      (𝓝[>] 0) (𝓝 (li x)) := by
  have hlim : Tendsto (fun ε : ℝ ↦ li x - (li (1 + ε) - li (1 - ε))) (𝓝[>] 0) (𝓝 (li x)) := by
    simpa using tendsto_const_nhds.sub tendsto_li_one_add_sub_one_sub
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (sub_pos.mpr hx))] with ε ⟨hε0, hεm⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
  have hεx : 1 + ε < x := by linarith [lt_of_lt_of_le hεm (min_le_right _ _)]
  rw [← li_eq_integral_inv_log (by linarith) (by linarith)]
  have hFTC : (∫ t in (1 + ε)..x, (log t)⁻¹) = li x - li (1 + ε) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ by
        rw [uIcc_of_le hεx.le] at ht
        exact hasDerivAt_li (by linarith [ht.1]) (by linarith [ht.1]))
      (by simpa [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith) hx)
  rw [hFTC]
  ring

/-- In exponential coordinates, `t ↦ li (exp t)` has derivative `exp u / u` at every `u ≠ 0`. -/
theorem hasDerivAt_li_exp {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ li (exp t)) (exp u / u) u := by
  have hne : exp u ≠ 1 := fun h ↦ hu (by simpa [log_exp] using congrArg log h)
  have h := (hasDerivAt_li (exp_pos u) hne).comp u (hasDerivAt_exp u)
  simpa only [Function.comp_def, log_exp, div_eq_mul_inv, mul_comm] using h

/-- On any closed interval avoiding `0`, `∫ u in a..b, exp u / u = li (exp b) - li (exp a)`. -/
theorem integral_exp_div_eq_li_exp_sub {a b : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) :
    (∫ u in a..b, exp u / u) = li (exp b) - li (exp a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ li (exp t))
    (fun u hu ↦ hasDerivAt_li_exp fun h ↦ h0 (h ▸ hu))
    (ContinuousOn.intervalIntegrable fun u hu ↦ ?_)
  have hu0 : u ≠ 0 := fun h ↦ h0 (h ▸ hu)
  fun_prop (disch := assumption)

/-- `u ↦ exp u / u` is integrable on `(-∞, y]` whenever `y < 0`. -/
theorem integrableOn_exp_div_Iic {y : ℝ} (hy : y < 0) :
    IntegrableOn (fun u : ℝ ↦ exp u / u) (Iic y) := by
  have hcomp := (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
    (Homeomorph.neg ℝ).measurableEmbedding).mpr (integrableOn_exp_neg_div_Ioi (neg_pos.mpr hy))
  have hIio : IntegrableOn (fun u : ℝ ↦ exp u / u) (Iio y) := by
    simpa [Function.comp_def, div_neg] using hcomp.neg
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  exact hIio

/-- Exponential-integral form of `li` on `(0, 1)`: for `y < 0`,
`∫ u in Iic y, exp u / u = li (exp y)`. -/
theorem integral_Iic_exp_div_eq_li_exp {y : ℝ} (hy : y < 0) :
    (∫ u in Iic y, exp u / u) = li (exp y) := by
  have hlim : Tendsto (fun t : ℝ ↦ li (exp t)) atBot (𝓝 0) :=
    tendsto_li_nhdsGT_zero.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_exp_atBot (Eventually.of_forall exp_pos))
  simpa using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun u hu ↦ hasDerivAt_li_exp (lt_of_le_of_lt hu hy).ne)
    (integrableOn_exp_div_Iic hy) hlim

/-- **Exponential-integral representation via the regularized integrand** `(exp u - 1) / u`:
for every `y : ℝ`, `li (exp y) = γ + log |y| + ∫ u in 0..y, (exp u - 1) / u`. -/
theorem li_exp (y : ℝ) :
    li (exp y) = eulerMascheroniConstant + log |y| + ∫ u in (0 : ℝ)..y, (exp u - 1) / u := by
  rw [li_eq_add_log_abs, log_exp, integral_exp_sub_one_div_eq_tsum]

/-- **Exponential-integral principal value representation of `li` on `(1, ∞)`**: for `y > 0`,
`∫ u in (-ε⁻¹)..(-ε), exp u / u + ∫ u in ε..y, exp u / u → li (exp y)` as `ε → 0⁺`. -/
theorem tendsto_integral_exp_div_principalValue {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun ε : ℝ ↦ (∫ u in (-ε⁻¹)..(-ε), exp u / u) + ∫ u in ε..y, exp u / u)
      (𝓝[>] 0) (𝓝 (li (exp y))) := by
  have hneg_inv : Tendsto (fun ε : ℝ ↦ li (exp (-ε⁻¹))) (𝓝[>] 0) (𝓝 0) :=
    tendsto_li_nhdsGT_zero.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_inv_nhdsGT_zero))
      (Eventually.of_forall fun _ ↦ exp_pos _))
  have hsymm : Tendsto (fun ε : ℝ ↦ li (exp (-ε)) - li (exp ε)) (𝓝[>] 0) (𝓝 0) := by
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
    rw [li_def, li_def, log_exp, log_exp, log_neg_eq_log]
    ring
  have hlim : Tendsto
      (fun ε : ℝ ↦ li (exp y) - li (exp (-ε⁻¹)) + (li (exp (-ε)) - li (exp ε)))
      (𝓝[>] 0) (𝓝 (li (exp y))) := by
    simpa using (tendsto_const_nhds.sub hneg_inv).add hsymm
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hy)] with ε ⟨hε0, hεm⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
  have hεy : ε < y := lt_of_lt_of_le hεm (min_le_right _ _)
  have hle_neg : -ε⁻¹ ≤ -ε := by linarith [(one_le_inv₀ hε0).mpr hε1.le]
  have h1 : (∫ u in (-ε⁻¹)..(-ε), exp u / u) = li (exp (-ε)) - li (exp (-ε⁻¹)) :=
    integral_exp_div_eq_li_exp_sub fun h ↦ by
      rw [uIcc_of_le hle_neg] at h
      linarith [h.2]
  have h2 : (∫ u in ε..y, exp u / u) = li (exp y) - li (exp ε) :=
    integral_exp_div_eq_li_exp_sub fun h ↦ by
      rw [uIcc_of_le hεy.le] at h
      linarith [h.1]
  rw [h1, h2]
  ring

/-! ### Absolutely convergent integral representations -/

/-- The regularized integrand `(log t)⁻¹ - (t - 1)⁻¹` is interval integrable on any interval in
`[0, ∞)`. -/
theorem intervalIntegrable_inv_log_sub_inv_sub_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) volume a b := by
  have hg_int : IntervalIntegrable
      (Function.update (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) 1 (1 / 2)) volume a b :=
    (continuousOn_update_inv_log_sub_inv_sub_one.mono
      fun t (ht : t ∈ uIcc a b) ↦ (le_min ha hb).trans ht.1).intervalIntegrable
  refine hg_int.congr_ae ?_
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht1
  exact Function.update_of_ne ht1 _ _

/-- The regularized integrand `(log t)⁻¹ - (t - 1)⁻¹` is bounded in absolute value on every
compact interval `[a, b]` with `0 ≤ a`. -/
theorem exists_abs_inv_log_sub_inv_sub_one_le {a b : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, ∀ t ∈ Icc a b, |(log t)⁻¹ - (t - 1)⁻¹| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_update_inv_log_sub_inv_sub_one.mono fun t (ht : t ∈ Icc a b) ↦ ha.trans ht.1)
  refine ⟨max C 0, fun t ht ↦ ?_⟩
  rcases eq_or_ne t 1 with rfl | ht1
  · simp
  · calc |(log t)⁻¹ - (t - 1)⁻¹|
        = ‖Function.update (fun u : ℝ ↦ (log u)⁻¹ - (u - 1)⁻¹) 1 (1 / 2) t‖ := by
          rw [Function.update_of_ne ht1, norm_eq_abs]
      _ ≤ C := hC t ht
      _ ≤ max C 0 := le_max_left _ _

/-- **Absolutely convergent integral representation of `li`**: for every `x > 0`, `x ≠ 1`,
`li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)`. -/
theorem li_eq_log_abs_sub_one_add_integral {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    li x = log |x - 1| + ∫ t in (0 : ℝ)..x, ((log t)⁻¹ - (t - 1)⁻¹) := by
  rcases lt_or_gt_of_ne hx1 with hx_lt | hx_gt
  · have h1 : (1 : ℝ) ∉ uIcc 0 x := by rw [uIcc_of_le hx0.le]; intro h; linarith [h.2]
    have hdiff := intervalIntegral.integral_sub
      (intervalIntegrable_inv_log_of_lt_one le_rfl one_pos hx0.le hx_lt)
      (intervalIntegrable_sub_inv_iff.mpr (Or.inr h1))
    rw [← li_eq_integral_inv_log hx0 hx_lt, integral_sub_inv h1, zero_sub, abs_neg, abs_one,
      log_one, sub_zero] at hdiff
    linarith
  · have h1 := (TauCeti.intervalIntegral.tendsto_integral_excise (c := 1)
      (by rw [uIoo_of_le hx0.le]; exact ⟨one_pos, hx_gt⟩)
      (intervalIntegrable_inv_log_sub_inv_sub_one le_rfl hx0.le)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    have h2 : Tendsto
        (fun ε : ℝ ↦
          (∫ t in (0 : ℝ)..(1 - ε), ((log t)⁻¹ - (t - 1)⁻¹)) +
            ∫ t in (1 + ε)..x, ((log t)⁻¹ - (t - 1)⁻¹))
        (𝓝[>] 0) (𝓝 (li x - log |x - 1|)) := by
      refine ((tendsto_integral_inv_log_principalValue hx_gt).sub_const
        (log |x - 1|)).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (sub_pos.mpr hx_gt))] with ε ⟨hε0, hεm⟩
      have hε1 : ε < 1 := lt_of_lt_of_le hεm (min_le_left _ _)
      have hεx : 1 + ε < x := by linarith [lt_of_lt_of_le hεm (min_le_right _ _)]
      have hnot1 : (1 : ℝ) ∉ uIcc 0 (1 - ε) := by
        rw [uIcc_of_le (by linarith)]; intro h; linarith [h.2]
      have hnot2 : (1 : ℝ) ∉ uIcc (1 + ε) x := by
        rw [uIcc_of_le hεx.le]; intro h; linarith [h.1]
      rw [intervalIntegral.integral_sub
            (intervalIntegrable_inv_log_of_lt_one le_rfl one_pos (by linarith) (by linarith))
            (intervalIntegrable_sub_inv_iff.mpr (Or.inr hnot1)),
          intervalIntegral.integral_sub
            (by simpa [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith) hx_gt)
            (intervalIntegrable_sub_inv_iff.mpr (Or.inr hnot2)),
          integral_sub_inv hnot1, integral_sub_inv hnot2]
      have hε_sub : |1 - ε - 1| = ε := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε0]
      have hε_add : |1 + ε - 1| = ε := by rw [add_sub_cancel_left, abs_of_pos hε0]
      rw [hε_sub, hε_add]
      norm_num [log_one]
      ring
    linarith [tendsto_nhds_unique h1 h2]

/-! ### Symmetric integral representation for `li 2` -/

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` tends to `1` as `u → 0`,
`u ≠ 0`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsNE_zero :
    Tendsto (fun u : ℝ ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹) (𝓝[≠] 0) (𝓝 1) := by
  have hp : Tendsto (fun u : ℝ ↦ (log (1 + u))⁻¹ - u⁻¹) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun u : ℝ ↦ 1 + u) (𝓝[≠] 0) (𝓝[≠] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((continuous_const_add (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds)
        (by
          filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
          exact mem_compl_singleton_iff.mpr (by simpa using hu))
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp h1).congr fun u ↦ ?_
    simp [Function.comp_apply]
  have hm : Tendsto (fun u : ℝ ↦ (log (1 - u))⁻¹ + u⁻¹) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[≠] 0) (𝓝[≠] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((continuous_sub_left (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds)
        (by
          filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
          exact mem_compl_singleton_iff.mpr (by simp [sub_eq_self, hu]))
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp h1).congr fun u ↦ ?_
    simp only [Function.comp_apply, sub_sub_cancel_left, inv_neg, sub_neg_eq_add]
  have hsum : Tendsto
      (fun u : ℝ ↦ ((log (1 + u))⁻¹ - u⁻¹) + ((log (1 - u))⁻¹ + u⁻¹))
      (𝓝[≠] 0) (𝓝 1) := by
    simpa only [add_halves] using hp.add hm
  exact hsum.congr fun u ↦ by ring

/-- The symmetric integrand `u ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹` is continuous at `1`, where it
takes the value `(log 2)⁻¹`. -/
theorem continuousAt_inv_log_one_add_add_inv_log_one_sub_one :
    ContinuousAt (fun u : ℝ ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹) 1 := by
  have h1 : ContinuousAt (fun u : ℝ ↦ (log (1 + u))⁻¹) 1 :=
    ((continuousAt_log (by norm_num)).comp (by fun_prop)).inv₀ (by
      have h11 : (1 : ℝ) + 1 = 2 := by norm_num
      dsimp only [Function.comp_apply]
      rw [h11]
      exact (log_pos one_lt_two).ne')
  have h2 : ContinuousAt (fun u : ℝ ↦ (log (1 - u))⁻¹) 1 := by
    have h0 : ContinuousAt (fun t : ℝ ↦ (log t)⁻¹) (1 - 1) := by
      simpa [sub_self] using continuousAt_inv_log_zero
    exact h0.comp (continuous_sub_left (1 : ℝ)).continuousAt
  exact h1.add h2

/-- Explicit bound on `(0, 1 / 2]` for the symmetric integrand of `li 2`:
`|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3`. -/
theorem abs_inv_log_one_add_add_inv_log_one_sub_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    |(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3 := by
  have h1u : 0 < 1 + u := by linarith
  have h1mu : 0 < 1 - u := by linarith
  have hlp : 0 < log (1 + u) := log_pos (by linarith)
  have hlm : 0 < -log (1 - u) := neg_pos.mpr (log_neg h1mu (by linarith))
  -- Rewrite as `-log (1 - u^2) / (log (1 + u) * (-log (1 - u)))`.
  have hrew : (log (1 + u))⁻¹ + (log (1 - u))⁻¹ =
      -log (1 - u ^ 2) / (log (1 + u) * (-log (1 - u))) := by
    have hmul : log (1 + u) + log (1 - u) = log (1 - u ^ 2) := by
      rw [← log_mul h1u.ne' h1mu.ne']; ring_nf
    have hlm_ne : log (1 - u) ≠ 0 := (log_neg h1mu (by linarith)).ne
    field_simp [hlp.ne', hlm_ne]
    linarith [hmul]
  have hnum_nonneg : 0 ≤ -log (1 - u ^ 2) :=
    neg_nonneg.mpr (log_nonpos (by nlinarith) (by nlinarith))
  rw [abs_of_nonneg (by rw [hrew]; positivity), hrew]
  -- Lower bound `log (1 + u) ≥ (3 / 4) * u` by concavity of `log` on `[1, 3 / 2]`.
  have hlp_ge : 3 / 4 * u ≤ log (1 + u) := by
    have hlog32 : (3 / 8 : ℝ) ≤ log (3 / 2) := by
      rw [le_log_iff_exp_le (by norm_num)]
      have hb := exp_bound' (x := (3 / 8 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by decide)
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hb
      norm_num at hb ⊢
      linarith
    have hconc : (1 - 2 * u) • log 1 + (2 * u) • log (3 / 2) ≤
        log ((1 - 2 * u) • 1 + (2 * u) • (3 / 2)) :=
      strictConcaveOn_log_Ioi.concaveOn.2 (by norm_num) (by norm_num)
        (by linarith) (by linarith) (by ring)
    simp only [smul_eq_mul, log_one, mul_zero, zero_add] at hconc
    have hcomb : (1 - 2 * u) * 1 + 2 * u * (3 / 2) = 1 + u := by ring
    rw [hcomb] at hconc
    nlinarith
  have hlm_ge : u ≤ -log (1 - u) := by linarith [log_le_sub_one_of_pos h1mu]
  -- Upper bound `-log (1 - u^2) ≤ 4 * log (4 / 3) * u^2` by concavity of `log` on `[3 / 4, 1]`.
  have hnum_le : -log (1 - u ^ 2) ≤ 4 * log (4 / 3) * u ^ 2 := by
    have hconc : (1 - 4 * u ^ 2) • log 1 + (4 * u ^ 2) • log (3 / 4) ≤
        log ((1 - 4 * u ^ 2) • 1 + (4 * u ^ 2) • (3 / 4)) :=
      strictConcaveOn_log_Ioi.concaveOn.2 (by norm_num) (by norm_num)
        (by nlinarith) (by positivity) (by ring)
    simp only [smul_eq_mul, log_one, mul_zero, zero_add] at hconc
    have hcomb : (1 - 4 * u ^ 2) * 1 + 4 * u ^ 2 * (3 / 4) = 1 - u ^ 2 := by ring
    have hlog34 : log (3 / 4 : ℝ) = -log (4 / 3) := by rw [← log_inv]; norm_num
    rw [hcomb, hlog34] at hconc
    linarith
  have hden_ge : 3 / 4 * u ^ 2 ≤ log (1 + u) * (-log (1 - u)) := by
    calc 3 / 4 * u ^ 2 = (3 / 4 * u) * u := by ring
      _ ≤ log (1 + u) * (-log (1 - u)) := mul_le_mul hlp_ge hlm_ge hu0.le hlp.le
  calc -log (1 - u ^ 2) / (log (1 + u) * (-log (1 - u)))
      ≤ (4 * log (4 / 3) * u ^ 2) / (3 / 4 * u ^ 2) :=
        div_le_div₀ (by have : 0 ≤ log (4 / 3) := log_nonneg (by norm_num); positivity)
          hnum_le (by positivity) hden_ge
    _ = 16 * log (4 / 3) / 3 := by field_simp [hu0.ne']; ring

private theorem intervalIntegrable_inv_log_one_add_sub_inv :
    IntervalIntegrable (fun u : ℝ ↦ (log (1 + u))⁻¹ - u⁻¹) volume 0 1 := by
  have h := intervalIntegrable_inv_log_sub_inv_sub_one (a := 1) (b := 2) zero_le_one (by norm_num)
  have h21 : (2 : ℝ) - 1 = 1 := by norm_num
  simpa [add_comm, add_sub_cancel_left, h21] using h.comp_add_left 1

private theorem intervalIntegrable_inv_log_one_sub_add_inv :
    IntervalIntegrable (fun u : ℝ ↦ (log (1 - u))⁻¹ + u⁻¹) volume 0 1 := by
  have h := intervalIntegrable_inv_log_sub_inv_sub_one (a := 0) (b := 1) le_rfl zero_le_one
  simpa [sub_zero, sub_self, sub_sub_cancel_left, inv_neg, sub_neg_eq_add] using
    (h.comp_sub_left 1).symm

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` is interval integrable on
`[0, 1]`. -/
theorem intervalIntegrable_inv_log_one_add_add_inv_log_one_sub :
    IntervalIntegrable (fun u : ℝ ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹) volume 0 1 := by
  convert intervalIntegrable_inv_log_one_add_sub_inv.add
    intervalIntegrable_inv_log_one_sub_add_inv using 1
  ext u
  ring

/-- **Symmetric absolutely convergent integral for `li 2`**:
`li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)`. -/
theorem li_two_eq_integral_inv_log_one_add_add_inv_log_one_sub :
    li 2 = ∫ u in (0 : ℝ)..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹) := by
  have hreg := li_eq_log_abs_sub_one_add_integral two_pos (by norm_num)
  norm_num [log_one] at hreg
  have heq : (∫ u in (0 : ℝ)..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)) =
      (∫ u in (0 : ℝ)..1, ((log (1 + u))⁻¹ - u⁻¹)) +
        ∫ u in (0 : ℝ)..1, ((log (1 - u))⁻¹ + u⁻¹) := by
    rw [← intervalIntegral.integral_add intervalIntegrable_inv_log_one_add_sub_inv
      intervalIntegrable_inv_log_one_sub_add_inv]
    exact intervalIntegral.integral_congr fun u _ ↦ by ring
  have hshift1 : (∫ u in (0 : ℝ)..1, ((log (1 + u))⁻¹ - u⁻¹)) =
      ∫ t in (1 : ℝ)..2, ((log t)⁻¹ - (t - 1)⁻¹) := by
    simpa [add_zero, add_sub_cancel_left, show (1 : ℝ) + 1 = 2 by norm_num] using
      intervalIntegral.integral_comp_add_left (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) (1 : ℝ)
        (a := (0 : ℝ)) (b := 1)
  have hshift2 : (∫ u in (0 : ℝ)..1, ((log (1 - u))⁻¹ + u⁻¹)) =
      ∫ t in (0 : ℝ)..1, ((log t)⁻¹ - (t - 1)⁻¹) := by
    simpa [sub_zero, sub_self, sub_sub_cancel_left, inv_neg, sub_neg_eq_add] using
      intervalIntegral.integral_comp_sub_left (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) (1 : ℝ)
        (a := (0 : ℝ)) (b := 1)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log_sub_inv_sub_one (a := (0 : ℝ)) (b := 1) le_rfl zero_le_one)
    (intervalIntegrable_inv_log_sub_inv_sub_one (a := (1 : ℝ)) (b := 2) zero_le_one (by norm_num))
  rw [heq, hshift1, hshift2, add_comm, hsplit, ← hreg]

end Real
