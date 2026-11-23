/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.Integrals
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.InvLog
import TauCeti.Analysis.SpecialFunctions.Log.Limits

/-!
# The unoffset logarithmic integral

This file defines the unoffset logarithmic integral
`li x = γ + log |log x| + ∑' n, (log x) ^ (n + 1) / ((n + 1) * (n + 1)!)`,
which equals the exponential integral `Ei (log x)` for `x > 0`, `x ≠ 1` (at `x = 1`, where
`log x = 0`, the definition takes a junk value).

## Main declarations

* `TauCeti.Real.unoffsetLogIntegralSeries`: the entire series
  `∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)`.
* `TauCeti.Real.unoffsetLogIntegral`: the unoffset logarithmic integral `li`.
* `TauCeti.Real.hasDerivAt_unoffsetLogIntegral`: `li' x = (log x)⁻¹` for `x > 0`, `x ≠ 1`.
* `TauCeti.Real.tendsto_unoffsetLogIntegral_nhdsGT_zero`: `li x → 0` as `x → 0⁺`.
* `TauCeti.Real.unoffsetLogIntegral_eq_integral`: `li x = ∫ t in 0..x, (log t)⁻¹` for
  `0 < x < 1`.
* `TauCeti.Real.tendsto_principalValue_inv_log`: the Cauchy principal value
  `∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹ → li x` for `x > 1`.
* `TauCeti.Real.logIntegral_eq_unoffsetLogIntegral_sub`: `Li x = li x - li 2` for `x > 1`.
* `TauCeti.Real.strictAntiOn_unoffsetLogIntegral_Ioo`,
  `TauCeti.Real.strictMonoOn_unoffsetLogIntegral_Ioi`: `li` decreases on `(0, 1)` (where it is
  negative) and increases on `(1, ∞)` from `-∞` to `+∞`.
* `TauCeti.Real.existsUnique_unoffsetLogIntegral_eq_zero`: Soldner's constant, the unique zero
  of `li` on `(1, ∞)`.
* `TauCeti.Real.isBigO_unoffsetLogIntegral_sub_sum`,
  `TauCeti.Real.unoffsetLogIntegral_isEquivalent_div_log`: asymptotic expansion to arbitrary order
  and `li x ~ Li x ~ x / log x` as `x → ∞`.
-/

public section

namespace TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology Nat

/-! ### The unoffset logarithmic integral and its derivative -/

/-- The entire power-series part `∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)` of the unoffset
logarithmic integral `Ei(y) - γ - log |y|`. -/
noncomputable def unoffsetLogIntegralSeries (y : ℝ) : ℝ :=
  ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))

/-- Defining equation of `TauCeti.Real.unoffsetLogIntegralSeries`. -/
theorem unoffsetLogIntegralSeries_def (y : ℝ) :
    unoffsetLogIntegralSeries y =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := (rfl)

/-- The power series `TauCeti.Real.unoffsetLogIntegralSeries` is differentiable everywhere on `ℝ`,
with derivative `Function.update (fun u : ℝ ↦ (exp u - 1) / u) 0 1 y`. -/
theorem hasDerivAt_unoffsetLogIntegralSeries (y : ℝ) :
    HasDerivAt unoffsetLogIntegralSeries
      (Function.update (fun u : ℝ ↦ (Real.exp u - 1) / u) 0 1 y) y :=
  Real.hasDerivAt_tsum_pow_div_mul_factorial y

/-- `TauCeti.Real.unoffsetLogIntegralSeries` is continuous on `ℝ`. -/
theorem continuous_unoffsetLogIntegralSeries : Continuous unoffsetLogIntegralSeries :=
  continuous_iff_continuousAt.mpr fun y ↦ (hasDerivAt_unoffsetLogIntegralSeries y).continuousAt

/-- The **unoffset logarithmic integral**
`li x = γ + log |log x| + ∑' n, (log x) ^ (n + 1) / ((n + 1) * (n + 1)!)`.

In Mathlib, `Real.log` satisfies `Real.log (-y) = Real.log y`, so `Real.log (Real.log x)` equals
`log |log x|` for every `x > 0` with `x ≠ 1`. At `x = 1`, where `log x = 0`, the definition takes
a junk value. For `0 < x < 1` it equals `∫ t in 0..x, (log t)⁻¹`, and for `x > 1` it is the
Cauchy principal value `lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹)`
and satisfies `Li x = li x - li 2`. -/
noncomputable def unoffsetLogIntegral (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log x) + unoffsetLogIntegralSeries (Real.log x)

/-- Defining equation of `TauCeti.Real.unoffsetLogIntegral`. -/
theorem unoffsetLogIntegral_def (x : ℝ) :
    unoffsetLogIntegral x =
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        unoffsetLogIntegralSeries (Real.log x) := (rfl)

/-- The unoffset logarithmic integral has derivative `(log x)⁻¹` for `x > 0`, `x ≠ 1`. -/
theorem hasDerivAt_unoffsetLogIntegral {x : ℝ} (hx₀ : 0 < x) (hx₁ : x ≠ 1) :
    HasDerivAt unoffsetLogIntegral (Real.log x)⁻¹ x := by
  have hlog_ne : Real.log x ≠ 0 := Real.log_ne_zero.mpr ⟨hx₀.ne', hx₁, by linarith⟩
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx₀.ne'
  have h1 : HasDerivAt (fun t : ℝ ↦ Real.eulerMascheroniConstant + Real.log (Real.log t))
      (x⁻¹ / Real.log x) x := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((Real.hasDerivAt_log hlog_ne).comp x hlog).const_add Real.eulerMascheroniConstant
  have h2 := (hasDerivAt_unoffsetLogIntegralSeries (Real.log x)).comp x hlog
  simp only [Function.update_of_ne hlog_ne, Real.exp_log hx₀] at h2
  refine (h1.add h2).congr_deriv ?_
  field_simp [hx₀.ne', hlog_ne]
  ring

/-- The unoffset logarithmic integral is differentiable on `(0, 1)`. -/
theorem differentiableOn_unoffsetLogIntegral_Ioo :
    DifferentiableOn ℝ unoffsetLogIntegral (Ioo 0 1) :=
  fun _ hx ↦ (hasDerivAt_unoffsetLogIntegral hx.1 hx.2.ne).differentiableAt.differentiableWithinAt

/-- The unoffset logarithmic integral is differentiable on `(1, ∞)`. -/
theorem differentiableOn_unoffsetLogIntegral_Ioi :
    DifferentiableOn ℝ unoffsetLogIntegral (Ioi 1) :=
  fun _ hx ↦
    (hasDerivAt_unoffsetLogIntegral (zero_lt_one.trans hx)
      hx.ne').differentiableAt.differentiableWithinAt

/-- The unoffset logarithmic integral is continuous on `(0, 1)`. -/
theorem continuousOn_unoffsetLogIntegral_Ioo : ContinuousOn unoffsetLogIntegral (Ioo 0 1) :=
  differentiableOn_unoffsetLogIntegral_Ioo.continuousOn

/-- The unoffset logarithmic integral is continuous on `(1, ∞)`. -/
theorem continuousOn_unoffsetLogIntegral_Ioi : ContinuousOn unoffsetLogIntegral (Ioi 1) :=
  differentiableOn_unoffsetLogIntegral_Ioi.continuousOn

/-! ### Behaviour as `x → 0⁺` -/

/-- For `0 < x < 1`, `li x = γ + x log (-log x) + ∫ t in 0..(-log x), log t * e^{-t}`. -/
theorem unoffsetLogIntegral_eq_add_mul_log_add_integral_log_mul_exp_neg
    {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    unoffsetLogIntegral x = Real.eulerMascheroniConstant + x * Real.log (-Real.log x) +
      ∫ t in (0 : ℝ)..(-Real.log x), Real.log t * Real.exp (-t) := by
  set z : ℝ := -Real.log x
  have hz : 0 < z := neg_pos.mpr (Real.log_neg hx₀ hx₁)
  have htsum := Real.integral_one_sub_exp_neg_div_eq z
  have hibp := Real.integral_one_sub_exp_neg_div_eq_sub_integral hz.le
  have hexp : Real.exp (-z) = x := by simp [z, Real.exp_log hx₀]
  rw [unoffsetLogIntegral_def, unoffsetLogIntegralSeries_def]
  have hlogabs : Real.log (Real.log x) = Real.log z := by
    rw [← Real.log_neg_eq_log]
  rw [hlogabs, show Real.log x = -z by simp [z], ← neg_neg (∑' n : ℕ, _), ← htsum, hibp, hexp]
  ring

/-- `li x → 0` as `x → 0⁺`. -/
theorem tendsto_unoffsetLogIntegral_nhdsGT_zero :
    Tendsto unoffsetLogIntegral (𝓝[>] 0) (𝓝 0) := by
  have hz_atTop : Tendsto (fun x : ℝ ↦ -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hint : Tendsto (fun z : ℝ ↦ ∫ t in (0 : ℝ)..z, Real.log t * Real.exp (-t)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    rw [Real.eulerMascheroniConstant_eq_neg_integral_log, neg_neg]
    exact intervalIntegral_tendsto_integral_Ioi 0 Real.integrableOn_Ioi_log_mul_exp_neg tendsto_id
  have hxexp : Tendsto (fun x : ℝ ↦ x * Real.log (-Real.log x)) (𝓝[>] 0) (𝓝 0) := by
    refine (Real.tendsto_exp_neg_mul_log_atTop.comp hz_atTop).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [Real.exp_log hx]
  have hsum : Tendsto (fun x : ℝ ↦ Real.eulerMascheroniConstant +
      x * Real.log (-Real.log x) + ∫ t in (0 : ℝ)..(-Real.log x), Real.log t * Real.exp (-t))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 := ((tendsto_const_nhds (x := Real.eulerMascheroniConstant)).add hxexp).add
      (hint.comp hz_atTop)
    simpa [add_assoc] using h1
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  exact (unoffsetLogIntegral_eq_add_mul_log_add_integral_log_mul_exp_neg hx.1 hx.2).symm

/-! ### Principal value and comparison with the offset logarithmic integral -/

/-- For `0 < x < 1`, `li x = ∫ t in 0..x, (log t)⁻¹`. -/
theorem unoffsetLogIntegral_eq_integral {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    unoffsetLogIntegral x = ∫ t in (0 : ℝ)..x, (Real.log t)⁻¹ := by
  have hderiv : ∀ t ∈ Ioo 0 x, HasDerivAt unoffsetLogIntegral (Real.log t)⁻¹ t :=
    fun t ht ↦ hasDerivAt_unoffsetLogIntegral ht.1 (ht.2.trans hx₁).ne
  have hint := Real.intervalIntegrable_inv_log_of_Ico hx₀.le hx₁
  have hlimx : Tendsto unoffsetLogIntegral (𝓝[<] x) (𝓝 (unoffsetLogIntegral x)) :=
    (hasDerivAt_unoffsetLogIntegral hx₀ hx₁.ne).continuousAt.continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx₀ hderiv hint
    tendsto_unoffsetLogIntegral_nhdsGT_zero hlimx
  linarith

/-- Symmetric cancellation of the logarithmic singularity at `1`:
`li (1 + ε) - li (1 - ε) → 0` as `ε → 0⁺`. -/
theorem tendsto_unoffsetLogIntegral_add_sub_sub :
    Tendsto (fun ε : ℝ ↦ unoffsetLogIntegral (1 + ε) - unoffsetLogIntegral (1 - ε))
      (𝓝[>] 0) (𝓝 0) := by
  have hS_cont : ContinuousAt unoffsetLogIntegralSeries 0 :=
    continuous_unoffsetLogIntegralSeries.continuousAt
  have hlog_add : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : ContinuousAt (fun ε : ℝ ↦ Real.log (1 + ε)) 0 := by fun_prop (disch := norm_num)
    simpa using h1.tendsto.mono_left nhdsWithin_le_nhds
  have hlog_sub : Tendsto (fun ε : ℝ ↦ Real.log (1 - ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : ContinuousAt (fun ε : ℝ ↦ Real.log (1 - ε)) 0 := by fun_prop (disch := norm_num)
    simpa using h1.tendsto.mono_left nhdsWithin_le_nhds
  have hS_diff : Tendsto (fun ε : ℝ ↦ unoffsetLogIntegralSeries (Real.log (1 + ε)) -
      unoffsetLogIntegralSeries (Real.log (1 - ε))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hS_cont.tendsto.comp hlog_add).sub (hS_cont.tendsto.comp hlog_sub)
  have hlogratio : Tendsto (fun ε : ℝ ↦ Real.log (Real.log (1 + ε) / (-Real.log (1 - ε))))
      (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp Real.tendsto_log_one_add_div_neg_log_one_sub
  have hsum := hlogratio.add hS_diff
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
  have hp : 0 < Real.log (1 + ε) := Real.log_pos (by linarith [hε.1])
  have hn : 0 < -Real.log (1 - ε) :=
    neg_pos.mpr (Real.log_neg (by linarith [hε.2]) (by linarith [hε.1]))
  rw [unoffsetLogIntegral_def, unoffsetLogIntegral_def]
  have hld : Real.log (Real.log (1 + ε)) - Real.log (Real.log (1 - ε)) =
      Real.log (Real.log (1 + ε) / (-Real.log (1 - ε))) := by
    rw [Real.log_div hp.ne' hn.ne', Real.log_neg_eq_log]
  linarith

/-- **Cauchy principal value for `li x`** (`x > 1`):
`lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹) = li x`. -/
theorem tendsto_principalValue_inv_log {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) +
        ∫ t in (1 + ε)..x, (Real.log t)⁻¹)
      (𝓝[>] 0) (𝓝 (unoffsetLogIntegral x)) := by
  have hsub :=
    (tendsto_const_nhds (x := unoffsetLogIntegral x)).sub tendsto_unoffsetLogIntegral_add_sub_sub
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one (sub_pos.mpr hx))] with ε hε
  have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
  have hεx : 1 + ε < x := by linarith [hε.2.trans_le (min_le_right _ _)]
  have hleft : ∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹ = unoffsetLogIntegral (1 - ε) :=
    (unoffsetLogIntegral_eq_integral (by linarith [hε1]) (by linarith [hε.1])).symm
  have hright : ∫ t in (1 + ε)..x, (Real.log t)⁻¹ =
      unoffsetLogIntegral x - unoffsetLogIntegral (1 + ε) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
    · intro t ht
      rw [uIcc_of_le hεx.le] at ht
      exact hasDerivAt_unoffsetLogIntegral (by linarith [ht.1, hε.1]) (by linarith [ht.1, hε.1])
    · simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith [hε.1]) hx
  rw [hleft, hright]
  ring

/-- **The offset relation**: `Li x = li x - li 2` for every `x > 1`. -/
theorem logIntegral_eq_unoffsetLogIntegral_sub {x : ℝ} (hx : 1 < x) :
    logIntegral x = unoffsetLogIntegral x - unoffsetLogIntegral 2 := by
  rw [logIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
  · intro t ht
    have ht1 : 1 < t := ordConnected_Ioi.uIcc_subset one_lt_two hx ht
    exact hasDerivAt_unoffsetLogIntegral (zero_lt_one.trans ht1) ht1.ne'
  · simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 one_lt_two hx

/-- For every `x > 1`, `li x = Li x + li 2`. -/
theorem unoffsetLogIntegral_eq_logIntegral_add {x : ℝ} (hx : 1 < x) :
    unoffsetLogIntegral x = logIntegral x + unoffsetLogIntegral 2 := by
  linarith [logIntegral_eq_unoffsetLogIntegral_sub hx]

/-! ### Monotonicity, limits, and Soldner's constant -/

/-- `li` is strictly decreasing on `(0, 1)`. -/
theorem strictAntiOn_unoffsetLogIntegral_Ioo : StrictAntiOn unoffsetLogIntegral (Ioo 0 1) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (f' := fun t ↦ (Real.log t)⁻¹) (convex_Ioo 0 1)
    continuousOn_unoffsetLogIntegral_Ioo (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [interior_Ioo] at hx
    exact (hasDerivAt_unoffsetLogIntegral hx.1 hx.2.ne).hasDerivWithinAt
  · rw [interior_Ioo] at hx
    exact inv_lt_zero.mpr (Real.log_neg hx.1 hx.2)

/-- For every `x ∈ (0, 1)`, `li x < 0`. -/
theorem unoffsetLogIntegral_neg_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    unoffsetLogIntegral x < 0 := by
  have hx2 : x / 2 ∈ Ioo (0 : ℝ) 1 := ⟨half_pos hx.1, by linarith [hx.2]⟩
  have hlt : unoffsetLogIntegral x < unoffsetLogIntegral (x / 2) :=
    strictAntiOn_unoffsetLogIntegral_Ioo hx2 hx (by linarith [hx.1])
  have hle : unoffsetLogIntegral (x / 2) ≤ 0 := by
    refine ge_of_tendsto tendsto_unoffsetLogIntegral_nhdsGT_zero ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos hx.1)] with y hy
    exact (strictAntiOn_unoffsetLogIntegral_Ioo ⟨hy.1, by linarith [hy.2, hx.2]⟩ hx2 hy.2).le
  exact hlt.trans_le hle

/-- `li` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_unoffsetLogIntegral_Ioi : StrictMonoOn unoffsetLogIntegral (Ioi 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun t ↦ (Real.log t)⁻¹) (convex_Ioi 1)
    continuousOn_unoffsetLogIntegral_Ioi (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_unoffsetLogIntegral (zero_lt_one.trans hx) hx.ne').hasDerivWithinAt
  · rw [interior_Ioi] at hx
    exact inv_pos.mpr (Real.log_pos hx)

/-- `li x → -∞` as `x → 1` (`x ≠ 1`). -/
theorem tendsto_unoffsetLogIntegral_nhdsNE_one :
    Tendsto unoffsetLogIntegral (𝓝[≠] 1) atBot := by
  have hloglog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) (𝓝[≠] 1) atBot :=
    Real.tendsto_log_nhdsNE_one_nhdsNE_zero |> Real.tendsto_log_nhdsNE_zero.comp
  have hS : Tendsto (fun x : ℝ ↦ unoffsetLogIntegralSeries (Real.log x)) (𝓝[≠] 1) (𝓝 0) := by
    have hS0 : ContinuousAt unoffsetLogIntegralSeries 0 :=
      continuous_unoffsetLogIntegralSeries.continuousAt
    simpa [unoffsetLogIntegralSeries_def, Function.comp_def] using
      hS0.tendsto.comp (Real.tendsto_log_nhdsNE_one_nhdsNE_zero.mono_right nhdsWithin_le_nhds)
  have hsum : Tendsto (fun x : ℝ ↦ (Real.eulerMascheroniConstant +
      unoffsetLogIntegralSeries (Real.log x)) + Real.log (Real.log x)) (𝓝[≠] 1) atBot :=
    Tendsto.add_atBot ((tendsto_const_nhds (x := Real.eulerMascheroniConstant)).add hS) hloglog
  refine hsum.congr fun x ↦ ?_
  rw [unoffsetLogIntegral_def]
  ring

/-- `li x → -∞` as `x → 1⁻`. -/
theorem tendsto_unoffsetLogIntegral_nhdsLT_one :
    Tendsto unoffsetLogIntegral (𝓝[<] 1) atBot :=
  tendsto_unoffsetLogIntegral_nhdsNE_one.mono_left (nhdsWithin_mono _ fun _ hx ↦ hx.ne)

/-- `li x → -∞` as `x → 1⁺`. -/
theorem tendsto_unoffsetLogIntegral_nhdsGT_one :
    Tendsto unoffsetLogIntegral (𝓝[>] 1) atBot :=
  tendsto_unoffsetLogIntegral_nhdsNE_one.mono_left (nhdsWithin_mono _ fun _ hx ↦ hx.ne')

/-- `li x → +∞` as `x → ∞`. -/
theorem tendsto_unoffsetLogIntegral_atTop :
    Tendsto unoffsetLogIntegral atTop atTop := by
  have hLi : Tendsto logIntegral atTop atTop := by
    have hhalf : Tendsto (fun x : ℝ ↦ (1 / 2 : ℝ) * (x / Real.log x)) atTop atTop :=
      tendsto_div_log_atTop.const_mul_atTop (by norm_num)
    refine tendsto_atTop_mono' atTop ?_ hhalf
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    calc (1 / 2 : ℝ) * (x / Real.log x)
        = (x / 2) / Real.log x := by ring
      _ ≤ (x - 2) / Real.log x := by gcongr; linarith
      _ ≤ logIntegral x := le_logIntegral (by linarith)
  have hadd : Tendsto (fun x : ℝ ↦ logIntegral x + unoffsetLogIntegral 2) atTop atTop :=
    hLi.atTop_add tendsto_const_nhds
  refine hadd.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (unoffsetLogIntegral_eq_logIntegral_add hx).symm

/-- **Soldner's constant**: `li` has a unique zero in `(1, ∞)`. -/
theorem existsUnique_unoffsetLogIntegral_eq_zero :
    ∃! μ ∈ Ioi (1 : ℝ), unoffsetLogIntegral μ = 0 := by
  obtain ⟨a, ha1, ha0⟩ : ∃ a ∈ Ioi (1 : ℝ), unoffsetLogIntegral a < 0 := by
    have hev := (tendsto_unoffsetLogIntegral_nhdsGT_one.eventually (eventually_lt_atBot 0)).and
      self_mem_nhdsWithin
    obtain ⟨a, ha0, ha1⟩ := hev.exists
    exact ⟨a, ha1, ha0⟩
  obtain ⟨b, hb_gt, hb0⟩ : ∃ b > a, 0 < unoffsetLogIntegral b := by
    have hev := (tendsto_unoffsetLogIntegral_atTop.eventually (eventually_gt_atTop 0)).and
      (eventually_gt_atTop a)
    obtain ⟨b, hb0, hba⟩ := hev.exists
    exact ⟨b, hba, hb0⟩
  have hab : a ≤ b := hb_gt.le
  have hcont : ContinuousOn unoffsetLogIntegral (Icc a b) :=
    continuousOn_unoffsetLogIntegral_Ioi.mono (Icc_subset_Ioi_iff hab |>.mpr ha1)
  obtain ⟨μ, hμ, hμ0⟩ := intermediate_value_Icc hab hcont (mem_Icc.mpr ⟨ha0.le, hb0.le⟩)
  refine ⟨μ, ⟨ha1.trans_le hμ.1, hμ0⟩, fun ν hν ↦ ?_⟩
  rcases lt_trichotomy ν μ with hlt | rfl | hgt
  · exact absurd (strictMonoOn_unoffsetLogIntegral_Ioi hν.1 (ha1.trans_le hμ.1) hlt)
      (by linarith [hν.2, hμ0])
  · rfl
  · exact absurd (strictMonoOn_unoffsetLogIntegral_Ioi (ha1.trans_le hμ.1) hν.1 hgt)
      (by linarith [hν.2, hμ0])

/-! ### Asymptotic expansion -/

/-- **Asymptotic expansion of `li x`**: for every `n : ℕ`,
`li x = (x / log x) * ∑ k < n, k! / (log x) ^ k + O(x / (log x) ^ (n + 1))` as `x → ∞`. -/
theorem isBigO_unoffsetLogIntegral_sub_sum (n : ℕ) :
    (fun x : ℝ ↦ unoffsetLogIntegral x -
        (x / Real.log x) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log x ^ k) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
  let C : ℝ := unoffsetLogIntegral 2 -
    (2 / Real.log 2) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log 2 ^ k
  have hconst_tendsto : Tendsto (fun x : ℝ ↦ Real.log x ^ (n + 1) / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 (n + 1) one_ne_zero
  have hconst : (fun _ : ℝ ↦ C) =O[atTop] fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
    refine (isLittleO_iff_tendsto' ?_).mpr ?_ |>.isBigO
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx h0
      exact absurd h0 (div_pos (zero_lt_one.trans hx) (pow_pos (Real.log_pos hx) _)).ne'
    · have hmul : Tendsto (fun x : ℝ ↦ C * (Real.log x ^ (n + 1) / x)) atTop (𝓝 0) := by
        simpa using hconst_tendsto.const_mul C
      refine hmul.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _
      rw [div_div_eq_mul_div]
      ring
  have hrem : (fun x : ℝ ↦ (n ! : ℝ) * ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (n + 1) :=
    (isBigO_integral_inv_log_pow_succ n).const_mul_left (n ! : ℝ)
  refine (hconst.add hrem).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx1 : 1 < x := one_lt_two.trans_le hx
  rw [unoffsetLogIntegral_eq_logIntegral_add hx1, logIntegral_eq_sub_add_integral n hx1]
  dsimp only [C]
  ring

/-- `li x ~ Li x` as `x → ∞`. -/
theorem unoffsetLogIntegral_isEquivalent_logIntegral :
    unoffsetLogIntegral ~[atTop] logIntegral := by
  have hdiff : (fun x : ℝ ↦ unoffsetLogIntegral x - logIntegral x) =o[atTop] logIntegral := by
    have hconst : (fun _ : ℝ ↦ unoffsetLogIntegral 2) =o[atTop] fun x : ℝ ↦ x / Real.log x :=
      isLittleO_const_div_log (unoffsetLogIntegral 2)
    have hli := hconst.trans_isEquivalent logIntegral_isEquivalent_div_log.symm
    refine hli.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [unoffsetLogIntegral_eq_logIntegral_add hx]
    ring
  exact hdiff.isEquivalent

/-- `li x ~ x / log x` as `x → ∞`. -/
theorem unoffsetLogIntegral_isEquivalent_div_log :
    unoffsetLogIntegral ~[atTop] fun x : ℝ ↦ x / Real.log x :=
  unoffsetLogIntegral_isEquivalent_logIntegral.trans logIntegral_isEquivalent_div_log

end TauCeti.Real
