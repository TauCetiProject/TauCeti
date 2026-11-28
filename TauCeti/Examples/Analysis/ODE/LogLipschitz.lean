/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.ODE.Gronwall.LogLipschitz
import Mathlib.Analysis.ODE.Transform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Checks for integral curves of log-Lipschitz fields

These computations fix the conventions of `TauCeti.Analysis.ODE.Gronwall.LogLipschitz`, where
the modulus is `ℓ(r) = r (1 - log r)` on `[0, 1]`.

* **Osgood's condition.** `∫₀¹ dr / ℓ(r) = ∞`: the function `r ↦ (r (1 - log r))⁻¹` is not
  integrable on `[0, 1]`, since `-log (1 - log r)` is an antiderivative that tends to `-∞` as
  `r → 0⁺` (`TauCeti.Examples.LogLipschitz.not_intervalIntegrable_inv_mul_one_sub_log`). This is
  what makes integral curves unique (`IsIntegralCurveOn.eqOn_Icc_of_logLipschitz`).
* **Non-uniqueness without it.** The field `x ↦ √|x|` on `ℝ` has the two integral curves `0` and
  `t ↦ t² / 4` from `0` (`TauCeti.Examples.LogLipschitz.isIntegralCurveOn_sq_div_four`), so it is
  not log-Lipschitz at small scales for any constant
  (`TauCeti.Examples.LogLipschitz.not_forall_dist_sqrt_abs_le`).
* **The Hölder exponent.** `r(t) = r₀ ^ exp (-C t)` solves `r' = -C r log r` with `r(0) = r₀`
  (`TauCeti.Examples.LogLipschitz.hasDerivAt_rpow_exp_neg_mul`). For `ρ = B / e`, the comparison
  equation `B' = C B (1 - log B)` behind `IsIntegralCurveOn.dist_le_exp_mul_dist_rpow` is
  `ρ' = -C ρ log ρ`, so the exponent `exp (-C t)` of the Hölder estimate is this one.
-/

public section

open Set Filter Real MeasureTheory Asymptotics
open scoped NNReal Topology Interval

namespace TauCeti.Examples.LogLipschitz

/-- **Osgood's condition for the log-Lipschitz modulus.** `∫₀¹ dr / (r (1 - log r)) = ∞`: the
reciprocal of `ℓ(r) = r (1 - log r)` is not integrable on `[0, 1]`. -/
theorem not_intervalIntegrable_inv_mul_one_sub_log :
    ¬IntervalIntegrable (fun r : ℝ ↦ (r * (1 - log r))⁻¹) volume 0 1 := by
  have hle : 𝓝[[[0, 1]] \ {0}] (0 : ℝ) ≤ 𝓝[>] 0 := nhdsWithin_mono _ fun r hr ↦
    lt_of_le_of_ne (by simpa using hr.1.1) (Ne.symm hr.2)
  -- On `(0, 1]` the function `log (1 - log r)` has derivative `-(r (1 - log r))⁻¹`.
  have hderiv : ∀ᶠ r in 𝓝[[[0, 1]] \ {0}] (0 : ℝ),
      HasDerivAt (fun r ↦ log (1 - log r)) (-(r * (1 - log r))⁻¹) r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : 0 < r := lt_of_le_of_ne (by simpa using hr.1.1) (Ne.symm hr.2)
    have hL : 0 < 1 - log r := by
      linarith [log_nonpos hr0.le (by simpa using hr.1.2 : r ≤ 1)]
    convert ((hasDerivAt_log hr0.ne').const_sub 1).log hL.ne' using 1
    rw [mul_inv]
    ring
  refine not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
    (f := fun r ↦ log (1 - log r)) zero_ne_one left_mem_uIcc
    (hderiv.mono fun r hr ↦ hr.differentiableAt) ?_ ?_
  · refine tendsto_norm_atTop_atTop.comp (tendsto_log_atTop.comp ?_)
    exact tendsto_atTop_add_const_left _ 1
      (tendsto_neg_atBot_atTop.comp (tendsto_log_nhdsGT_zero.mono_left hle))
  · exact ((isBigO_refl _ _).neg_left).congr' (hderiv.mono fun r hr ↦ hr.deriv.symm)
      EventuallyEq.rfl

/-- `t ↦ t² / 4` is an integral curve of `x ↦ √|x|` for `t ≥ 0`, starting at `0`. -/
theorem isIntegralCurveOn_sq_div_four :
    IsIntegralCurveOn (fun t : ℝ ↦ t ^ 2 / 4) (fun _ x ↦ √|x|) (Ici 0) := fun t ht ↦ by
  have h : √|t ^ 2 / 4| = t / 2 := by
    rw [show t ^ 2 / 4 = (t / 2) ^ 2 by ring, abs_of_nonneg (by positivity),
      sqrt_sq (by linarith [mem_Ici.1 ht])]
  beta_reduce
  rw [h]
  convert ((hasDerivAt_pow 2 t).div_const 4).hasDerivWithinAt using 1
  ring

/-- **Non-uniqueness for a non-Osgood field.** The field `x ↦ √|x|` has the two distinct integral
curves `0` and `t ↦ t² / 4` from `0`, so by `IsIntegralCurveOn.eqOn_Icc_of_logLipschitz` it is
not log-Lipschitz at small scales for any constant `C`. -/
theorem not_forall_dist_sqrt_abs_le (C : ℝ≥0) :
    ¬∀ p q : ℝ, dist p q ≤ 1 → dist √|p| √|q| ≤ C * (dist p q * (1 - log (dist p q))) := by
  intro hv
  have hzero : IsIntegralCurveOn (fun _ ↦ (0 : ℝ)) (fun _ x ↦ √|x|) (Icc 0 1) :=
    (isIntegralCurve_const fun _ ↦ by simp).isIntegralCurveOn _
  have h := (isIntegralCurveOn_sq_div_four.mono Icc_subset_Ici_self).eqOn_Icc_of_logLipschitz
    hzero (fun _ _ ↦ hv) (left_mem_Icc.2 zero_le_one) (by simp) (right_mem_Icc.2 zero_le_one)
  norm_num at h

/-- **The Hölder exponent.** `r(t) = r₀ ^ exp (-C t)` solves `r' = -C r log r`, with `r(0) = r₀`.
-/
theorem hasDerivAt_rpow_exp_neg_mul {r₀ : ℝ} (hr₀ : 0 < r₀) (C t : ℝ) :
    HasDerivAt (fun t ↦ r₀ ^ exp (-(C * t)))
      (-C * r₀ ^ exp (-(C * t)) * log (r₀ ^ exp (-(C * t)))) t := by
  have h0 : HasDerivAt (fun t ↦ -(C * t)) (-C) t := by
    convert ((hasDerivAt_id' t).const_mul C).neg using 1
    ring
  convert h0.exp.const_rpow hr₀ using 1
  rw [log_rpow hr₀]
  ring

end TauCeti.Examples.LogLipschitz
