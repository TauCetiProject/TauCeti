/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Positive divided differences of the real exponential

The divided difference of the exponential is the integral of the exponential along the segment
between its arguments. In particular it is strictly positive, including when the arguments
coincide. It is jointly real analytic, including on the diagonal. These divided differences
are the scalar coefficients in the derivative of the matrix exponential at a Hermitian matrix.

At base point `0`, `TauCeti.dslope_exp_zero_of_ne` identifies `dslope exp 0 u` with
`(exp u - 1) / u` away from `0`, so `(exp u - 1) / u` agrees almost everywhere with a continuous
function (`TauCeti.continuous_dslope_exp_zero`) and is interval integrable on every closed interval
(`Real.intervalIntegrable_exp_sub_one_div`), with Taylor series
`∑' n, u ^ n / (n + 1)!` (`Real.hasSum_dslope_exp_zero`, `Real.dslope_exp_zero_eq_tsum`). Termwise
integration and quantitative estimates for the resulting exponential-integral series live in
`TauCeti.Analysis.SpecialFunctions.Exp.ExpIntegralSeries`.
-/

public section

open Filter MeasureTheory
open scoped ContDiff Nat

namespace Real

/-- The divided difference of the exponential is its average along a segment. -/
theorem dslope_exp_eq_integral (a b : ℝ) :
    dslope exp a b = ∫ t in (0 : ℝ)..1, exp ((1 - t) * a + t * b) := by
  have heq (t : ℝ) : (1 - t) * a + t * b = a + t * (b - a) := by ring
  simp_rw [heq]
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (by fun_prop : ContinuousOn (fun t : ℝ ↦ exp (a + t * (b - a))) (Set.Icc 0 1))
    (fun t _ ↦ hasDerivAt_exp (a + t * (b - a)))
  simp only [smul_eq_mul, add_sub_cancel] at h
  by_cases hab : b = a
  · simp [hab]
  · rw [dslope_of_ne exp hab, slope_def_field, div_eq_iff (sub_ne_zero.mpr hab)]
    simpa only [mul_comm] using h.symm

/-- All divided differences of the real exponential are strictly positive. -/
theorem dslope_exp_pos (a b : ℝ) : 0 < dslope exp a b := by
  rw [dslope_exp_eq_integral]
  exact intervalIntegral.integral_pos (by norm_num) (by fun_prop)
    (fun t _ ↦ (exp_pos _).le) ⟨0, by simp, exp_pos _⟩

/-- Translating the real exponential divided difference to zero extracts the factor `exp a`. -/
theorem dslope_exp_eq_exp_mul_dslope_zero (a b : ℝ) :
    dslope exp a b = exp a * dslope exp 0 (b - a) := by
  rw [dslope_exp_eq_integral a b, dslope_exp_eq_integral 0 (b - a),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← exp_add]
  congr 1
  ring

/-- The real exponential divided difference is jointly smooth, including its removable
value at equal arguments. The regularity parameter also permits real analyticity. -/
theorem contDiff_dslope_exp (m : ℕ∞ω) :
    ContDiff ℝ m (fun p : ℝ × ℝ ↦ dslope exp p.1 p.2) := by
  have hz : ContDiff ℝ m (dslope exp 0) :=
    ((analyticOnNhd_rexp (u := Set.univ)).dslope 0).contDiff
  have h : ContDiff ℝ m (fun p : ℝ × ℝ ↦ exp p.1 * dslope exp 0 (p.2 - p.1)) :=
    (contDiff_fst.exp).mul (hz.comp (contDiff_snd.sub contDiff_fst))
  convert h using 1
  funext p
  exact dslope_exp_eq_exp_mul_dslope_zero p.1 p.2

end Real

namespace TauCeti

open _root_.Real

/-- Away from `0`, `dslope exp 0 u = (exp u - 1) / u`. -/
theorem dslope_exp_zero_of_ne {u : ℝ} (hu : u ≠ 0) :
    dslope exp 0 u = (exp u - 1) / u := by
  rw [dslope_of_ne exp hu, slope_def_field, exp_zero, sub_zero]

/-- `dslope exp 0` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_dslope_exp_zero : Continuous (dslope exp 0) :=
  (contDiff_dslope_exp 0).continuous.comp (continuous_const.prodMk continuous_id)

end TauCeti

namespace Real

/-- Power series for `dslope exp 0`: `∑' n, u ^ n / (n + 1)! = dslope exp 0 u` for all `u : ℝ`. -/
theorem hasSum_dslope_exp_zero (u : ℝ) :
    HasSum (fun n : ℕ ↦ u ^ n / ((n + 1)! : ℝ)) (dslope exp 0 u) := by
  by_cases hu : u = 0
  · subst hu
    rw [dslope_same, Real.deriv_exp, exp_zero]
    simpa using hasSum_single (0 : ℕ) (f := fun n : ℕ ↦ (0 : ℝ) ^ n / ((n + 1)! : ℝ))
      (fun n hn ↦ by simp [zero_pow hn])
  · have hsumm : Summable fun n : ℕ ↦ u ^ n / ((n + 1)! : ℝ) := by
      refine .of_norm_bounded (summable_pow_div_factorial |u|) fun n ↦ ?_
      simp only [norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
      gcongr
      exact Nat.le_succ n
    have hexp : HasSum (fun n : ℕ ↦ u ^ n / (n ! : ℝ)) (exp u) := by
      simpa [exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using
        (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) u)
    have hshift : HasSum (fun n : ℕ ↦ u ^ (n + 1) / ((n + 1)! : ℝ)) (exp u - 1) := by
      simpa [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).mpr hexp
    have heq : u * (∑' n : ℕ, u ^ n / ((n + 1)! : ℝ)) = exp u - 1 := by
      refine (hsumm.hasSum.mul_left u).unique ?_
      convert hshift using 1
      ext n
      rw [pow_succ']
      ring
    rw [TauCeti.dslope_exp_zero_of_ne hu, ← eq_div_of_mul_eq hu (mul_comm _ u ▸ heq)]
    exact hsumm.hasSum

/-- `tsum` form of `Real.hasSum_dslope_exp_zero`. -/
theorem dslope_exp_zero_eq_tsum (u : ℝ) :
    dslope exp 0 u = ∑' n : ℕ, u ^ n / ((n + 1)! : ℝ) :=
  (hasSum_dslope_exp_zero u).tsum_eq.symm

/-- The function `u ↦ (exp u - 1) / u` is interval integrable on every closed interval `[a, b]`
(including across `0`). -/
theorem intervalIntegrable_exp_sub_one_div (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ (exp u - 1) / u) volume a b := by
  refine (TauCeti.continuous_dslope_exp_zero.intervalIntegrable a b).congr_ae ?_
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with u hu
  exact TauCeti.dslope_exp_zero_of_ne hu

end Real
