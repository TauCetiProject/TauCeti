/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The entire function `cos √s`

The cosine is even, so `cos r` is a function of `r²`. This file defines that function,
`TauCeti.cosSqrt s = ∑ (-1)ⁿ sⁿ / (2n)!`, as the sum of a power series of infinite radius of
convergence. Thus `cosSqrt` is analytic on all of `ℝ`, `cosSqrt (r ^ 2) = cos r` for every real
`r`, and `cosSqrt s = cos √s` for `s ≥ 0`.

Composed with `x ↦ ‖x‖ ^ 2`, it is a way to see that radial functions built from `cos ‖x‖` are
smooth also at the origin of an inner product space, where the norm itself is not differentiable.
Its difference quotients `dslope cosSqrt 0` and `dslope (dslope cosSqrt 0) 0` are analytic too
(`AnalyticOnNhd.dslope`), and at `s = r²` they are `(cos r - 1) / r²` and
`((cos r - 1) / r² + 1 / 2) / r²` for `r ≠ 0`.

## Main definitions

* `TauCeti.cosSqrt`: the entire function `s ↦ ∑ (-1)ⁿ sⁿ / (2n)!`.

## Main results

* `TauCeti.cosSqrt_sq`: `cosSqrt (r ^ 2) = cos r`.
* `TauCeti.cosSqrt_of_nonneg`: `cosSqrt s = cos √s` for `s ≥ 0`.
* `TauCeti.analyticOnNhd_cosSqrt`, `TauCeti.contDiff_cosSqrt`: `cosSqrt` is analytic, hence
  smooth.
* `TauCeti.deriv_cosSqrt_zero`: `cosSqrt' 0 = -1 / 2`.
-/

public section

noncomputable section

open Filter Topology Set FormalMultilinearSeries
open scoped Nat

namespace TauCeti

/-- The entire function `cosSqrt s = ∑ (-1)ⁿ sⁿ / (2n)!`. It satisfies `cosSqrt (r ^ 2) = cos r`
(`TauCeti.cosSqrt_sq`), so it is `cos √s` for `s ≥ 0`, and it is analytic on all of `ℝ`
(`TauCeti.analyticOnNhd_cosSqrt`). -/
def cosSqrt (s : ℝ) : ℝ :=
  ∑' n : ℕ, (-1) ^ n * s ^ n / (2 * n)!

/-- `cosSqrt` is the sum of the power series with coefficients `(-1)ⁿ / (2n)!`. -/
theorem cosSqrt_eq_ofScalarsSum :
    cosSqrt = ofScalarsSum (E := ℝ) fun n ↦ (-1) ^ n / ((2 * n)! : ℝ) := by
  ext s
  rw [cosSqrt, ofScalars_sum_eq]
  congr 1 with n
  rw [smul_eq_mul]
  ring

/-- The power series of `cosSqrt` has infinite radius of convergence, by the ratio test. -/
theorem radius_ofScalars_cosSqrt :
    (ofScalars ℝ fun n ↦ (-1) ^ n / ((2 * n)! : ℝ)).radius = ⊤ := by
  refine ofScalars_radius_eq_top_of_tendsto _ _ (Eventually.of_forall fun n ↦ by positivity) ?_
  -- Consecutive coefficients have ratio `1 / ((2n + 1) (2n + 2)) ≤ 1 / (n + 1)`.
  have hratio (n : ℕ) : ‖(-1) ^ n.succ / ((2 * n.succ)! : ℝ)‖ / ‖(-1) ^ n / ((2 * n)! : ℝ)‖ =
      1 / ((2 * n + 1) * (2 * n + 2)) := by
    rw [show 2 * n.succ = (2 * n + 1).succ by omega, Nat.factorial_succ, Nat.factorial_succ]
    simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast]
    push_cast
    field_simp
    ring
  simp_rw [hratio]
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  gcongr
  nlinarith

/-- `cosSqrt` is the sum of its power series on the whole real line. -/
theorem hasFPowerSeriesOnBall_cosSqrt :
    HasFPowerSeriesOnBall cosSqrt (ofScalars ℝ fun n ↦ (-1) ^ n / ((2 * n)! : ℝ)) 0 ⊤ := by
  have h := (ofScalars ℝ fun n ↦ (-1) ^ n / ((2 * n)! : ℝ)).hasFPowerSeriesOnBall
    (by rw [radius_ofScalars_cosSqrt]; exact WithTop.top_pos)
  rw [radius_ofScalars_cosSqrt] at h
  rwa [cosSqrt_eq_ofScalarsSum]

/-- `cosSqrt` is analytic on the whole real line. -/
theorem analyticOnNhd_cosSqrt : AnalyticOnNhd ℝ cosSqrt univ :=
  fun _ _ ↦ hasFPowerSeriesOnBall_cosSqrt.analyticAt_of_mem (by simp)

/-- `cosSqrt` is smooth. -/
theorem contDiff_cosSqrt {n : WithTop ℕ∞} : ContDiff ℝ n cosSqrt :=
  analyticOnNhd_cosSqrt.contDiff

/-- `cosSqrt (r ^ 2) = cos r` for every real `r`. -/
@[simp]
theorem cosSqrt_sq (r : ℝ) : cosSqrt (r ^ 2) = Real.cos r := by
  rw [← (Real.hasSum_cos r).tsum_eq, cosSqrt]
  congr 1 with n
  rw [pow_mul]

/-- `cosSqrt s = cos √s` for `s ≥ 0`. -/
theorem cosSqrt_of_nonneg {s : ℝ} (hs : 0 ≤ s) : cosSqrt s = Real.cos √s := by
  rw [← cosSqrt_sq, Real.sq_sqrt hs]

/-- `cosSqrt 0 = 1`. -/
@[simp]
theorem cosSqrt_zero : cosSqrt 0 = 1 := by
  simpa using cosSqrt_sq 0

/-- The derivative of `cosSqrt` at `0` is `-1 / 2`, the coefficient of `r²` in `cos r`. -/
theorem deriv_cosSqrt_zero : deriv cosSqrt 0 = -1 / 2 := by
  rw [hasFPowerSeriesOnBall_cosSqrt.hasFPowerSeriesAt.deriv, ofScalars_apply_eq]
  norm_num

end TauCeti
