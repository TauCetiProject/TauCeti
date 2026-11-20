/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.RingTheory.PowerSeries.Entire.Taylor
public import TauCeti.RingTheory.PowerSeries.ExponentialSeries.Basic
public import TauCeti.RingTheory.PowerSeries.Radius

import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Analytic evaluation of exponential power series

Analytic sum `TauCeti.eFun a z = ∑' n, a n * z ^ n / n!`, matching
`PowerSeries.evalAt (ePowerSeries a) z`. When `ePowerSeries a` is entire, `eFun a` converges
everywhere, respects addition, subtraction, and Hurwitz convolution, and satisfies
`deriv (eFun a) = eFun (fun n ↦ a (n + 1))` and `iteratedDeriv k (eFun a) 0 = a k`. Over an
`RCLike` field, a geometric bound `‖a n‖ ≤ C ^ (n + 1)` ensures `ePowerSeries a` is entire.

## Main definitions

* `TauCeti.eFun`: the analytic sum `z ↦ ∑' n, aₙ * zⁿ / n!`.

## Main results

* `TauCeti.hasFPowerSeriesOnBall_eFun`, `TauCeti.deriv_eFun`, `TauCeti.iteratedDeriv_eFun_zero`,
  `TauCeti.eFun_hurwitzMul`: analytic calculus of `eFun` for entire series.
* `TauCeti.isEntire_ePowerSeries_of_norm_le`: geometric growth implies entireness.

## References

* F. Beukers, *E-functions and G-functions*, Arizona Winter School, 2008, §3.1–3.2.
-/

public section

open PowerSeries
open scoped ENNReal

namespace TauCeti

/-- The analytic sum `eFun a z = ∑' n, a n * z ^ n / n!` attached to `a : ℕ → K`.
Outside the domain of convergence it takes the junk value of `tsum`. -/
noncomputable def eFun {K : Type*} [DivisionRing K] [TopologicalSpace K] (a : ℕ → K) (z : K) : K :=
  ∑' n, a n * z ^ n / n.factorial

section Field

variable {K : Type*} [Field K] [TopologicalSpace K]

/-- Unfolding `eFun`. -/
theorem eFun_def (a : ℕ → K) (z : K) : eFun a z = ∑' n, a n * z ^ n / n.factorial := (rfl)

/-- `eFun a z` is `PowerSeries.evalAt (ePowerSeries a) z`. -/
theorem evalAt_ePowerSeries (a : ℕ → K) (z : K) : (ePowerSeries a).evalAt z = eFun a z := by
  rw [evalAt_def, eFun_def]
  exact tsum_congr fun n ↦ by rw [coeff_ePowerSeries, smul_eq_mul, div_mul_eq_mul_div]

/-- The zero sequence evaluates to `0` at every point. -/
@[simp] theorem eFun_zero (z : K) : eFun (0 : ℕ → K) z = 0 := by simp [eFun_def]

/-- At `z = 0`, `eFun a 0 = a 0` unconditionally, since all higher terms vanish identically. -/
@[simp] theorem eFun_apply_zero (a : ℕ → K) : eFun a 0 = a 0 := by
  rw [eFun_def, tsum_eq_single 0 (fun _ hn ↦ by simp [zero_pow hn])]; simp

/-- A sequence supported at index `k` sums to the single term `c * z ^ k / k!`. -/
@[simp] theorem eFun_single (k : ℕ) (c z : K) :
    eFun (Pi.single k c) z = c * z ^ k / k.factorial := by
  rw [eFun_def, tsum_eq_single k (fun _ hn ↦ by simp [Pi.single_eq_of_ne hn])]; simp

/-- Pointwise negation of `eFun`. -/
theorem eFun_neg [IsTopologicalAddGroup K] [T2Space K] (a : ℕ → K) (z : K) :
    eFun (-a) z = -eFun a z := by
  rw [← evalAt_ePowerSeries, ePowerSeries_neg, evalAt_neg, evalAt_ePowerSeries]

end Field

/-- Over `ℂ`, constant-one data sum to `Complex.exp`. -/
@[simp] theorem eFun_one_complex (z : ℂ) : eFun (fun _ ↦ (1 : ℂ)) z = Complex.exp z := by
  simp [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div, eFun_def]

section Entire

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] {a b : ℕ → K}

/-- When `ePowerSeries a` is entire, the defining series of `eFun a z` converges to `eFun a z`. -/
theorem hasSum_eFun (ha : (ePowerSeries a).IsEntire) (z : K) :
    HasSum (fun n ↦ a n * z ^ n / n.factorial) (eFun a z) := by
  rw [← evalAt_ePowerSeries]
  simpa only [coeff_ePowerSeries, smul_eq_mul, div_mul_eq_mul_div] using ha.hasSum_evalAt z

/-- When `ePowerSeries a` is entire, its terms at `z` are summable. -/
theorem summable_eFun (ha : (ePowerSeries a).IsEntire) (z : K) :
    Summable fun n ↦ a n * z ^ n / n.factorial := (hasSum_eFun ha z).summable

/-- Pointwise addition of `eFun` for entire factorial-divided series. -/
theorem eFun_add (ha : (ePowerSeries a).IsEntire) (hb : (ePowerSeries b).IsEntire) (z : K) :
    eFun (a + b) z = eFun a z + eFun b z := by
  rw [← evalAt_ePowerSeries, ePowerSeries_add, ha.evalAt_add hb, evalAt_ePowerSeries,
    evalAt_ePowerSeries]

/-- Pointwise subtraction of `eFun` for entire factorial-divided series. -/
theorem eFun_sub (ha : (ePowerSeries a).IsEntire) (hb : (ePowerSeries b).IsEntire) (z : K) :
    eFun (a - b) z = eFun a z - eFun b z := by
  rw [← evalAt_ePowerSeries, ePowerSeries_sub, ha.evalAt_sub hb, evalAt_ePowerSeries,
    evalAt_ePowerSeries]

/-- If `ePowerSeries a` is entire, `eFun a` admits a formal power series of infinite radius at
every center `z`, given by the Hasse derivatives of `ePowerSeries a` evaluated at `z`. -/
theorem hasFPowerSeriesOnBall_eFun_at (ha : (ePowerSeries a).IsEntire) (z : K) :
    HasFPowerSeriesOnBall (eFun a)
      (FormalMultilinearSeries.ofScalars K fun k ↦
        (PowerSeries.hasseDeriv k (ePowerSeries a)).evalAt z) z ⊤ := by
  have hrad : (FormalMultilinearSeries.ofScalars K fun k ↦
      coeff k ((ePowerSeries a).taylor z)).radius = ⊤ := by
    rw [← PowerSeries.radius_eq_radius_ofScalars, radius_eq_top_iff]; exact ha.taylor z
  refine ⟨by simpa [coeff_taylor] using hrad.ge, ENNReal.zero_lt_top, fun {y} _ ↦ ?_⟩
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, evalAt_ePowerSeries,
    add_comm z y] using ha.hasSum_taylor z y

/-- If `ePowerSeries a` is entire, `eFun a` is analytic on all of `K`. -/
theorem analyticOnNhd_eFun (ha : (ePowerSeries a).IsEntire) :
    AnalyticOnNhd K (eFun a) Set.univ := fun z _ ↦ (hasFPowerSeriesOnBall_eFun_at ha z).analyticAt

section CharZero

variable [CharZero K]

/-- Pointwise multiplication of `eFun` corresponds to `hurwitzMul` when both series are entire. -/
theorem eFun_hurwitzMul (ha : (ePowerSeries a).IsEntire) (hb : (ePowerSeries b).IsEntire) (z : K) :
    eFun (hurwitzMul a b) z = eFun a z * eFun b z := by
  rw [← evalAt_ePowerSeries, ePowerSeries_hurwitzMul, ha.evalAt_mul hb, evalAt_ePowerSeries,
    evalAt_ePowerSeries]

/-- If `ePowerSeries a` is entire, `eFun a` has formal power series
`∑ (aₙ / n!) zⁿ` on the whole space (`r = ⊤`) centered at `0`. -/
theorem hasFPowerSeriesOnBall_eFun (ha : (ePowerSeries a).IsEntire) :
    HasFPowerSeriesOnBall (eFun a)
      (FormalMultilinearSeries.ofScalars K fun k ↦ a k / k.factorial) 0 ⊤ := by
  convert hasFPowerSeriesOnBall_eFun_at ha 0 using 2; ext k
  simp [hasseDeriv_ePowerSeries, div_eq_inv_mul]

/-- Termwise derivative of `eFun a` at `z`: shifting `a` differentiates `eFun a`. -/
theorem hasDerivAt_eFun (ha : (ePowerSeries a).IsEntire) (z : K) :
    HasDerivAt (eFun a) (eFun (fun n ↦ a (n + 1)) z) z := by
  have hd := (hasFPowerSeriesOnBall_eFun_at ha z).hasFPowerSeriesAt.hasDerivAt
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, pow_one, mul_one, smul_eq_mul,
    hasseDeriv_one_apply, derivative_ePowerSeries, evalAt_ePowerSeries] using hd

/-- If `ePowerSeries a` is entire, `eFun a` is everywhere differentiable. -/
theorem differentiable_eFun (ha : (ePowerSeries a).IsEntire) : Differentiable K (eFun a) :=
  fun z ↦ (hasDerivAt_eFun ha z).differentiableAt

/-- Derivative of `eFun a`: `deriv (eFun a) = eFun (fun n ↦ a (n + 1))`. -/
theorem deriv_eFun (ha : (ePowerSeries a).IsEntire) :
    deriv (eFun a) = eFun fun n ↦ a (n + 1) := funext fun z ↦ (hasDerivAt_eFun ha z).deriv

/-- Iterated derivatives of `eFun a`: `iteratedDeriv k (eFun a) = eFun (fun n ↦ a (n + k))`. -/
theorem iteratedDeriv_eFun (ha : (ePowerSeries a).IsEntire) (k : ℕ) :
    iteratedDeriv k (eFun a) = eFun fun n ↦ a (n + k) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have ha' : (ePowerSeries fun n ↦ a (n + 1)).IsEntire := by
      rw [← derivative_ePowerSeries]; exact ha.derivative
    rw [iteratedDeriv_succ', deriv_eFun ha, ih ha']; simp only [add_assoc]

/-- The `k`-th derivative of `eFun a` at `0` recovers `a k`. -/
@[simp] theorem iteratedDeriv_eFun_zero (ha : (ePowerSeries a).IsEntire) (k : ℕ) :
    iteratedDeriv k (eFun a) 0 = a k := by
  rw [iteratedDeriv_eFun ha k, eFun_apply_zero, zero_add]

end CharZero

end Entire

section GeometricGrowth

/-- Over `ℝ` or `ℂ` (`RCLike`), any sequence `a` with geometric bound `‖a n‖ ≤ C ^ (n + 1)` gives
an entire factorial-divided formal power series `ePowerSeries a`. -/
theorem isEntire_ePowerSeries_of_norm_le {K : Type*} [RCLike K] {a : ℕ → K} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) : (ePowerSeries a).IsEntire := by
  refine isEntire_iff_forall_pos.mpr fun r hr ↦ (isRestricted_iff' r _).mpr ?_
  have hlim : Filter.Tendsto (fun n : ℕ ↦ C * ((C * r) ^ n / n.factorial))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((Real.summable_pow_div_factorial (C * r)).tendsto_atTop_zero).const_mul C
  refine squeeze_zero (fun _ ↦ by positivity) (fun n ↦ ?_) hlim
  rw [coeff_ePowerSeries, norm_div, RCLike.norm_natCast]
  calc ‖a n‖ / n.factorial * r ^ n
      ≤ C ^ (n + 1) / n.factorial * r ^ n := by gcongr; exact ha n
    _ = C * ((C * r) ^ n / n.factorial) := by rw [pow_succ', mul_pow]; ring

end GeometricGrowth

/-! ### Checks on small sequences -/

example (z : ℂ) : eFun (Pi.single 1 (1 : ℂ)) z = z := by simp
example (c z : ℂ) : eFun (Pi.single 0 c) z = c := by simp

end TauCeti
