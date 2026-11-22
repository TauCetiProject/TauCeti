/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Nat.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.LaplaceTransform.Truncated
import TauCeti.Analysis.SpecialFunctions.Log.Base
import TauCeti.Analysis.SpecialFunctions.Log.NatCastAdd

/-!
# Laplace integrals of exponential step functions

For a sequence `a : ℕ → ℂ`, this file collects elementary Laplace-integral and boundedness
properties of the exponential step function `t ↦ a ⌊exp t⌋₊`:

* on each step `[log n, log (n + 1)]`, `t ↦ a ⌊exp t⌋₊ * exp (-z * t)` is interval integrable
  (`TauCeti.intervalIntegrable_floor_exp_mul_cexp_neg_mul`) and integrates to
  `a n * ∫ x in n..n+1, x ^ (-z - 1)` (`TauCeti.intervalIntegral_floor_exp_mul_cexp_neg_mul`);
* on `[0, ∞)`, `t ↦ a ⌊exp t⌋₊` is bounded by `M` whenever `a` is bounded by `M` from `n = 1` on
  (`TauCeti.norm_floor_exp_le`);
* for an integer base `b` and `0 ≤ t`, `(if ⌊exp t⌋₊ = 0 then 0 else c (Nat.log b ⌊exp t⌋₊))`
  equals `c ⌊t / log b⌋₊` (`TauCeti.ite_floor_exp_natLog_eq`), identifying the `[0, ∞)` Laplace
  integral of the `b`-adic block step function with that of the uniform step function
  `t ↦ c ⌊t / log b⌋₊` (`TauCeti.integral_floor_exp_natLog_mul_cexp_neg_mul`).
-/

public section

open MeasureTheory Set
open scoped Complex Interval

namespace TauCeti

/-- **The Laplace integral over one step.** For `n ≠ 0`, the step function `t ↦ a ⌊exp t⌋₊`
equals `a n` on `(log n, log (n + 1))`, so its Laplace integral over `[log n, log (n + 1)]` is
`a n ∫ x in n..n+1, x ^ (-z - 1)`. -/
theorem intervalIntegral_floor_exp_mul_cexp_neg_mul (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    ∫ t in Real.log n..Real.log (n + 1), a ⌊Real.exp t⌋₊ * cexp (-z * t) =
      a n * ∫ x in (n : ℝ)..n + 1, (x : ℂ) ^ (-z - 1) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [intervalIntegral_ofReal_cpow_neg_sub_one hn' (by positivity),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_Ioo_of_le
    (Real.log_le_log hn' (by linarith)) fun t ht ↦ ?_
  rw [Real.floor_exp_eq_of_mem_Ioo ht]

/-- The step function `t ↦ a ⌊exp t⌋₊` times `exp (-z t)` is interval integrable on each step
`[log n, log (n + 1)]`, where for `n ≠ 0` it agrees with `a n exp (-z t)` away from the
endpoints (and for `n = 0` the interval is degenerate). -/
theorem intervalIntegrable_floor_exp_mul_cexp_neg_mul (a : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    IntervalIntegrable (fun t : ℝ ↦ a ⌊Real.exp t⌋₊ * cexp (-z * t)) volume
      (Real.log n) (Real.log (n + 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  refine ((by fun_prop : Continuous fun t : ℝ ↦ a n * cexp (-z * t)).intervalIntegrable
    _ _).congr_uIoo fun t ht ↦ ?_
  rw [uIoo_of_le (Real.log_le_log hn' (by linarith))] at ht
  simp only [Real.floor_exp_eq_of_mem_Ioo ht]

/-- For `0 ≤ t`, the step function `t ↦ a ⌊exp t⌋₊` only takes values `a n` with `1 ≤ n`, so it
is bounded by `M` when the coefficients are bounded by `M` from `n = 1` on. -/
theorem norm_floor_exp_le {a : ℕ → ℂ} {M : ℝ} (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M)
    {t : ℝ} (ht : t ∈ Ici 0) :
    ‖a ⌊Real.exp t⌋₊‖ ≤ M :=
  hbound _ (Nat.le_floor (by simpa using Real.one_le_exp (mem_Ici.mp ht)))

/-- For `0 ≤ t`, the `b`-adic block exponential step function agrees pointwise with the uniform step
function `t ↦ c ⌊t / log b⌋₊`. -/
theorem ite_floor_exp_natLog_eq {α : Type*} [Zero α] (b : ℕ) (c : ℕ → α) {t : ℝ} (ht : 0 ≤ t) :
    (if ⌊Real.exp t⌋₊ = 0 then (0 : α) else c (Nat.log b ⌊Real.exp t⌋₊)) =
      c ⌊t / Real.log b⌋₊ := by
  rw [ite_eq_right (Nat.floor_pos.mpr (Real.one_le_exp ht)).ne',
    ← Real.natFloor_logb_eq_natLog_natFloor b (Real.exp_nonneg t), Real.logb, Real.log_exp]

/-- **Integral-level bridge for `b`-adic block coefficients.** On `[0, ∞)`, the exponential-step
Laplace integral of `n ↦ if n = 0 then 0 else c (Nat.log b n)` agrees with the uniform-step
Laplace integral of `c` with step length `log b`. -/
theorem integral_floor_exp_natLog_mul_cexp_neg_mul (b : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    ∫ t in Ici (0 : ℝ),
        (if ⌊Real.exp t⌋₊ = 0 then (0 : ℂ) else c (Nat.log b ⌊Real.exp t⌋₊)) *
          cexp (-z * t) =
      ∫ t in Ici (0 : ℝ), c ⌊t / Real.log b⌋₊ * cexp (-z * t) := by
  refine setIntegral_congr_fun measurableSet_Ici fun t ht ↦ ?_
  rw [ite_floor_exp_natLog_eq b c ht]

end TauCeti
