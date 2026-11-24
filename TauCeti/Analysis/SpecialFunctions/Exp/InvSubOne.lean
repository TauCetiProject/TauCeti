/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The function `(exp t - 1)⁻¹`

The function `g(t) = (exp t - 1)⁻¹` is the factor of the Bernoulli kernel `t / (exp t - 1)` that
carries its behaviour away from `0`. It satisfies the Riccati-type equation `g' = -(g + g²)`, it
decays like `exp (-t)` at `+∞`, and for `t > 0` it is the geometric series
`∑_{k ≥ 0} exp (-((k + 1) t))`.

## Main results

* `Real.exp_sub_one_ne_zero`: `exp t - 1 ≠ 0` for `t ≠ 0`, so `g` is defined away from `0`.
* `Real.hasDerivAt_inv_exp_sub_one`: `g' = -(g + g²)` away from `0`.
* `Real.isBigO_inv_exp_sub_one`: `g(t) = O(exp (-t))` as `t → ∞`.
* `Real.hasSum_exp_neg_nat_succ_mul`: `g(t) = ∑_{k ≥ 0} exp (-((k + 1) t))` for `t > 0`.
-/

public section

open Filter Asymptotics

namespace Real

/-- `exp t - 1` vanishes only at `t = 0`. -/
theorem exp_sub_one_ne_zero {t : ℝ} (ht : t ≠ 0) : exp t - 1 ≠ 0 :=
  sub_ne_zero.2 ((exp_eq_one_iff t).not.2 ht)

/-- The derivative of `g = (exp t - 1)⁻¹` is `-(g + g²)`. -/
theorem hasDerivAt_inv_exp_sub_one {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s ↦ (exp s - 1)⁻¹) (-((exp t - 1)⁻¹ + (exp t - 1)⁻¹ ^ 2)) t := by
  convert ((hasDerivAt_exp t).sub_const 1).inv (exp_sub_one_ne_zero ht) using 1
  field_simp
  ring

/-- `(exp t - 1)⁻¹ = O(exp (-t))` as `t → ∞`. -/
theorem isBigO_inv_exp_sub_one : (fun t ↦ (exp t - 1)⁻¹) =O[atTop] fun t ↦ exp (-t) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (log 2)] with t ht
  have h2 : 2 ≤ exp t := (exp_log two_pos).symm.le.trans (exp_le_exp.2 ht)
  have hpos : 0 < exp t - 1 := by linarith
  rw [norm_of_nonneg (inv_pos.2 hpos).le, norm_of_nonneg (exp_pos _).le, exp_neg]
  calc (exp t - 1)⁻¹ ≤ (exp t / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    _ = 2 * (exp t)⁻¹ := by rw [inv_div, div_eq_mul_inv]

/-- For `t > 0`, the geometric expansion `(exp t - 1)⁻¹ = ∑_{k ≥ 0} exp (-((k + 1) t))`. -/
theorem hasSum_exp_neg_nat_succ_mul {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ ↦ exp (-((k + 1) * t))) (exp t - 1)⁻¹ := by
  have h1 : 1 < exp t := one_lt_exp_iff.2 ht
  convert (hasSum_geometric_of_lt_one (exp_pos (-t)).le
    (exp_lt_one_iff.2 (neg_neg_of_pos ht))).mul_left (exp (-t)) using 1
  · funext k
    rw [← exp_natCast_mul, ← exp_add]
    ring_nf
  · have h2 : exp t - 1 ≠ 0 := by linarith
    rw [exp_neg]
    field_simp

end Real
