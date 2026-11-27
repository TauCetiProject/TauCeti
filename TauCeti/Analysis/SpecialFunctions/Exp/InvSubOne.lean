/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# The function `(exp t - 1)⁻¹`

The function `g(t) = (exp t - 1)⁻¹` is the factor of the Bernoulli kernel `t / (exp t - 1)` that
carries its behaviour away from `0`. It satisfies the Riccati-type equation `g' = -(g + g²)`, it
decays like `exp (-t)` at `+∞`, and for `t > 0` it is the geometric series
`∑_{k ≥ 0} exp (-((k + 1) t))`.

Over any complete characteristic-zero normed field `𝕜` with `[ContinuousSMul ℚ 𝕜]` (and in
particular over `ℂ`), factoring `exp z` from `exp z - 1` gives `exp z - 1 = exp z * (1 - exp (-z))`
in any complete commutative normed `𝕜`-algebra
(`NormedSpace.exp_sub_one_eq_exp_mul_one_sub_exp_neg`), and over `𝕜` itself gives
`exp (-c * z) / (1 - exp (-z)) = exp ((1 - c) * z) / (exp z - 1)` and
`exp (-z) / (1 - exp (-z)) = (exp z - 1)⁻¹`.

## Main results

* `Real.exp_sub_one_ne_zero`: `exp t - 1 ≠ 0` for `t ≠ 0`, so `g` is defined away from `0`.
* `Real.exp_sub_one_eq_one_sub_exp_neg_mul`: `exp t - 1 = (1 - exp (-t)) * exp t`.
* `Real.one_sub_exp_neg_mul_exp_le_exp_sub_one`: `(1 - exp (-s)) * exp t ≤ exp t - 1` for `s ≤ t`.
* `Real.hasDerivAt_inv_exp_sub_one`: `g' = -(g + g²)` away from `0`.
* `Real.isBigO_inv_exp_sub_one`: `g(t) = O(exp (-t))` as `t → ∞`.
* `Real.hasSum_exp_neg_nat_succ_mul`: `g(t) = ∑_{k ≥ 0} exp (-((k + 1) t))` for `t > 0`.
* `Real.hasSum_mul_exp_neg_nat_succ_mul`: `a / (exp t - 1) = ∑_{k ≥ 0} a * exp (-((k + 1) t))`
  for `t > 0`.
* `NormedSpace.exp_sub_one_eq_exp_mul_one_sub_exp_neg`: general commutative Banach-algebra
  factorization `exp z - 1 = exp z * (1 - exp (-z))`.
* `NormedSpace.exp_neg_mul_div_one_sub_exp_neg`, `NormedSpace.exp_neg_div_one_sub_exp_neg`:
  general normed-field quotient rewrites.
* `Complex.exp_sub_one_eq_exp_mul_one_sub_exp_neg`,
  `Complex.exp_neg_mul_div_one_sub_exp_neg`, `Complex.exp_neg_div_one_sub_exp_neg`:
  complex specializations.
-/

public section

open Filter Asymptotics

namespace Real

/-- `exp t - 1` vanishes only at `t = 0`. -/
theorem exp_sub_one_ne_zero {t : ℝ} (ht : t ≠ 0) : exp t - 1 ≠ 0 :=
  sub_ne_zero.2 ((exp_eq_one_iff t).not.2 ht)

/-- Factorization `exp t - 1 = (1 - exp (-t)) * exp t`. -/
theorem exp_sub_one_eq_one_sub_exp_neg_mul (t : ℝ) :
    exp t - 1 = (1 - exp (-t)) * exp t := by
  rw [sub_mul, one_mul, ← exp_add, neg_add_cancel, exp_zero]

/-- For `s ≤ t`, `(1 - exp (-s)) * exp t ≤ exp t - 1`. -/
theorem one_sub_exp_neg_mul_exp_le_exp_sub_one {s t : ℝ} (hst : s ≤ t) :
    (1 - exp (-s)) * exp t ≤ exp t - 1 := by
  rw [exp_sub_one_eq_one_sub_exp_neg_mul t]
  gcongr

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

/-- For `t > 0` and any scalar `a : ℝ`, the scaled geometric expansion
`a / (exp t - 1) = ∑_{k ≥ 0} a * exp (-((k + 1) * t))`. -/
theorem hasSum_mul_exp_neg_nat_succ_mul (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ ↦ a * exp (-((k + 1) * t))) (a / (exp t - 1)) := by
  simpa [div_eq_mul_inv] using (hasSum_exp_neg_nat_succ_mul ht).mul_left a

end Real

namespace NormedSpace

section CommAlgebra

variable (𝕜 : Type*) {A : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [ContinuousSMul ℚ 𝕜]
  [NormedCommRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

include 𝕜 in
/-- Factoring out `NormedSpace.exp z` rewrites `exp z - 1` as `exp z * (1 - exp (-z))`. -/
theorem exp_sub_one_eq_exp_mul_one_sub_exp_neg (z : A) :
    exp z - 1 = exp z * (1 - exp (-z)) := by
  rw [mul_sub, mul_one, ← exp_add_of_continuousSMul 𝕜, add_neg_cancel, exp_zero]

end CommAlgebra

section Field

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [ContinuousSMul ℚ 𝕜]
  [CompleteSpace 𝕜]

/-- Rewriting `exp (-c * z) / (1 - exp (-z))` with denominator `exp z - 1`. -/
theorem exp_neg_mul_div_one_sub_exp_neg (c z : 𝕜) :
    exp (-c * z) / (1 - exp (-z)) = exp ((1 - c) * z) / (exp z - 1) := by
  have hnum : exp z * exp (-c * z) = exp ((1 - c) * z) := by
    rw [← exp_add_of_continuousSMul 𝕜]
    congr 1
    ring
  have hne : exp z ≠ 0 :=
    left_ne_zero_of_mul_eq_one (by rw [← exp_add_of_continuousSMul 𝕜, add_neg_cancel, exp_zero])
  rw [exp_sub_one_eq_exp_mul_one_sub_exp_neg 𝕜, ← hnum, mul_div_mul_left _ _ hne]

/-- Coefficient-free specialization of `exp_neg_mul_div_one_sub_exp_neg`:
`exp (-z) / (1 - exp (-z)) = (exp z - 1)⁻¹`. -/
theorem exp_neg_div_one_sub_exp_neg (z : 𝕜) :
    exp (-z) / (1 - exp (-z)) = (exp z - 1)⁻¹ := by
  simpa [one_div] using exp_neg_mul_div_one_sub_exp_neg (1 : 𝕜) z

end Field

end NormedSpace

namespace Complex

/-- Factoring out `Complex.exp z` rewrites `exp z - 1` as `exp z * (1 - exp (-z))`. -/
theorem exp_sub_one_eq_exp_mul_one_sub_exp_neg (z : ℂ) :
    exp z - 1 = exp z * (1 - exp (-z)) := by
  simpa only [Complex.exp_eq_exp_ℂ] using
    NormedSpace.exp_sub_one_eq_exp_mul_one_sub_exp_neg ℂ z

/-- Rewriting `Complex.exp (-c * z) / (1 - Complex.exp (-z))` with denominator `exp z - 1`. -/
theorem exp_neg_mul_div_one_sub_exp_neg (c z : ℂ) :
    exp (-c * z) / (1 - exp (-z)) = exp ((1 - c) * z) / (exp z - 1) := by
  simpa only [Complex.exp_eq_exp_ℂ] using
    NormedSpace.exp_neg_mul_div_one_sub_exp_neg c z

/-- Coefficient-free specialization `Complex.exp (-z) / (1 - Complex.exp (-z)) = (exp z - 1)⁻¹`. -/
theorem exp_neg_div_one_sub_exp_neg (z : ℂ) :
    exp (-z) / (1 - exp (-z)) = (exp z - 1)⁻¹ := by
  simpa only [Complex.exp_eq_exp_ℂ] using
    NormedSpace.exp_neg_div_one_sub_exp_neg z

end Complex
