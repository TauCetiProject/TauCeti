/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# The exponential potential dominates the modular `√(1 + t²) - 1`

The convex potential `exp (2t) - 1 - 2t` is nonnegative and vanishes to second order at `0`, like
the modular `√(1 + t²) - 1`. For positive `t` it grows exponentially, but for negative `t` only
linearly, as does the modular. This file records the comparison

`√(1 + t²) - 1 ≤ exp (2t) - 1 - 2t`

(`Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul`), which turns a bound on the
potential into a bound on a quantity comparable to `min (t², |t|)`. It is the pointwise input to
coercivity estimates for functionals with this potential, such as Taubes's functional for planar
vortices.

## Main results

* `Real.exp_two_mul_sub_one_sub_two_mul_nonneg`: for every real `t`, `0 ≤ exp (2t) - 1 - 2t`.
* `Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul`: for every real `t`,
  `√(1 + t²) - 1 ≤ exp (2t) - 1 - 2t`.
* `Real.exp_two_mul_sub_one_sub_two_mul_le_of_mem_uIcc`: the potential decreases when `t` moves
  towards `0`.
* `Real.abs_exp_two_mul_sub_one_sub_two_mul_sub_le`: on `[-N, N]` the potential is Lipschitz with
  constant `4 exp (2N) (|a| + |b|)` between `a` and `b`. With
  `Real.abs_exp_sub_one_le_abs_mul_exp_abs`, `|exp x - 1| ≤ |x| exp |x|`, these are the pointwise
  inputs to approximating functions of finite potential.
-/

public section

namespace Real

/-- The potential `exp (2t) - 1 - 2t` is nonnegative. -/
theorem exp_two_mul_sub_one_sub_two_mul_nonneg (t : ℝ) : 0 ≤ exp (2 * t) - 1 - 2 * t := by
  linarith [add_one_le_exp (2 * t)]

/-- The potential `exp (2t) - 1 - 2t` dominates the modular `√(1 + t²) - 1`. -/
theorem sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul (t : ℝ) :
    √(1 + t ^ 2) - 1 ≤ exp (2 * t) - 1 - 2 * t := by
  have hsq : √(1 + t ^ 2) ≤ 1 + t ^ 2 / 2 :=
    sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (t ^ 2)]⟩
  rcases le_total 0 t with ht | ht
  · have := quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * t)
    nlinarith
  rcases le_total (-1) t with ht1 | ht1
  · -- For `-1 ≤ t ≤ 0`, `(1 + 2t/3)³ ≤ exp (2t)`.
    have h := one_sub_div_pow_le_exp_neg (n := 3) (t := -(2 * t)) (by push_cast; linarith)
    rw [neg_neg] at h
    have ht3 : 0 ≤ t ^ 2 * (t + 1) := mul_nonneg (sq_nonneg t) (by linarith)
    nlinarith
  · -- For `t ≤ -1`, `exp (2t) - 1 - 2t ≥ -t - (1 + t) ≥ |t| ≥ √(1 + t²) - 1`.
    have habs := sqrt_one_add_sq_sub_one_le_abs t
    rw [abs_of_nonpos ht] at habs
    nlinarith [exp_pos (2 * t)]

/-- `|exp x - 1| ≤ |x| exp |x|` for every real `x`. -/
theorem abs_exp_sub_one_le_abs_mul_exp_abs (x : ℝ) : |exp x - 1| ≤ |x| * exp |x| := by
  rcases le_total 0 x with hx | hx
  · have h := add_one_le_exp (-x)
    have he : exp x * exp (-x) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
    rw [abs_of_nonneg hx, abs_of_nonneg (by linarith [add_one_le_exp x])]
    nlinarith [exp_pos x]
  · have h := add_one_le_exp x
    have h1 : 1 ≤ exp (-x) := one_le_exp (by linarith)
    rw [abs_of_nonpos hx, abs_of_nonpos (by linarith [exp_le_one_iff.mpr hx])]
    nlinarith [mul_nonneg (neg_nonneg.mpr hx) (sub_nonneg.mpr h1)]

/-- The potential `exp (2t) - 1 - 2t` decreases when `t` moves towards `0`: its value at any `s`
between `0` and `t` is at most its value at `t`. -/
theorem exp_two_mul_sub_one_sub_two_mul_le_of_mem_uIcc {s t : ℝ} (h : s ∈ Set.uIcc 0 t) :
    exp (2 * s) - 1 - 2 * s ≤ exp (2 * t) - 1 - 2 * t := by
  rw [Set.mem_uIcc] at h
  have h₁ := add_one_le_exp (2 * (t - s))
  have hst : exp (2 * t) = exp (2 * s) * exp (2 * (t - s)) := by
    rw [← exp_add]; ring_nf
  have h₃ : exp (2 * s) * (1 + 2 * (t - s)) ≤ exp (2 * t) := by
    rw [hst]; exact mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
  rcases h with ⟨hs, hst'⟩ | ⟨hts', hs⟩
  · have : 1 ≤ exp (2 * s) := one_le_exp (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hst') (sub_nonneg.mpr this)]
  · have : exp (2 * s) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hts') (sub_nonneg.mpr this)]

/-- The tangent-line inequality for the convex potential `exp (2t) - 1 - 2t`, whose derivative at
`a` is `2 (exp (2a) - 1)`. -/
theorem exp_two_mul_sub_one_sub_two_mul_sub_le (a b : ℝ) :
    (exp (2 * a) - 1 - 2 * a) - (exp (2 * b) - 1 - 2 * b) ≤ 2 * (exp (2 * a) - 1) * (a - b) := by
  have h := add_one_le_exp (2 * (b - a))
  have hab : exp (2 * b) = exp (2 * a) * exp (2 * (b - a)) := by
    rw [← exp_add]; ring_nf
  nlinarith [exp_pos (2 * a)]

/-- On `[-N, N]` the potential `exp (2t) - 1 - 2t` is locally Lipschitz, with a constant
proportional to `|a| + |b|`, reflecting its vanishing to second order at `0`. -/
theorem abs_exp_two_mul_sub_one_sub_two_mul_sub_le {N a b : ℝ} (ha : |a| ≤ N) (hb : |b| ≤ N) :
    |(exp (2 * a) - 1 - 2 * a) - (exp (2 * b) - 1 - 2 * b)| ≤
      4 * exp (2 * N) * (|a| + |b|) * |a - b| := by
  have hpos : 0 ≤ 4 * exp (2 * N) := by positivity
  have hd (t : ℝ) (ht : |t| ≤ N) : |2 * (exp (2 * t) - 1)| ≤ 4 * exp (2 * N) * |t| := by
    have h := abs_exp_sub_one_le_abs_mul_exp_abs (2 * t)
    have he := exp_le_exp.mpr (by linarith : 2 * |t| ≤ 2 * N)
    rw [abs_mul, abs_two]
    rw [abs_mul, abs_two] at h
    nlinarith [abs_nonneg t, exp_pos (2 * |t|)]
  have k₁ : 2 * (exp (2 * a) - 1) * (a - b) ≤ 4 * exp (2 * N) * |a| * |a - b| :=
    (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hd a ha)
  have k₂ : 2 * (exp (2 * b) - 1) * (b - a) ≤ 4 * exp (2 * N) * |b| * |a - b| :=
    (le_abs_self _).trans (by rw [abs_mul, abs_sub_comm]; gcongr; exact hd b hb)
  have h₁ := exp_two_mul_sub_one_sub_two_mul_sub_le a b
  have h₂ := exp_two_mul_sub_one_sub_two_mul_sub_le b a
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (mul_nonneg hpos (abs_nonneg a)) (abs_nonneg (a - b)),
    mul_nonneg (mul_nonneg hpos (abs_nonneg b)) (abs_nonneg (a - b))]

end Real

end
