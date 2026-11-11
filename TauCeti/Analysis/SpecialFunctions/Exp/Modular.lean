/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
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

* `Real.continuous_exp_two_mul_sub_one_sub_two_mul`: the potential is continuous.
* `Real.exp_two_mul_sub_one_sub_two_mul_nonneg`: for every real `t`, `0 ≤ exp (2t) - 1 - 2t`.
* `Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul`: for every real `t`,
  `√(1 + t²) - 1 ≤ exp (2t) - 1 - 2t`.
* `Real.monotoneOn_exp_two_mul_sub_one_sub_two_mul`,
  `Real.antitoneOn_exp_two_mul_sub_one_sub_two_mul`: the potential increases on `[0, ∞)` and
  decreases on `(-∞, 0]`.
* `Real.exp_two_mul_sub_one_sub_two_mul_le_mul_sq`: below a level `S`, the potential is at most
  `4 (exp (2S) + 2) t²`.
-/

public section

namespace Real

/-- The potential `exp (2t) - 1 - 2t` is continuous. -/
theorem continuous_exp_two_mul_sub_one_sub_two_mul :
    Continuous fun t : ℝ ↦ exp (2 * t) - 1 - 2 * t := by
  fun_prop

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

/-- The potential `exp (2t) - 1 - 2t` is increasing on `[0, ∞)`. -/
theorem monotoneOn_exp_two_mul_sub_one_sub_two_mul :
    MonotoneOn (fun t ↦ exp (2 * t) - 1 - 2 * t) (Set.Ici 0) := by
  intro a ha b _ hab
  have h1 := add_one_le_exp (2 * (b - a))
  have h2 : 1 ≤ exp (2 * a) := one_le_exp (by linarith [Set.mem_Ici.mp ha])
  have h3 : exp (2 * b) = exp (2 * a) * exp (2 * (b - a)) := by
    rw [← exp_add]; ring_nf
  simp only
  nlinarith

/-- The potential `exp (2t) - 1 - 2t` is decreasing on `(-∞, 0]`. -/
theorem antitoneOn_exp_two_mul_sub_one_sub_two_mul :
    AntitoneOn (fun t ↦ exp (2 * t) - 1 - 2 * t) (Set.Iic 0) := by
  intro b _ a ha hba
  have h1 := add_one_le_exp (-(2 * (a - b)))
  have h2 : exp (2 * a) ≤ 1 := exp_le_one_iff.mpr (by linarith [Set.mem_Iic.mp ha])
  have h3 : exp (2 * b) = exp (2 * a) * exp (-(2 * (a - b))) := by
    rw [← exp_add]; ring_nf
  have h4 : 0 ≤ exp (2 * a) := exp_nonneg _
  simp only
  nlinarith

/-- Below a level `S`, the potential `exp (2t) - 1 - 2t` is at most a multiple of `t²`:
`exp (2t) - 1 - 2t ≤ 4 (exp (2S) + 2) t²` for `t ≤ S`. -/
theorem exp_two_mul_sub_one_sub_two_mul_le_mul_sq {S t : ℝ} (ht : t ≤ S) :
    exp (2 * t) - 1 - 2 * t ≤ 4 * (exp (2 * S) + 2) * t ^ 2 := by
  have hS : 0 ≤ exp (2 * S) := exp_nonneg _
  rcases le_or_gt |2 * t| 1 with h | h
  · -- Near zero, `|exp x - 1 - x| ≤ x²`.
    have := (abs_le.mp (abs_exp_sub_one_sub_id_le h)).2
    nlinarith [sq_nonneg t]
  · -- Away from zero, `1 ≤ 4 t²` and `|2t| ≤ 4 t²` absorb the constant and linear terms.
    have hexp : exp (2 * t) ≤ exp (2 * S) := exp_le_exp.mpr (by linarith)
    have h1 : 1 ≤ 4 * t ^ 2 := by
      have := sq_abs (2 * t)
      nlinarith
    have h2 : -(2 * t) ≤ 4 * t ^ 2 := by
      have := neg_abs_le (2 * t)
      nlinarith [abs_nonneg (2 * t), sq_abs (2 * t)]
    nlinarith

end Real

end
