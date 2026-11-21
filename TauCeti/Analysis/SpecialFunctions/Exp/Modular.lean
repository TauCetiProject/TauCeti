/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
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

In the other direction, the potential is quadratic on every half-line `t ≤ M`:
`exp (2t) - 1 - 2t ≤ 2 exp (2M) t²` for `0 ≤ M`
(`Real.exp_two_mul_sub_one_sub_two_mul_le_mul_sq`). Its midpoint convexity defect is exactly a
square: `Φ(a) + Φ(b) - 2 Φ((a + b) / 2) = (exp a - exp b)²` for `Φ(t) = exp (2t) - 1 - 2t`
(`Real.exp_two_mul_sub_one_sub_two_mul_midpoint_defect_eq_sq`), the strict convexity behind the
stability of the minimizer of such a functional.

## Main results

* `Real.exp_two_mul_sub_one_sub_two_mul_nonneg`: for every real `t`, `0 ≤ exp (2t) - 1 - 2t`.
* `Real.convexOn_exp_two_mul_sub_one_sub_two_mul`: the potential `exp (2t) - 1 - 2t` is convex.
* `Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul`: for every real `t`,
  `√(1 + t²) - 1 ≤ exp (2t) - 1 - 2t`.
* `Real.exp_two_mul_sub_one_sub_two_mul_le_mul_sq`: for `t ≤ M` with `0 ≤ M`,
  `exp (2t) - 1 - 2t ≤ 2 exp (2M) t²`.
* `Real.exp_two_mul_sub_one_sub_two_mul_midpoint_defect_eq_sq`: the midpoint convexity defect of
  `exp (2t) - 1 - 2t` is `(exp a - exp b)²`.
-/

public section

namespace Real

/-- The potential `exp (2t) - 1 - 2t` is nonnegative. -/
theorem exp_two_mul_sub_one_sub_two_mul_nonneg (t : ℝ) : 0 ≤ exp (2 * t) - 1 - 2 * t := by
  linarith [add_one_le_exp (2 * t)]

/-- The potential `exp (2t) - 1 - 2t` is convex: it is the convex function `exp (2t)` minus an
affine function. -/
theorem convexOn_exp_two_mul_sub_one_sub_two_mul :
    ConvexOn ℝ Set.univ fun t : ℝ ↦ exp (2 * t) - 1 - 2 * t := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have h := convexOn_exp.2 (Set.mem_univ (2 * x)) (Set.mem_univ (2 * y)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  -- Rewrite the convex combination of the arguments `2x` and `2y` as `2` times that of `x`, `y`.
  have harg : a * (2 * x) + b * (2 * y) = 2 * (a * x + b * y) := by ring
  rw [harg] at h
  linarith

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

/-- On the half-line `t ≤ M`, `0 ≤ M`, the potential `exp (2t) - 1 - 2t` is at most
`2 exp (2M) t²`. -/
theorem exp_two_mul_sub_one_sub_two_mul_le_mul_sq {M t : ℝ} (hM : 0 ≤ M) (ht : t ≤ M) :
    exp (2 * t) - 1 - 2 * t ≤ 2 * exp (2 * M) * t ^ 2 := by
  rcases le_total t 0 with h0 | h0
  · have h := exp_le_one_add_add_sq_div_two_of_nonpos (by linarith : 2 * t ≤ 0)
    have h1 : 1 ≤ exp (2 * M) := one_le_exp (by linarith)
    nlinarith [sq_nonneg t]
  · have h := exp_le_one_add_add_sq_div_two_mul_exp_abs (2 * t)
    rw [abs_of_nonneg (by linarith)] at h
    have h1 : exp (2 * t) ≤ exp (2 * M) := exp_le_exp.2 (by linarith)
    nlinarith [sq_nonneg t]

/-- The midpoint convexity defect of the potential `Φ(t) = exp (2t) - 1 - 2t` is a square:
`Φ(a) + Φ(b) - 2 Φ((a + b) / 2) = (exp a - exp b)²`. -/
theorem exp_two_mul_sub_one_sub_two_mul_midpoint_defect_eq_sq (a b : ℝ) :
    (exp (2 * a) - 1 - 2 * a) + (exp (2 * b) - 1 - 2 * b) -
        2 * (exp (2 * ((a + b) / 2)) - 1 - 2 * ((a + b) / 2)) =
      (exp a - exp b) ^ 2 := by
  have ha : exp (2 * a) = exp a ^ 2 := by rw [sq, ← exp_add]; ring_nf
  have hb : exp (2 * b) = exp b ^ 2 := by rw [sq, ← exp_add]; ring_nf
  have hab : exp (2 * ((a + b) / 2)) = exp a * exp b := by rw [← exp_add]; ring_nf
  rw [ha, hb, hab]
  ring

end Real

end
