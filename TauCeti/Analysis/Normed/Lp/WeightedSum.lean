/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Group.Int
import TauCeti.Analysis.MeanInequalities

/-!
# Sums weighted by `(1 + ‖x‖) ^ s`

On a seminormed additive group, the weights `(1 + ‖x‖) ^ s` define the weighted `ℓ²` spaces.
On the circle these correspond, through Fourier coefficients, to the Sobolev spaces `H^s`. This
file records two facts about sums with these weights, stated for unconditional sums in `ℝ≥0∞`.

## Main statements

* `TauCeti.sq_tsum_le_tsum_one_add_norm_rpow_mul`: by the Cauchy–Schwarz inequality, a weighted
  `ℓ²` family is summable whenever the weights `(1 + ‖x‖) ^ (-2 s)` are:
  `(∑' x, h x) ^ 2 ≤ (∑' x, (1 + ‖x‖) ^ (-2 s)) * ∑' x, ((1 + ‖x‖) ^ s * h x) ^ 2`.
* `TauCeti.ofReal_sq_one_add_abs_rpow_mul_norm`: on `ℤ`, the real weighted square
  `((1 + |n|) ^ s * ‖v‖) ^ 2` in `ℝ≥0∞` is `((1 + ‖n‖) ^ s * ‖v‖ₑ) ^ 2`. This converts between
  real weighted sums on `ℤ` and the `ℝ≥0∞` sums used here.
-/

public section

open scoped ENNReal

namespace TauCeti

/-- **Weighted `ℓ²` bounds `ℓ¹`.** By the Cauchy–Schwarz inequality,
`(∑' x, h x) ^ 2 ≤ (∑' x, (1 + ‖x‖) ^ (-2 s)) * ∑' x, ((1 + ‖x‖) ^ s * h x) ^ 2`
for every family `h` in `ℝ≥0∞`. On `ℤ` the first factor is finite for `s > 1 / 2`
(`TauCeti.summable_one_add_abs_int_rpow`). -/
theorem sq_tsum_le_tsum_one_add_norm_rpow_mul {G : Type*} [SeminormedAddGroup G] (s : ℝ)
    (h : G → ℝ≥0∞) :
    (∑' x, h x) ^ 2 ≤ (∑' x : G, ENNReal.ofReal ((1 + ‖x‖) ^ (-2 * s))) *
      ∑' x, (ENNReal.ofReal ((1 + ‖x‖) ^ s) * h x) ^ 2 := by
  have hw (x : G) : 0 < 1 + ‖x‖ := by positivity
  -- Write `h x = (1 + ‖x‖) ^ (-s) * ((1 + ‖x‖) ^ s * h x)` and apply Cauchy–Schwarz.
  have hsplit (x : G) : h x =
      ENNReal.ofReal ((1 + ‖x‖) ^ (-s)) * (ENNReal.ofReal ((1 + ‖x‖) ^ s) * h x) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (hw x),
      neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  have hsq (x : G) : ENNReal.ofReal ((1 + ‖x‖) ^ (-s)) ^ (2 : ℝ) =
      ENNReal.ofReal ((1 + ‖x‖) ^ (-2 * s)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two, ← Real.rpow_mul (hw x).le,
      mul_comm (-s), neg_mul, mul_neg]
  have hCS := ENNReal.inner_le_Lp_mul_Lq_tsum (fun x ↦ ENNReal.ofReal ((1 + ‖x‖) ^ (-s)))
    (fun x ↦ ENNReal.ofReal ((1 + ‖x‖) ^ s) * h x) Real.HolderConjugate.two_two
  simp only [hsq, ENNReal.rpow_two, ← hsplit] at hCS
  calc (∑' x, h x) ^ 2 ≤ ((∑' x, ENNReal.ofReal ((1 + ‖x‖) ^ (-2 * s))) ^ (1 / 2 : ℝ) *
        (∑' x, (ENNReal.ofReal ((1 + ‖x‖) ^ s) * h x) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_mul_natCast, ← ENNReal.rpow_mul_natCast]
        norm_num

/-- On `ℤ`, the real weighted square `((1 + |n|) ^ s * ‖v‖) ^ 2`, viewed in `ℝ≥0∞`, is
`((1 + ‖n‖) ^ s * ‖v‖ₑ) ^ 2`. -/
theorem ofReal_sq_one_add_abs_rpow_mul_norm {X : Type*} [SeminormedAddGroup X] (s : ℝ) (n : ℤ)
    (v : X) :
    ENNReal.ofReal (((1 + |(n : ℝ)|) ^ s * ‖v‖) ^ 2) =
      (ENNReal.ofReal ((1 + ‖n‖) ^ s) * ‖v‖ₑ) ^ 2 := by
  rw [Int.norm_eq_abs, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
    ofReal_norm]

end TauCeti
