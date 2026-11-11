/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quadratic upper bounds for the real exponential

Mathlib records the lower bound `1 + x + x ^ 2 / 2 ≤ exp x` for `0 ≤ x`
(`Real.quadratic_le_exp_of_nonneg`). This file supplies the matching upper bounds:

* `Real.exp_le_one_add_add_sq_div_two_of_nonpos`: for `x ≤ 0`,
  `exp x ≤ 1 + x + x ^ 2 / 2`;
* `Real.exp_le_one_add_add_sq_div_of_le`: if `x ≤ c` with `0 ≤ c < 3`, then
  `exp x ≤ 1 + x + x ^ 2 / (2 * (1 - c / 3))`.

The second bound is the exponential estimate behind Bernstein's inequality: applied to `t X` for a
centred random variable `X ≤ b` it bounds the moment-generating function by the second moment.

In the other direction, the lower bound gives
`Real.neg_mul_abs_sub_sq_div_le_mul_add_mul_exp_div`: for `V > 0`,
`-S |t| - S ^ 2 / V ≤ t S + V exp (2 t) / 2`. This controls the part of a Liouville-type energy
`∫ (K u + e^(2u) / 2) dV` carried by the mean `t` of `u`, with `S = ∫ K dV` and `V` the volume
(`TauCeti.Manifold.exists_le_liouvilleEnergy_add`).

## References

* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*, Oxford University Press (2013), §2.8.
-/

public section

open scoped Nat

namespace Real

/-- For `x ≤ 0`, the exponential lies below its second-order Taylor polynomial at `0`. -/
theorem exp_le_one_add_add_sq_div_two_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    exp x ≤ 1 + x + x ^ 2 / 2 := by
  -- `p = 1 - x + x ^ 2 / 2 ≤ exp (-x)` and `p * (1 + x + x ^ 2 / 2) = 1 + x ^ 4 / 4 ≥ 1`.
  have hp : 0 < 1 + -x + (-x) ^ 2 / 2 := by nlinarith
  have hle := quadratic_le_exp_of_nonneg (neg_nonneg.2 hx)
  have hmul : exp x * exp (-x) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  refine le_of_mul_le_mul_right ?_ hp
  calc exp x * (1 + -x + (-x) ^ 2 / 2) ≤ exp x * exp (-x) :=
        mul_le_mul_of_nonneg_left hle (exp_pos x).le
    _ = 1 := hmul
    _ ≤ (1 + x + x ^ 2 / 2) * (1 + -x + (-x) ^ 2 / 2) := by nlinarith [pow_two_nonneg (x ^ 2)]

/-- For `0 ≤ x ≤ c < 3`, the remainder `exp x - 1 - x` is at most `x ^ 2 / (2 * (1 - c / 3))`. -/
private theorem exp_le_one_add_add_sq_div_of_nonneg_of_le {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c)
    (hc : c < 3) : exp x ≤ 1 + x + x ^ 2 / (2 * (1 - c / 3)) := by
  have hc0 : 0 ≤ c := hx.trans hxc
  have hs : HasSum (fun n : ℕ ↦ x ^ n / n !) (exp x) := by
    rw [exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hs2 : HasSum (fun n : ℕ ↦ x ^ (n + 2) / (n + 2)!) (exp x - 1 - x) := by
    have := (hasSum_nat_add_iff' 2).2 hs
    simpa [Finset.sum_range_succ, sub_sub] using this
  have hg : HasSum (fun n : ℕ ↦ x ^ 2 / 2 * (c / 3) ^ n) (x ^ 2 / 2 * (1 - c / 3)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by linarith)).mul_left _
  have hterm (n : ℕ) : x ^ (n + 2) / (n + 2)! ≤ x ^ 2 / 2 * (c / 3) ^ n := by
    have hfac : (2 * 3 ^ n : ℝ) ≤ (n + 2)! := by
      rw [add_comm n 2]
      exact_mod_cast Nat.factorial_mul_pow_le_factorial (m := 2) (n := n)
    have hxn : x ^ n ≤ c ^ n := pow_le_pow_left₀ hx hxc n
    rw [div_le_iff₀ (by positivity), div_pow, pow_add]
    calc x ^ n * x ^ 2 ≤ c ^ n * x ^ 2 := mul_le_mul_of_nonneg_right hxn (by positivity)
      _ = x ^ 2 / 2 * (c ^ n / 3 ^ n) * (2 * 3 ^ n) := by field_simp
      _ ≤ x ^ 2 / 2 * (c ^ n / 3 ^ n) * (n + 2)! := by gcongr
  have := hasSum_le hterm hs2 hg
  rw [mul_comm 2, ← div_div, div_eq_mul_inv _ (1 - c / 3)]
  linarith

/-- **Bernstein's exponential bound.** If `x ≤ c` with `0 ≤ c < 3`, then
`exp x ≤ 1 + x + x ^ 2 / (2 * (1 - c / 3))`. Only an upper bound on `x` is needed: negative `x`
are covered by `Real.exp_le_one_add_add_sq_div_two_of_nonpos`. -/
theorem exp_le_one_add_add_sq_div_of_le {x c : ℝ} (hxc : x ≤ c) (hc0 : 0 ≤ c) (hc3 : c < 3) :
    exp x ≤ 1 + x + x ^ 2 / (2 * (1 - c / 3)) := by
  rcases le_total x 0 with hx | hx
  · refine (exp_le_one_add_add_sq_div_two_of_nonpos hx).trans ?_
    gcongr
    · nlinarith
    · linarith
  · exact exp_le_one_add_add_sq_div_of_nonneg_of_le hx hxc hc3

/-- Real numbers `S`, `t` and `V > 0` satisfy `t S + V exp (2 t) / 2 ≥ -S |t| - S ^ 2 / V`. For
`t ≥ 0` this follows from `exp (2 t) ≥ 1 + 2 t + 2 t ^ 2` and `(V t + S) ^ 2 ≥ 0`. -/
theorem neg_mul_abs_sub_sq_div_le_mul_add_mul_exp_div {S V t : ℝ} (hV : 0 < V) :
    -S * |t| - S ^ 2 / V ≤ t * S + V * exp (2 * t) / 2 := by
  have hq : 0 ≤ S ^ 2 / V := by positivity
  have hVq : V * (S ^ 2 / V) = S ^ 2 := mul_div_cancel₀ _ hV.ne'
  rcases le_total t 0 with ht | ht
  · rw [abs_of_nonpos ht]
    nlinarith [exp_pos (2 * t)]
  · rw [abs_of_nonneg ht]
    have hexp := quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 2 * t)
    -- `V t² + 2 t S + S² / V = (V t + S)² / V ≥ 0`.
    have hsq : 0 ≤ V * (V * t ^ 2 + 2 * t * S + S ^ 2 / V) := by
      nlinarith [sq_nonneg (V * t + S)]
    have := (mul_nonneg_iff_of_pos_left hV).1 hsq
    nlinarith [mul_le_mul_of_nonneg_left hexp hV.le]

end Real
