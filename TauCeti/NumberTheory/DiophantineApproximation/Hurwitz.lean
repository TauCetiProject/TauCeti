/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Real.GoldenRatio

import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Data.Rat.BoundedDen

/-!
# Sharpness of Hurwitz's theorem at the golden ratio

Hurwitz's theorem (`Real.infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational`) states
that every irrational number `ξ` has infinitely many rational approximations `r` with
`|ξ - r| < 1 / (√5 * r.den ^ 2)`. This file proves that the constant `√5` cannot be improved for the
golden ratio `φ`: for every `c > √5`, only finitely many rationals `r` satisfy
`|φ - r| < 1 / (c * r.den ^ 2)`.

The proof does not use continued fractions. For integers `p` and `q` that are not both zero, the
product `(q * φ - p) * (q * ψ - p) = p ^ 2 - p * q - q ^ 2` is a nonzero integer, where `ψ` is the
conjugate of `φ`, so `1 ≤ |q * φ - p| * |q * ψ - p|`. Since `q * ψ - p = q * φ - p - q * √5`, the
number `x = |q * φ - p|` satisfies `1 ≤ x * (x + |q| * √5)`
(`TauCeti.one_le_abs_mul_goldenRatio_sub_mul_add`). Now let `c > √5`. If `p / q` with `q > 0`
satisfies `|φ - p / q| < 1 / (c * q ^ 2)`, then `x * (c * q) < 1`, and the two inequalities give
`q ^ 2 * (c * (c - √5)) < 1`. Because `c * (c - √5) > 0`, this bounds the denominator `q`, and a
bounded set contains finitely many rationals of bounded denominator.

## Main results

* `TauCeti.finite_setOf_abs_goldenRatio_sub_lt_of_sqrt_five_lt`: sharpness of Hurwitz's theorem
  at `φ`: for `c > √5`, only finitely many rationals `r` satisfy
  `|φ - r| < 1 / (c * r.den ^ 2)`.

## References

* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, ch. XI.
-/

public section

open scoped goldenRatio
open Real

namespace TauCeti

/-- For `c ≥ 0`, an integer `p` and a natural number `q` with `|q * φ - p| * (c * q) < 1` satisfy
`q ^ 2 * (c * (c - √5)) < 1`. For `c > √5` this bounds `q`. -/
private theorem sq_mul_lt_one_of_abs_mul_goldenRatio_sub_mul_lt {c : ℝ} (hc : 0 ≤ c) (p : ℤ)
    (q : ℕ) (h : |q * φ - p| * (c * q) < 1) : (q : ℝ) ^ 2 * (c * (c - √5)) < 1 := by
  rcases le_or_gt c √5 with hc5 | hc5
  · linarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (q : ℝ))
      (mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hc5))]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hc0 : 0 < c := (Real.sqrt_nonneg 5).trans_lt hc5
  have hnorm := one_le_abs_mul_goldenRatio_sub_mul_add (p := p) (q := q)
    (Or.inr (Nat.cast_ne_zero.mpr hq))
  rw [Int.cast_natCast, Nat.abs_cast] at hnorm
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = q * φ - p := ⟨_, rfl⟩
  rw [← hx] at h hnorm
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = |x| * (c * q) := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hw1 : w < 1 := hw ▸ h
  have key : c ^ 2 * (q : ℝ) ^ 2 ≤ w * w + w * (c * (q : ℝ) ^ 2 * √5) :=
    calc c ^ 2 * (q : ℝ) ^ 2 = c ^ 2 * (q : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ c ^ 2 * (q : ℝ) ^ 2 * (|x| * (|x| + q * √5)) := by gcongr
      _ = w * w + w * (c * (q : ℝ) ^ 2 * √5) := by rw [hw]; ring
  have h1 : w * w < 1 := (mul_le_of_le_one_right hw0 hw1.le).trans_lt hw1
  have h2 : w * (c * (q : ℝ) ^ 2 * √5) ≤ c * (q : ℝ) ^ 2 * √5 :=
    mul_le_of_le_one_left (by positivity) hw1.le
  calc (q : ℝ) ^ 2 * (c * (c - √5)) = c ^ 2 * (q : ℝ) ^ 2 - c * (q : ℝ) ^ 2 * √5 := by ring
    _ < 1 := by linarith

/-- **Sharpness of Hurwitz's theorem at the golden ratio.** For every `c > √5`, only finitely many
rational numbers `r` satisfy `|φ - r| < 1 / (c * r.den ^ 2)`. -/
theorem finite_setOf_abs_goldenRatio_sub_lt_of_sqrt_five_lt {c : ℝ} (hc : √5 < c) :
    {r : ℚ | |φ - r| < 1 / (c * (r.den : ℝ) ^ 2)}.Finite := by
  have h5 : (1 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hc1 : 1 ≤ c := (h5.trans hc).le
  have hc0 : 0 < c := one_pos.trans_le hc1
  have hcc : 0 < c * (c - √5) := mul_pos hc0 (sub_pos.mpr hc)
  refine ((Metric.isBounded_ball (x := φ) (r := (1 : ℝ))).finite_setOf_rat_den_le
    ⌊1 / (c * (c - √5))⌋₊).subset fun r hr ↦ ?_
  simp only [Set.mem_ofPred_eq] at hr ⊢
  have hd0 : (0 : ℝ) < r.den := mod_cast r.den_pos
  have hd : (1 : ℝ) ≤ r.den := mod_cast r.den_pos
  -- clearing the denominator bounds `q * φ - p`
  have hx : |(r.den : ℝ) * φ - r.num| * (c * r.den) < 1 := by
    calc |(r.den : ℝ) * φ - r.num| * (c * r.den) = c * (r.den * |r.den * φ - r.num|) := by ring
      _ = |φ - r| * (c * (r.den : ℝ) ^ 2) := by
        rw [mul_abs_mul_sub_eq_sq_mul_abs_sub_div hd0, ← Rat.cast_def]
        ring
      _ < 1 := (lt_div_iff₀ (by positivity)).mp hr
  -- hence the denominator is bounded
  have hden : (r.den : ℝ) ^ 2 * (c * (c - √5)) < 1 :=
    sq_mul_lt_one_of_abs_mul_goldenRatio_sub_mul_lt hc0.le r.num r.den hx
  refine ⟨Nat.le_floor ?_, ?_⟩
  · rw [le_div_iff₀ hcc]
    nlinarith
  -- and the approximation inequality puts `r` in the unit ball around `φ`
  · rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    exact hr.trans_le ((div_le_one (by positivity)).mpr
      (one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hd)))

end TauCeti
