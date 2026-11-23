/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.ContinuedFractions.Basic

/-!
# Convergents are best approximations

Let `pₖ / qₖ = ξ.convergent k` be the convergents of a real number `ξ`, in lowest terms.
This file proves Lagrange's best approximation property: no `q` with `0 < |q| < qₙ₊₁` brings `q ξ`
closer to an integer than `qₙ ξ` comes to `pₙ`,

`|qₙ ξ - pₙ| ≤ |q ξ - p|` for all integers `p` and `q` with `0 < |q| < qₙ₊₁`.

The proof writes `(p, q)` as an integer combination `a (pₙ, qₙ) + b (pₙ₊₁, qₙ₊₁)`, which the
determinant identity `pₙ qₙ₊₁ - pₙ₊₁ qₙ = ±1` allows. Take `q > 0`, replacing `(p, q)` by
`(-p, -q)` if necessary. Then `0 < q < qₙ₊₁` forces `a ≠ 0` and `a b ≤ 0`, and the errors
`qₙ ξ - pₙ` and `qₙ₊₁ ξ - pₙ₊₁` have opposite signs, so the two terms of
`q ξ - p = a (qₙ ξ - pₙ) + b (qₙ₊₁ ξ - pₙ₊₁)` do not cancel. Once the continued fraction has
terminated, `qₙ ξ - pₙ = 0` and there is nothing to prove; rational `ξ` need no separate statement.

This is the argument of Hardy and Wright, §10.15, Theorem 182, who expand `(p, q)` in two
consecutive convergents in the same way. Khinchin, Theorem 17, states the result as: every
convergent is a best approximation of the second kind.

## Main results

* `Real.abs_den_convergent_mul_sub_num_convergent_le`: the best approximation property.
* `Real.abs_den_convergent_mul_sub_num_convergent_le_norm`: the same, with the distance of
  `q ξ` to the nearest integer measured in `UnitAddCircle`.

## References

* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, Ch. X, §10.15
  (Approximation by convergents), Theorem 182.
* A. Ya. Khinchin, *Continued Fractions*, Ch. II, §6 (Convergents as best approximations),
  Theorem 17.
-/

public section

open GenContFract
open GenContFract (of)

namespace Real

/-- The best approximation property for a positive denominator `q < qₙ₊₁`. -/
private theorem abs_den_convergent_mul_sub_num_convergent_le_of_pos (ξ : ℝ) (n : ℕ) {q : ℤ}
    (hq : 0 < q) (hq' : q < (ξ.convergent (n + 1)).den) (p : ℤ) :
    |(ξ.convergent n).den * ξ - (ξ.convergent n).num| ≤ |q * ξ - p| := by
  by_cases hn : (of ξ).TerminatedAt n
  · rw [den_convergent_mul_sub_num_convergent_eq_zero ξ hn, abs_zero]
    exact abs_nonneg _
  have hdet := num_convergent_mul_den_convergent_succ_sub ξ hn
  have hD : ((-1 : ℤ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; simp
  -- The coordinates of `(p, q)` in the basis `(pₙ, qₙ)`, `(pₙ₊₁, qₙ₊₁)`.
  obtain ⟨a, b, hqab, hpab⟩ : ∃ a b : ℤ,
      q = a * (ξ.convergent n).den + b * (ξ.convergent (n + 1)).den ∧
        p = a * (ξ.convergent n).num + b * (ξ.convergent (n + 1)).num :=
    ⟨(-1) ^ (n + 1) * (p * (ξ.convergent (n + 1)).den - q * (ξ.convergent (n + 1)).num),
      (-1) ^ (n + 1) * (q * (ξ.convergent n).num - p * (ξ.convergent n).den),
      by linear_combination (-q) * hD - q * (-1) ^ (n + 1) * hdet,
      by linear_combination (-p) * hD - p * (-1) ^ (n + 1) * hdet⟩
  -- The signs of the errors `εₖ = qₖ ξ - pₖ` alternate; `εₙ₊₁` vanishes after termination.
  set s : ℝ := (-1) ^ n
  have hx := neg_one_pow_mul_den_convergent_mul_sub_num_convergent_pos ξ hn
  have hy : s * ((ξ.convergent (n + 1)).den * ξ - (ξ.convergent (n + 1)).num) ≤ 0 := by
    have := neg_one_pow_mul_den_convergent_mul_sub_num_convergent_nonneg ξ (n + 1)
    rw [pow_succ] at this
    linarith
  have hqR : (q : ℝ) = a * (ξ.convergent n).den + b * (ξ.convergent (n + 1)).den := by
    exact_mod_cast hqab
  have hpR : (p : ℝ) = a * (ξ.convergent n).num + b * (ξ.convergent (n + 1)).num := by
    exact_mod_cast hpab
  have herr : s * (q * ξ - p) =
      a * (s * ((ξ.convergent n).den * ξ - (ξ.convergent n).num)) +
        b * (s * ((ξ.convergent (n + 1)).den * ξ - (ξ.convergent (n + 1)).num)) := by
    rw [hpR, hqR]; ring
  have hQ : (0 : ℤ) < (ξ.convergent n).den := mod_cast (ξ.convergent n).pos
  have hs : |s| = 1 := by simp [s]
  have habs : ∀ x : ℝ, |x| = |s * x| := fun x ↦ by rw [abs_mul, hs, one_mul]
  rw [habs, habs (_ - _), abs_of_pos hx]
  rcases le_or_gt b 0 with hb | hb
  · -- `b ≤ 0` forces `a ≥ 1`, and both terms are at least `0`, the first at least `εₙ`.
    have ha : 1 ≤ a := by nlinarith [hQ, hq']
    have ha' : (1 : ℝ) ≤ a := mod_cast ha
    have hb' : (b : ℝ) ≤ 0 := mod_cast hb
    refine le_abs.2 (Or.inl ?_)
    rw [herr]
    nlinarith
  · -- `b ≥ 1` forces `a ≤ -1`, and both terms are at most `0`, the first at most `-εₙ`.
    have ha : a ≤ -1 := by nlinarith [hQ, hq']
    have ha' : (a : ℝ) ≤ -1 := mod_cast ha
    have hb' : (0 : ℝ) < b := mod_cast hb
    refine le_abs.2 (Or.inr ?_)
    rw [herr]
    nlinarith

/-- **Lagrange's best approximation property.** For a real `ξ` with convergents `pₖ / qₖ`, no
integers `p` and `q` with `0 < |q| < qₙ₊₁` satisfy `|q ξ - p| < |qₙ ξ - pₙ|`.

See Hardy and Wright, *An Introduction to the Theory of Numbers*, §10.15, Theorem 182, and
Khinchin, *Continued Fractions*, Ch. II, §6, Theorem 17. -/
theorem abs_den_convergent_mul_sub_num_convergent_le (ξ : ℝ) (n : ℕ) {q : ℤ}
    (hq : q ≠ 0) (hq' : q.natAbs < (ξ.convergent (n + 1)).den) (p : ℤ) :
    |(ξ.convergent n).den * ξ - (ξ.convergent n).num| ≤ |q * ξ - p| := by
  rcases hq.lt_or_gt with h | h
  · have := abs_den_convergent_mul_sub_num_convergent_le_of_pos ξ n (q := -q) (by omega)
      (by omega) (-p)
    have hneg : ((-q : ℤ) : ℝ) * ξ - ((-p : ℤ) : ℝ) = -(q * ξ - p) := by push_cast; ring
    rwa [hneg, abs_neg] at this
  · exact abs_den_convergent_mul_sub_num_convergent_le_of_pos ξ n h (by omega) p

/-- **Lagrange's best approximation property**, measured in `UnitAddCircle`: for `0 < q < qₙ₊₁`,
the point `q ξ` is at least as far from an integer as `qₙ ξ` is from `pₙ`. -/
theorem abs_den_convergent_mul_sub_num_convergent_le_norm (ξ : ℝ) (n : ℕ) {q : ℕ}
    (hq : q ≠ 0) (hq' : q < (ξ.convergent (n + 1)).den) :
    |(ξ.convergent n).den * ξ - (ξ.convergent n).num| ≤ ‖((q * ξ : ℝ) : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  exact_mod_cast abs_den_convergent_mul_sub_num_convergent_le ξ n (q := q) (mod_cast hq)
    (by simpa using hq') (round ((q : ℝ) * ξ))

end Real
