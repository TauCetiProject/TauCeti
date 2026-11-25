/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The equality case of Bergström's inequality

Bergström's inequality, also called Sedrakyan's or Titu's lemma, states that for `b > 0` on a
finset `s`, `(∑ i ∈ s, a i) ^ 2 / ∑ i ∈ s, b i ≤ ∑ i ∈ s, a i ^ 2 / b i`; Mathlib proves it as
`Finset.sq_sum_div_le_sum_sq_div`. This file computes the deficit of the inequality as a sum of
squares and deduces the equality case: equality holds exactly when `a` is a constant multiple of
`b` on `s`.

## Main results

* `Finset.sum_sq_div_sub_sq_sum_div`: in any field, if `b i ≠ 0` on `s` then
  `∑ a i ^ 2 / b i - (∑ a i) ^ 2 / ∑ b i = ∑ (a i - c * b i) ^ 2 / b i` with
  `c = (∑ a i) / ∑ b i`.
* `Finset.sq_sum_div_eq_sum_sq_div_iff`: in a linearly ordered field, if `b > 0` on `s` then
  `(∑ a i) ^ 2 / ∑ b i = ∑ a i ^ 2 / b i` if and only if `a i = c * b i` on `s` for some `c`.

## References

This is target 3.2 of the Tau Ceti roadmap `MeansMajorizationAndDiscreteInequalities`.
The Cauchy–Schwarz equality case `DLMF.AlgebraicAnalytic.sq_sum_mul_eq_iff` of lean-DLMF
(`DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean`) was consulted; the proof here does not use
inner product spaces and works in any linearly ordered field.
-/

public section

namespace Finset

variable {ι K : Type*} {s : Finset ι} {a b : ι → K}

/-- The deficit in Bergström's inequality is a sum of squares: if `b i ≠ 0` for `i ∈ s`, then
`∑ a i ^ 2 / b i - (∑ a i) ^ 2 / ∑ b i = ∑ (a i - c * b i) ^ 2 / b i`, where
`c = (∑ a i) / ∑ b i`. If `∑ b i = 0` then both sides equal `∑ a i ^ 2 / b i`. -/
theorem sum_sq_div_sub_sq_sum_div [Field K] (hb : ∀ i ∈ s, b i ≠ 0) :
    ∑ i ∈ s, a i ^ 2 / b i - (∑ i ∈ s, a i) ^ 2 / ∑ i ∈ s, b i =
      ∑ i ∈ s, (a i - (∑ j ∈ s, a j) / (∑ j ∈ s, b j) * b i) ^ 2 / b i := by
  set A := ∑ j ∈ s, a j
  set B := ∑ j ∈ s, b j
  -- Expand each square: `(a - c b) ^ 2 / b = a ^ 2 / b - 2 c a + c ^ 2 b`.
  have hterm : ∀ i ∈ s, (a i - A / B * b i) ^ 2 / b i =
      a i ^ 2 / b i - 2 * (A / B) * a i + (A / B) ^ 2 * b i := fun i hi ↦ by
    field_simp [hb i hi]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  obtain hB | hB := eq_or_ne B 0
  · simp [hB]
  · field_simp
    ring

/-- **Equality case of Bergström's inequality** (Sedrakyan's or Titu's lemma). If `b > 0` on `s`,
then `(∑ a i) ^ 2 / ∑ b i = ∑ a i ^ 2 / b i` if and only if `a` is a constant multiple of `b`
on `s`. For empty `s` both sides are `0` and the condition holds. The inequality itself is
`Finset.sq_sum_div_le_sum_sq_div`. -/
theorem sq_sum_div_eq_sum_sq_div_iff [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) ^ 2 / ∑ i ∈ s, b i = ∑ i ∈ s, a i ^ 2 / b i ↔
      ∃ c : K, ∀ i ∈ s, a i = c * b i := by
  constructor
  · intro h
    refine ⟨(∑ j ∈ s, a j) / ∑ j ∈ s, b j, fun i hi ↦ ?_⟩
    have hsum := sum_sq_div_sub_sq_sum_div (a := a) fun i hi ↦ (hb i hi).ne'
    rw [h, sub_self, eq_comm, sum_eq_zero_iff_of_nonneg
      fun i hi ↦ div_nonneg (sq_nonneg _) (hb i hi).le] at hsum
    have := hsum i hi
    rw [div_eq_zero_iff, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at this
    exact this.resolve_right (hb i hi).ne'
  · rintro ⟨c, hc⟩
    have hA : ∑ i ∈ s, a i = c * ∑ i ∈ s, b i := by
      rw [mul_sum]
      exact sum_congr rfl hc
    have hA2 : ∑ i ∈ s, a i ^ 2 / b i = c ^ 2 * ∑ i ∈ s, b i := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi ↦ ?_
      rw [hc i hi]
      field_simp [(hb i hi).ne']
    rw [hA, hA2, mul_pow, sq (∑ i ∈ s, b i), mul_div_assoc, mul_self_div_self]

end Finset
