/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import TauCeti.Algebra.Order.Ring.Basic

/-!
# The equality case of Bergström's inequality

Bergström's inequality, also called Sedrakyan's or Titu's lemma, states that for `b > 0` on a
finset `s`, `(∑ i ∈ s, a i) ^ 2 / ∑ i ∈ s, b i ≤ ∑ i ∈ s, a i ^ 2 / b i`; Mathlib proves it as
`Finset.sq_sum_div_le_sum_sq_div`. This file proves the equality case: equality holds exactly when
`a` is a constant multiple of `b` on `s`. Over a field the deficit of the inequality is the sum of
squares `Finset.sum_sq_div_sub_sq_sum_div`.

## Main results

* `TauCeti.sq_sum_div_eq_sum_sq_div_iff`: in a linearly ordered semifield, if `b > 0` on `s`
  then `(∑ a i) ^ 2 / ∑ b i = ∑ a i ^ 2 / b i` if and only if `a i = c * b i` on `s` for some
  `c`.

The proof applies the equality case `TauCeti.two_mul_eq_add_sq_iff` of the AM-GM inequality to
each term of `2 c a i ≤ a i ^ 2 / b i + c ^ 2 b i`, with `c = (∑ a i) / ∑ b i`; the two sides of
this termwise inequality have equal sums exactly in the equality case of Bergström's inequality.

## References

The Cauchy–Schwarz equality case `DLMF.AlgebraicAnalytic.sq_sum_mul_eq_iff` of lean-DLMF
(<https://github.com/bjbraams/lean-DLMF>, `DLMF/AlgebraicAnalytic/Calculus/Inequalities.lean`)
was consulted; the proof here does not use inner product spaces and works in any linearly ordered
semifield.
-/

public section

namespace TauCeti

open Finset

variable {ι K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [ExistsAddOfLE K]
  {s : Finset ι} {a b : ι → K}

/-- **Equality case of Bergström's inequality** (Sedrakyan's or Titu's lemma). If `b > 0` on `s`,
then `(∑ a i) ^ 2 / ∑ b i = ∑ a i ^ 2 / b i` if and only if `a` is a constant multiple of `b`
on `s`. For empty `s` both sides are `0` and the condition holds. The inequality itself is
`Finset.sq_sum_div_le_sum_sq_div`. -/
theorem sq_sum_div_eq_sum_sq_div_iff (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) ^ 2 / ∑ i ∈ s, b i = ∑ i ∈ s, a i ^ 2 / b i ↔
      ∃ c : K, ∀ i ∈ s, a i = c * b i := by
  constructor
  · intro h
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨0, by simp⟩
    set A := ∑ i ∈ s, a i
    set B := ∑ i ∈ s, b i
    have hB : 0 < B := sum_pos hb hs
    refine ⟨A / B, fun i hi ↦ ?_⟩
    -- Termwise AM-GM: `2 c a j ≤ a j ^ 2 / b j + c ^ 2 b j` with `c = A / B`. The two sides
    -- have equal sums by `h`, so every term is an equality.
    have hle : ∀ j ∈ s, 2 * (A / B) * a j ≤ a j ^ 2 / b j + (A / B) ^ 2 * b j := fun j hj ↦ by
      have := two_mul_le_add_sq (a j) (A / B * b j)
      rw [← mul_le_mul_iff_of_pos_right (hb j hj)]
      convert this using 1 <;> field_simp [(hb j hj).ne']
    have hsum : ∑ j ∈ s, 2 * (A / B) * a j = ∑ j ∈ s, (a j ^ 2 / b j + (A / B) ^ 2 * b j) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← h]
      field_simp
      ring
    have heq := congrArg (· * b i) ((sum_eq_sum_iff_of_le hle).mp hsum i hi)
    refine two_mul_eq_add_sq_iff.mp ?_
    convert heq using 1 <;> field_simp [(hb i hi).ne']
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

end TauCeti
