/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Infinitely many norm-one elements

A characteristic-zero field with a nontrivial involution has infinitely many
norm-one elements. A nonzero skew element `a` gives the injective rational family
`q ↦ (1 - q a) / (1 + q a)`. In particular scalar unitary matrices provide infinitely
many translates for avoiding the complement of a Cayley chart.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [StarRing K] [CharZero K]

/-- A nonzero skew element in a characteristic-zero field produces infinitely many
norm-one elements by rational parametrization. -/
theorem infinite_unitary_of_skew {a : K} (ha : star a = -a) (ha0 : a ≠ 0) :
    Infinite (unitary K) := by
  have hden (q : ℚ) : 1 + (q : K) * a ≠ 0 := by
    intro h
    have hs := congrArg star h
    simp only [star_add, star_one, star_mul, star_ratCast, ha, star_zero] at hs
    have ht : (2 : K) = 0 := by linear_combination h + hs
    exact two_ne_zero ht
  let c (q : ℚ) : K := (1 - (q : K) * a) / (1 + (q : K) * a)
  have hc (q : ℚ) : c q ∈ unitary K := by
    rw [Unitary.mem_iff_star_mul_self]
    simp only [c, star_div₀, star_sub, star_one, star_mul, star_ratCast, ha,
      star_add]
    have hnum : 1 - (q : K) * a ≠ 0 := by
      simpa only [Rat.cast_neg, neg_mul, sub_eq_add_neg] using hden (-q)
    simp only [neg_mul, sub_neg_eq_add, mul_comm a (q : K)]
    field_simp [hden q, hnum]
    rw [← sub_eq_add_neg, div_self hnum]
  let u (q : ℚ) : unitary K := ⟨c q, hc q⟩
  refine Infinite.of_injective u fun p q h ↦ ?_
  have heq : c p = c q := congrArg Subtype.val h
  have hcross := (div_eq_div_iff (hden p) (hden q)).1 heq
  have hzero : ((p : K) - (q : K)) * a = 0 := by
    linear_combination -hcross / 2
  exact Rat.cast_injective (sub_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_right ha0))

/-- A characteristic-zero field with a nontrivial involution has infinitely many
norm-one elements. -/
theorem infinite_unitary_of_exists_star_ne (hstar : ∃ x : K, star x ≠ x) :
    Infinite (unitary K) := by
  obtain ⟨x, hx⟩ := hstar
  exact infinite_unitary_of_skew (a := x - star x) (by simp [star_sub])
    (sub_ne_zero.2 hx.symm)

end TauCeti
