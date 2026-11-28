/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Unitary.Basic
public import TauCeti.Algebra.Ring.CayleyChart
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

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
  let c (q : ℚ) : K := cayleyCoord 1 ((q : K) * a)
  have hc_eq (q : ℚ) : c q = (1 - (q : K) * a) / (1 + (q : K) * a) := by
    simp only [c, cayleyCoord_def, Ring.inverse_eq_inv, div_eq_mul_inv]
  have hc (q : ℚ) : c q ∈ unitary K := by
    rw [Unitary.mem_iff_star_mul_self]
    simp only [hc_eq, star_div₀, star_sub, star_one, star_mul, star_ratCast, ha,
      star_add]
    have hnum : 1 - (q : K) * a ≠ 0 := by
      simpa only [Rat.cast_neg, neg_mul, sub_eq_add_neg] using hden (-q)
    simp only [neg_mul, sub_neg_eq_add, mul_comm a (q : K)]
    field_simp [hden q, hnum]
    rw [← sub_eq_add_neg, div_self hnum]
  let u (q : ℚ) : unitary K := ⟨c q, hc q⟩
  refine Infinite.of_injective u fun p q h ↦ ?_
  have heq : c p = c q := congrArg Subtype.val h
  have hmul : (p : K) * a = (q : K) * a := by
    simpa only [c, cayleyCoord_one_cayleyCoord_one (isUnit_iff_ne_zero.2 two_ne_zero)
      (isUnit_iff_ne_zero.2 (hden _))] using congrArg (cayleyCoord 1) heq
  exact Rat.cast_injective (mul_right_cancel₀ ha0 hmul)

/-- A characteristic-zero field with a nontrivial involution has infinitely many
norm-one elements. -/
theorem infinite_unitary_of_exists_star_ne (hstar : ∃ x : K, star x ≠ x) :
    Infinite (unitary K) := by
  obtain ⟨x, hx⟩ := hstar
  exact infinite_unitary_of_skew (a := x - star x) (by simp [star_sub])
    (sub_ne_zero.2 hx.symm)

end TauCeti
