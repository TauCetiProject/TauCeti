/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Fintype.BigOperators

/-!
# Vanishing products for three indexed arms

In an associative non-unital semiring, suppose each `u a * d a * u a` vanishes and the sum of the
products `u a * d a` vanishes. When there are at most three indices, every length-five
product through three such arms vanishes. The opposite-ring version gives the reversed product
under the corresponding assumption that each `d a * u a * d a` vanishes.
-/

public section

namespace TauCeti

/-! ### A vanishing identity for three arms -/

/-- In a non-unital semiring, let `u a` and `d a` be indexed by a type with at most three
elements, with `u a * d a * u a = 0` for every `a` and `∑ a, u a * d a = 0`. Then every product
`(u a * d a) * (u b * d b) * u c` vanishes. -/
theorem mul_mul_eq_zero_of_card_le_three {A L : Type*} [NonUnitalSemiring A] [Fintype L]
    (hL : Fintype.card L ≤ 3) (u d : L → A) (hudu : ∀ a, u a * d a * u a = 0)
    (hsum : ∑ a, u a * d a = 0) (a b c : L) :
    u a * d a * (u b * d b) * u c = 0 := by
  classical
  have hdiag (a : L) : u a * d a * (u a * d a) * u c = 0 := by
    simp only [← mul_assoc, hudu, zero_mul]
  have hlast (a : L) : u a * d a * (u c * d c) * u c = 0 := by
    rw [mul_assoc, hudu, mul_zero]
  have hrow (a : L) : ∑ b, u a * d a * (u b * d b) * u c = 0 := by
    simp only [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_zero, zero_mul]
  have hcol (b : L) : ∑ a, u a * d a * (u b * d b) * u c = 0 := by
    simp only [← Finset.sum_mul, hsum, zero_mul]
  -- For three distinct indices, the row sum at `a` has only the term at `b` left.
  have hdist (a b : L) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      u a * d a * (u b * d b) * u c = 0 := by
    refine (Fintype.sum_eq_single b fun b' hb' => ?_).symm.trans (hrow a)
    have := Finset.card_le_univ ({a, b, c, b'} : Finset L)
    grind
  rcases eq_or_ne b c with rfl | hbc
  · exact hlast a
  rcases eq_or_ne a b with rfl | hab
  · exact hdiag a
  rcases eq_or_ne a c with rfl | hac
  · -- The column sum at `b` has only the term at `a` left.
    refine (Fintype.sum_eq_single a fun a' ha' => ?_).symm.trans (hcol b)
    grind
  exact hdist a b hab hac hbc

/-- The dual form of `mul_mul_eq_zero_of_card_le_three`, read in the opposite ring: every product
`d c * (u b * d b) * (u a * d a)` vanishes, assuming the reversed length-three
products `d a * u a * d a` vanish and `∑ a, u a * d a = 0`. -/
theorem mul_mul_eq_zero_of_card_le_three' {A L : Type*} [NonUnitalSemiring A] [Fintype L]
    (hL : Fintype.card L ≤ 3) (u d : L → A) (hdud : ∀ a, d a * u a * d a = 0)
    (hsum : ∑ a, u a * d a = 0) (a b c : L) :
    d c * (u b * d b) * (u a * d a) = 0 := by
  have h := mul_mul_eq_zero_of_card_le_three hL (fun a => MulOpposite.op (d a))
    (fun a => MulOpposite.op (u a))
    (fun a => by simp only [← MulOpposite.op_mul, ← mul_assoc, hdud, MulOpposite.op_zero])
    (by simp only [← MulOpposite.op_mul, ← Finset.op_sum, hsum, MulOpposite.op_zero]) a b c
  apply MulOpposite.op_injective
  simpa only [← MulOpposite.op_mul, mul_assoc, MulOpposite.op_zero] using h

end TauCeti
