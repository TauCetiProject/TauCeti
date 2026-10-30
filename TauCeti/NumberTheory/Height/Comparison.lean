/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.MahlerMeasure
public import TauCeti.NumberTheory.Height.Naive

/-!
# Comparison of naive height and Mahler measure

The naive height of an algebraic number is the coefficient sup norm of its primitive minimal
polynomial, while its Mahler measure records the sizes of the roots as well as the leading
coefficient. The standard coefficient estimate and Landau's inequality compare these two size
functions in terms of the degree of the rational minimal polynomial.

The statements include transcendental elements under the conventions that their primitive
minimal polynomial is `1`, their rational minimal polynomial is `0`, and both heights are `1`.
They provide the polynomial estimates used to compare naive, Mahler, and absolute heights.

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), Chapter 6, Theorem 6.1.
* Xiaorun Wu, *Diophantine geometry, week 08: arithmetic heights* (2023), Lemma 3.3.
-/

public section

open Polynomial

namespace TauCeti

local instance : RingHomIsometric (Int.castRingHom ℂ) where
  norm_map := by simp [Int.norm_eq_abs]

variable {F : Type*} [Field F] [CharZero F]

/-- The rational minimal polynomial has the same degree as the primitive minimal polynomial
mapped to `ℂ`. -/
private theorem natDegree_map_primitiveMinpoly (x : F) :
    ((primitiveMinpoly x).map (Int.castRingHom ℂ)).natDegree = (minpoly ℚ x).natDegree := by
  rw [natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℂ)),
    natDegree_primitiveMinpoly]

/-- The naive height is at most the middle binomial coefficient times the Mahler measure. -/
theorem naiveHeight_le_choose_natDegree_div_two_mul_mahlerMeasure (x : F) :
    naiveHeight x ≤
      (minpoly ℚ x).natDegree.choose ((minpoly ℚ x).natDegree / 2) * mahlerMeasure x := by
  rw [naiveHeight_def, mahlerMeasure_def,
    ← supNorm_map _ (Int.castRingHom ℂ),
    ← natDegree_map_primitiveMinpoly x]
  exact supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure _

/-- The naive height is at most `2 ^ d` times the Mahler measure, where `d` is the degree of the
rational minimal polynomial. -/
theorem naiveHeight_le_two_pow_mul_mahlerMeasure (x : F) :
    naiveHeight x ≤ 2 ^ (minpoly ℚ x).natDegree * mahlerMeasure x :=
  (naiveHeight_le_choose_natDegree_div_two_mul_mahlerMeasure x).trans <| by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast (Nat.choose_le_two_pow
        (minpoly ℚ x).natDegree ((minpoly ℚ x).natDegree / 2))
    · exact zero_le_one.trans (one_le_mahlerMeasure x)

/-- Landau's inequality for an algebraic number: its Mahler measure is at most its naive height
times the square root of one plus the degree of its rational minimal polynomial. -/
theorem mahlerMeasure_le_sqrt_natDegree_add_one_mul_naiveHeight (x : F) :
    mahlerMeasure x ≤ Real.sqrt ((minpoly ℚ x).natDegree + 1) * naiveHeight x := by
  rw [naiveHeight_def, mahlerMeasure_def,
    ← supNorm_map _ (Int.castRingHom ℂ),
    ← natDegree_map_primitiveMinpoly x]
  exact mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _

end TauCeti
