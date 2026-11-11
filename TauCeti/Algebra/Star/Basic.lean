/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic

/-!
# Annihilators in rings with a proper star

In a star ring whose star is proper (`IsProperStar`: `star x * x = 0` forces `x = 0`), such as a
C⋆-algebra, an element killed by every two-sided multiplication `star d * X * c` vanishes. This is
how entrywise identities are read off from sesquilinear forms with coefficients in the ring, for
instance for matrices over a C⋆-algebra.

In particular, a ring with proper star has zero left and right annihilators. These are recorded
as the instances `FaithfulSMul Rᵐᵒᵖ R` and `FaithfulSMul R R` for the actions of `R` on itself by
right and left multiplication, which is how nondegeneracy enters the theory of double
centralizers.

## Main results

* `TauCeti.eq_zero_of_forall_star_mul_mul_eq_zero`: if `star d * X * c = 0` for all `c` and
  `d`, then `X = 0`.
* `TauCeti.faithfulSMul_mulOpposite_of_isProperStar`: if `c * x = c * y` for all `c`, then
  `x = y`.
* `TauCeti.faithfulSMul_of_isProperStar`: if `x * c = y * c` for all `c`, then `x = y`.
-/

public section

namespace TauCeti

variable {R : Type*} [NonUnitalSemiring R] [StarRing R] [IsProperStar R]

/-- In a star ring with proper star, an element annihilated by every two-sided multiplication
vanishes. -/
theorem eq_zero_of_forall_star_mul_mul_eq_zero {X : R} (h : ∀ c d : R, star d * X * c = 0) :
    X = 0 := by
  have h' : star (X * star X) * (X * star X) = 0 := by
    simpa [star_mul, mul_assoc] using h (star X) (X * star X)
  exact mul_star_self_eq_zero.mp (star_mul_self_eq_zero.mp h')

section Ring

variable {R : Type*} [NonUnitalRing R]

/-- In a ring with proper star, an element `x` with `c * x = 0` for every `c` vanishes:
the action of `Rᵐᵒᵖ` on `R` by right multiplication is faithful. -/
instance faithfulSMul_mulOpposite_of_isProperStar [Star R] [IsProperStar R] :
    FaithfulSMul Rᵐᵒᵖ R where
  eq_of_smul_eq_smul {x y} h := MulOpposite.unop_injective <| sub_eq_zero.mp <|
    star_mul_self_eq_zero.mp <| by
      simpa [mul_sub, sub_eq_zero, MulOpposite.smul_eq_mul_unop] using h (star (x.unop - y.unop))

/-- In a ring with proper involutive star, an element `x` with `x * c = 0` for every `c`
vanishes: the action of `R` on itself by left multiplication is faithful. -/
instance faithfulSMul_of_isProperStar [InvolutiveStar R] [IsProperStar R] :
    FaithfulSMul R R where
  eq_of_smul_eq_smul {x y} h := by
    have h' : star (star (x - y)) * star (x - y) = 0 := by
      simpa [sub_mul, sub_eq_zero] using h (star (x - y))
    have hs : star (x - y) = 0 := star_mul_self_eq_zero.mp h'
    exact sub_eq_zero.mp (star_mul_self_eq_zero.mp (by rw [hs, zero_mul]))

end Ring

end TauCeti
