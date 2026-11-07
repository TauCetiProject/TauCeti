/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Basic

/-! # Lagrange indicators for signs

`SignType.lagrangeCoeff` gives the coefficients of the three indicator polynomials
`1 - x²`, `(x² - x) / 2`, and `(x² + x) / 2` on `{-1,0,1}`, in any division ring.
`SignType.sum_lagrangeCoeff_mul_pow` evaluates these indicators on signs when `2 ≠ 0`,
supplying the one-coordinate inverse in finite sign determination.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 10, for the ternary sign-moment inverse.
-/

public section

namespace SignType

variable {K : Type*} [DivisionRing K]

/-- Coefficients of the three Lagrange indicator polynomials on `{-1,0,1}`: when `(2 : K) ≠ 0`,
the coefficient of `x ^ e` in the polynomial that is `1` at the sign `s` and `0` at the other
two signs (see `sum_lagrangeCoeff_mul_pow`). In characteristic `2`, `1 / 2 = 0`, so this
indicator property fails. -/
def lagrangeCoeff (s : SignType) (e : Fin 3) : K :=
  match s with
  | .zero => if e = 0 then 1 else if e = 2 then -1 else 0
  | .neg => if e = 1 then -1/2 else if e = 2 then 1/2 else 0
  | .pos => if e = 1 then 1/2 else if e = 2 then 1/2 else 0

@[grind =]
theorem lagrangeCoeff_zero (e : Fin 3) :
    (lagrangeCoeff 0 e : K) = if e = 0 then 1 else if e = 2 then -1 else 0 := (rfl)

@[grind =]
theorem lagrangeCoeff_neg_one (e : Fin 3) :
    (lagrangeCoeff (-1) e : K) = if e = 1 then -1/2 else if e = 2 then 1/2 else 0 := (rfl)

@[grind =]
theorem lagrangeCoeff_one (e : Fin 3) :
    (lagrangeCoeff 1 e : K) = if e = 1 then 1/2 else if e = 2 then 1/2 else 0 := (rfl)

/-- Each Lagrange indicator evaluates to one at its own sign and zero at the other signs. -/
@[simp]
theorem sum_lagrangeCoeff_mul_pow [NeZero (2 : K)] (s t : SignType) :
    ∑ e : Fin 3, lagrangeCoeff s e * (t : K) ^ e.val = if s = t then 1 else 0 := by
  cases s <;> cases t <;>
    simp [Fin.sum_univ_three, lagrangeCoeff, neg_div, ← two_mul, two_ne_zero]

end SignType
