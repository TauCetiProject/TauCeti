/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.RingTheory.MvPolynomial.PolynomialOperator

/-!
# The `sl₂`-triple of binary forms

In two variables, with `x = X 0` and `y = X 1`, the raising operator `E = x ∂_y`, the lowering
operator `F = y ∂_x` and `H = ⁅E, F⁆ = x ∂_x - y ∂_y` (see `TauCeti.polynomialOperator`) form an
`sl₂`-triple of derivations of `R[x, y]` (`TauCeti.isSl2Triple_polynomialOperator`). The binary
monomial `e_i = x ^ (d - i) * y ^ i` has weight `d - 2i`, and `x ^ d` is a primitive vector of
weight `d`.

## Main results

* `TauCeti.lie_polynomialOperator_zero_one_one_zero_polynomialMonomial`: `H e_i = (d - 2i) e_i`.
* `TauCeti.hasPrimitiveVectorWith_X_zero_pow`: `x ^ d` is a primitive vector of weight `d`.

## References

* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, pp. 62–64: the
  representations of `sl₂` on homogeneous polynomials in two variables and their ladder.
-/

public section

open MvPolynomial

namespace TauCeti

variable {R : Type*} [CommRing R] {d i : ℕ}

/-- **The weights of the binary monomials**: `H = ⁅x ∂_y, y ∂_x⁆` multiplies `e_i` by `d - 2i`. -/
theorem lie_polynomialOperator_zero_one_one_zero_polynomialMonomial :
    ⁅polynomialOperator R (0 : Fin 2) 1, polynomialOperator R (1 : Fin 2) 0⁆
        (polynomialMonomial R d i) =
      ((d : R) - 2 * i) • polynomialMonomial R d i := by
  rcases le_or_gt i d with h | h
  · rw [lie_polynomialOperator_zero_one_one_zero, sub_apply,
      polynomialOperator_zero_zero_polynomialMonomial,
      polynomialOperator_one_one_polynomialMonomial, ← sub_smul, Nat.cast_sub h]
    congr 1
    ring
  · simp [polynomialMonomial_of_lt h]

/-- The binary monomial `x ^ d` is a primitive vector of weight `d` for the `sl₂`-triple of
binary forms. -/
theorem hasPrimitiveVectorWith_X_zero_pow [Nontrivial R] (d : ℕ) :
    (isSl2Triple_polynomialOperator R (show (0 : Fin 2) ≠ 1 by decide)).HasPrimitiveVectorWith
      (X 0 ^ d : MvPolynomial (Fin 2) R) (d : R) where
  ne_zero := by simp [X_pow_eq_monomial]
  lie_h := by
    rw [Derivation.bracket_eq_fun]
    have := lie_polynomialOperator_zero_one_one_zero_polynomialMonomial (R := R) (d := d) (i := 0)
    simpa [lie_polynomialOperator_zero_one_one_zero, polynomialMonomial_zero_right] using this
  lie_e := by
    rw [Derivation.bracket_eq_fun]
    simp

end TauCeti
