/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic

/-!
# Commutation with a universal diagonal matrix

Comparing monomial coefficients detects the off-diagonal entries of a matrix commuting with
a diagonalizable group, without requiring an infinite field or reduced coefficients.
The diagonal entries are universal characters in a monoid algebra, rather than scalar
values of those characters at a single point.

The coefficient argument follows
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Centralizer`.
-/

public section

open TensorProduct

namespace Matrix

/-- A constant matrix commuting with the universal diagonal matrix of monomial characters has
zero entries between distinct characters. The coefficient algebra may have nilpotents. -/
theorem apply_eq_zero_of_commute_diagonal_monomial
    {R A X ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Monoid X]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (χ : ι → X)
    (h : Commute
      (M.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] MonoidAlgebra R X))
      (diagonal fun i ↦ (1 : A) ⊗ₜ[R] MonoidAlgebra.single (χ i) (1 : R)))
    {i j : ι} (hij : χ j ≠ χ i) : M i j = 0 := by
  have he := congrArg (fun N : Matrix ι ι (A ⊗[R] MonoidAlgebra R X) ↦ N i j) h.eq
  simp only [mul_diagonal, diagonal_mul, map_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul] at he
  have hc := congrArg
    (LinearMap.tensorComponent (R := R) (M := A) (TauCeti.Comodule.monoidCoeff R X (χ i))) he
  simpa [MonoidAlgebra.coeff_single, hij] using hc.symm

end Matrix
