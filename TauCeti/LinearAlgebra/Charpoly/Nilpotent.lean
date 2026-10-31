/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.Charpoly.Projective
public import TauCeti.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Characteristic polynomials of scalar plus nilpotent endomorphisms

On a finite free module over a reduced commutative ring, an endomorphism whose difference from
`μ • 1` is nilpotent has characteristic polynomial `(X - μ) ^ finrank R M`.
Its reversed characteristic polynomial is `(1 - μ X) ^ finrank R M`, including `μ = 0`.
These formulas identify the determinant factor contributed by a generalised eigenspace.

The case `μ = 0`, `LinearMap.charpoly_eq_X_pow_finrank_of_isNilpotent`, generalizes Mathlib's
`IsNilpotent.charpoly_eq_X_pow_finrank` from integral domains to reduced rings. Reducedness is
needed: over `k[ε]` with `ε ^ 2 = 0`, the nilpotent scalar `ε` has characteristic polynomial
`X - ε` on `k[ε]`, not `X`.
-/

public section

namespace LinearMap

open Polynomial Module

variable {R M : Type*} [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- Over a reduced commutative ring, a nilpotent endomorphism of a finite free module has
characteristic polynomial `X ^ finrank R M`. -/
theorem charpoly_eq_X_pow_finrank_of_isNilpotent {f : Module.End R M} (hf : IsNilpotent f) :
    f.charpoly = X ^ finrank R M := by
  -- This follows Mathlib's `IsNilpotent.charpoly_eq_X_pow_finrank`, replacing its final domain
  -- step by the coefficientwise criterion `Polynomial.isNilpotent_iff`.
  nontriviality R
  let b := Free.chooseBasis R M
  have hmat : toMatrixAlgEquiv b f = toMatrix b b f := by
    ext i j
    rw [toMatrixAlgEquiv_apply, toMatrix_apply]
  have hP :=
    Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent (hmat ▸ hf.map (toMatrixAlgEquiv b))
  rw [charpoly_toMatrix, ← finrank_eq_card_chooseBasisIndex] at hP
  rw [← sub_eq_zero]
  ext i
  simpa using (Polynomial.isNilpotent_iff.mp hP i).eq_zero

/-- A scalar plus a nilpotent endomorphism has only that scalar in its characteristic
polynomial, counted with the full rank of the module. -/
theorem charpoly_eq_pow_of_isNilpotent_sub_smul (f : Module.End R M) (μ : R)
    (hf : IsNilpotent (f - μ • 1)) :
    f.charpoly = (X - C μ) ^ finrank R M := by
  have h := congrArg (fun p : R[X] ↦ p.comp (X - C μ))
    (charpoly_eq_X_pow_finrank_of_isNilpotent hf)
  rw [charpoly_sub_smul] at h
  simpa [Polynomial.comp_assoc, sub_eq_add_neg] using h

/-- The determinant `det (1 - X f)` of a scalar plus a nilpotent endomorphism, including
the nilpotent case `μ = 0` and the zero module. -/
theorem projectiveCharpolyRev_eq_pow_of_isNilpotent_sub_smul (f : Module.End R M) (μ : R)
    (hf : IsNilpotent (f - μ • 1)) :
    f.projectiveCharpolyRev = (1 - C μ * X) ^ finrank R M := by
  nontriviality R
  rw [projectiveCharpolyRev_eq_reverse_charpoly, Polynomial.reverse, charpoly_natDegree,
    charpoly_eq_pow_of_isNilpotent_sub_smul f μ hf]
  have hlinear : (X - C μ : R[X]).reflect 1 = 1 - C μ * X := by
    rw [reflect_sub, reflect_one_X, reflect_C, pow_one]
  calc
    _ = (X - C μ : R[X]).reflect 1 ^ finrank R M := by
      simpa only [Nat.mul_one] using
        reflect_pow (X - C μ) (N := 1) (by simp) (finrank R M)
    _ = _ := congrArg (fun p : R[X] ↦ p ^ finrank R M) hlinear

end LinearMap
