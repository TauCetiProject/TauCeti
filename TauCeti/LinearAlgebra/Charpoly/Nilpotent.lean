/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import TauCeti.LinearAlgebra.Charpoly.Projective
public import TauCeti.Algebra.Polynomial.Reverse

/-!
# Characteristic polynomials of scalar plus nilpotent endomorphisms

On a finite free module over an integral domain, an endomorphism whose difference from
`μ • 1` is nilpotent has characteristic polynomial `(X - μ) ^ finrank R M`.
Its reversed characteristic polynomial is `(1 - μ X) ^ finrank R M`, including `μ = 0`.
These formulas identify the determinant factor contributed by a generalised eigenspace.
They extend Mathlib's `IsNilpotent.charpoly_eq_X_pow_finrank` by scalar translation.
-/

public section

namespace LinearMap

open Polynomial Module

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- A scalar plus a nilpotent endomorphism has only that scalar in its characteristic
polynomial, counted with the full rank of the module. -/
theorem charpoly_eq_pow_of_isNilpotent_sub_smul (f : Module.End R M) (μ : R)
    (hf : IsNilpotent (f - μ • 1)) :
    f.charpoly = (X - C μ) ^ finrank R M := by
  have h := congrArg (fun p : R[X] ↦ p.comp (X - C μ)) hf.charpoly_eq_X_pow_finrank
  rw [charpoly_sub_smul] at h
  simpa [Polynomial.comp_assoc, sub_eq_add_neg] using h

/-- The determinant `det (1 - X f)` of a scalar plus a nilpotent endomorphism, including
the nilpotent case `μ = 0` and the zero module. -/
theorem projectiveCharpolyRev_eq_pow_of_isNilpotent_sub_smul (f : Module.End R M) (μ : R)
    (hf : IsNilpotent (f - μ • 1)) :
    f.projectiveCharpolyRev = (1 - C μ * X) ^ finrank R M := by
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
