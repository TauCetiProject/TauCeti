/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The symmetric algebra of the base semiring as univariate polynomials

For any commutative semiring `R`, the symmetric algebra `SymmetricAlgebra R R` of the rank-one free
module `R` is canonically `R`-algebra isomorphic to the univariate polynomial algebra `R[X]`,
sending the generator `SymmetricAlgebra.ι R R 1` to `Polynomial.X`.

## Main definitions

* `SymmetricAlgebra.equivPolynomial`: the canonical `R`-algebra equivalence
  `SymmetricAlgebra R R ≃ₐ[R] R[X]`.
-/

public section

open Polynomial

namespace SymmetricAlgebra

universe u

variable (R : Type u) [CommSemiring R]

/-- Canonical `R`-algebra equivalence `SymmetricAlgebra R R ≃ₐ[R] R[X]` sending `ι R R 1` to `X`. -/
noncomputable def equivPolynomial : SymmetricAlgebra R R ≃ₐ[R] R[X] :=
  AlgEquiv.ofAlgHom
    (SymmetricAlgebra.lift (LinearMap.toSpanSingleton R R[X] X))
    (aeval (SymmetricAlgebra.ι R R 1))
    (Polynomial.algHom_ext <| by simp)
    (SymmetricAlgebra.algHom_ext <| LinearMap.ext_ring <| by simp)

/-- `equivPolynomial` sends the generator `ι R R 1` to `X`. -/
@[simp]
theorem equivPolynomial_ι_one : equivPolynomial R (ι R R 1) = X := by
  simp [equivPolynomial]

/-- The inverse of `equivPolynomial` sends `X` to `ι R R 1`. -/
@[simp]
theorem equivPolynomial_symm_X : (equivPolynomial R).symm X = ι R R 1 := by
  simp [equivPolynomial]

end SymmetricAlgebra
