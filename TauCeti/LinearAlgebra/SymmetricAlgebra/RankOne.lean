/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Polynomial coordinates on the rank-one symmetric algebra

The symmetric algebra `SymmetricAlgebra R R` of the free module of rank one is the polynomial
algebra `R[X]` on the generator `ι R R 1`, and its tensor square is the bivariate polynomial
algebra `R[X][Y]`, the left factor giving the variable `X` and the right factor the variable `Y`.
This is the univariate counterpart of Mathlib's `SymmetricAlgebra.equivMvPolynomial`, which needs
a basis and lands in `MvPolynomial`.

## Main definitions

* `SymmetricAlgebra.equivPolynomial`: `SymmetricAlgebra R R ≃ₐ[R] R[X]`, sending `ι R R 1` to `X`.
* `SymmetricAlgebra.tensorEquivBivariate`:
  `SymmetricAlgebra R R ⊗[R] SymmetricAlgebra R R ≃ₐ[R] R[X][Y]`.

## Main results

* `SymmetricAlgebra.equivPolynomial_ι_one`: `ι R R 1` corresponds to `X`.
* `SymmetricAlgebra.equivPolynomial_symm_apply`: a polynomial `f` corresponds to `f(ι R R 1)`.
* `SymmetricAlgebra.tensorEquivBivariate_tmul`: `a ⊗ b` corresponds to `a(X) * b(Y)`.
-/

public section

open Polynomial Polynomial.Bivariate TensorProduct

namespace SymmetricAlgebra

variable {R : Type*} [CommSemiring R]

/-- The rank-one symmetric algebra is the polynomial algebra on `ι R R 1`. -/
noncomputable def equivPolynomial : SymmetricAlgebra R R ≃ₐ[R] R[X] :=
  .ofAlgHom (lift (LinearMap.toSpanSingleton R R[X] X)) (aeval (ι R R 1))
    (by ext; simp) (by ext; simp)

/-- Under `equivPolynomial`, a polynomial `f` corresponds to `f(ι R R 1)`. -/
theorem equivPolynomial_symm_apply (f : R[X]) :
    equivPolynomial.symm f = aeval (ι R R 1) f := by
  rw [equivPolynomial]
  rfl

/-- Under `equivPolynomial`, the generator `ι R R 1` corresponds to `X`. -/
@[simp]
theorem equivPolynomial_ι_one : equivPolynomial (ι R R 1) = X := by
  simp [equivPolynomial]

/-- Under `equivPolynomial`, the variable `X` corresponds to the generator `ι R R 1`. -/
@[simp]
theorem equivPolynomial_symm_X : equivPolynomial.symm (X : R[X]) = ι R R 1 := by
  simp [equivPolynomial_symm_apply]

/-- The tensor square of the rank-one symmetric algebra is the bivariate polynomial algebra, the
left factor giving the variable `X` and the right factor the variable `Y`. -/
noncomputable def tensorEquivBivariate :
    SymmetricAlgebra R R ⊗[R] SymmetricAlgebra R R ≃ₐ[R] R[X][Y] :=
  (Algebra.TensorProduct.congr equivPolynomial equivPolynomial).trans
    (polyEquivTensor R R[X]).symm

/-- Under `tensorEquivBivariate`, a pure tensor `a ⊗ b` corresponds to `a(X) * b(Y)`. -/
@[simp]
theorem tensorEquivBivariate_tmul (a b : SymmetricAlgebra R R) :
    tensorEquivBivariate (a ⊗ₜ[R] b) = C (equivPolynomial a) * (equivPolynomial b).map C := by
  simp [tensorEquivBivariate, smul_eq_C_mul, ← Polynomial.algebraMap_eq]

end SymmetricAlgebra
