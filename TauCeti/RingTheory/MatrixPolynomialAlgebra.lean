/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MatrixPolynomialAlgebra
public import TauCeti.RingTheory.Polynomial.MulRightAction
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Algebra homomorphisms and actions of polynomial matrices

`AlgHom.polynomialExtension` extends a matrix-valued algebra homomorphism coefficientwise,
retaining compatibility with scalars over the polynomial ring.
`TauCeti.matrixPolynomialMulRightAction` lifts the polynomial action by right multiplication
to vectors, using the equivalence between matrices of endomorphisms and vector endomorphisms.
Together these constructions transport polynomial matrix relations to algebra elements.
-/

public section

open Polynomial Matrix

namespace AlgHom

variable {R L Λ σ : Type*} [CommSemiring R] [CommSemiring L] [Algebra R L]
  [Semiring Λ] [Algebra R Λ] [Fintype σ] [DecidableEq σ]

attribute [local instance] Polynomial.algebra

/-- The coefficientwise extension `Λ[X] →ₐ[R[X]] Matrix σ σ L[X]` of `ρ : Λ →ₐ[R] Matrix σ σ L`. -/
noncomputable def polynomialExtension (ρ : Λ →ₐ[R] Matrix σ σ L) :
    Λ[X] →ₐ[R[X]] Matrix σ σ L[X] where
  toRingHom := ρ.toRingHom.polyToMatrix
  commutes' q := by
    ext s t k
    simp only [algebraMap_matrix_apply]
    split_ifs <;>
      simp [RingHom.polyToMatrix, matPolyEquiv_symm_apply_coeff, algebraMap_matrix_apply, *]

/-- Coefficients of the extension are obtained by applying the original matrix homomorphism. -/
@[simp] theorem coeff_polynomialExtension_apply (ρ : Λ →ₐ[R] Matrix σ σ L) (p : Λ[X]) (s t : σ)
    (k : ℕ) : (polynomialExtension ρ p s t).coeff k = ρ (p.coeff k) s t := by
  simp [polynomialExtension, RingHom.polyToMatrix, matPolyEquiv_symm_apply_coeff]

end AlgHom

namespace TauCeti

variable {R Λ N : Type*} [CommSemiring R] [Semiring Λ] [Algebra R Λ]
  [Fintype N] [DecidableEq N]

variable (R) in
/-- Matrices over `Λ[X]` act on vectors through `polynomialMulRightAction R ρ₀`.
Multiplication and addition are preserved by this ring homomorphism. -/
noncomputable def matrixPolynomialMulRightAction (ρ₀ : Λ) :
    Matrix N N Λ[X] →+* Module.End R (N → Λ) :=
  (endVecRingEquivMatrixEnd N R Λ).symm.toRingHom.comp
    (polynomialMulRightAction R ρ₀).mapMatrix

/-- The vector action is the row sum of the entrywise polynomial actions. -/
theorem matrixPolynomialMulRightAction_apply (ρ₀ : Λ) (M : Matrix N N Λ[X]) (v : N → Λ)
    (i : N) : matrixPolynomialMulRightAction R ρ₀ M v i =
      ∑ j, polynomialMulRightAction R ρ₀ (M i j) (v j) := (rfl)

end TauCeti
