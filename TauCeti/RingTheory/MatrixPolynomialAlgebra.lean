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

/-- The underlying ring homomorphism of the extension is Mathlib's `RingHom.polyToMatrix`. -/
theorem toRingHom_polynomialExtension (ρ : Λ →ₐ[R] Matrix σ σ L) :
    (polynomialExtension ρ).toRingHom = ρ.toRingHom.polyToMatrix := (rfl)

/-- Coefficients of the extension are obtained by applying the original matrix homomorphism. -/
@[simp] theorem coeff_polynomialExtension_apply (ρ : Λ →ₐ[R] Matrix σ σ L) (p : Λ[X]) (s t : σ)
    (k : ℕ) : (polynomialExtension ρ p s t).coeff k = ρ (p.coeff k) s t := by
  simp [polynomialExtension, RingHom.polyToMatrix, matPolyEquiv_symm_apply_coeff]

/-- A constant polynomial is sent to the image of its coefficient, with constant entries. -/
@[simp] theorem polynomialExtension_C (ρ : Λ →ₐ[R] Matrix σ σ L) (w : Λ) :
    polynomialExtension ρ (C w) = (ρ w).map C := by
  ext s t k
  simp [coeff_C, apply_ite (ρ · s t)]

/-- The variable is sent to the diagonal matrix with entries `X`. -/
@[simp] theorem polynomialExtension_X (ρ : Λ →ₐ[R] Matrix σ σ L) :
    polynomialExtension ρ X = diagonal fun _ ↦ X := by
  have h := (polynomialExtension ρ).commutes X
  rw [Polynomial.algebraMap_def, coe_mapRingHom, map_X] at h
  rw [h, algebraMap_eq_diagonal]
  congr 1
  ext
  simp [Polynomial.algebraMap_def]

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
@[simp] theorem matrixPolynomialMulRightAction_apply (ρ₀ : Λ) (M : Matrix N N Λ[X]) (v : N → Λ)
    (i : N) : matrixPolynomialMulRightAction R ρ₀ M v i =
      ∑ j, polynomialMulRightAction R ρ₀ (M i j) (v j) := (rfl)

attribute [local instance] Polynomial.algebra in
/-- The scalar matrix of `F : R[X]` acts by right multiplication by `aeval ρ₀ F`. -/
@[simp] theorem matrixPolynomialMulRightAction_algebraMap (ρ₀ : Λ) (F : R[X]) (v : N → Λ) :
    matrixPolynomialMulRightAction R ρ₀ (algebraMap R[X] (Matrix N N Λ[X]) F) v =
      fun i ↦ v i * aeval ρ₀ F := by
  ext i
  rw [matrixPolynomialMulRightAction_apply, Finset.sum_eq_single i
    (fun j _ hj ↦ by simp [algebraMap_matrix_apply, Ne.symm hj]) (by simp)]
  simp [algebraMap_matrix_apply, polynomialMulRightAction_map_algebraMap]

end TauCeti
