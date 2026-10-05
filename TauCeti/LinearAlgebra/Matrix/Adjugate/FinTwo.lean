/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis

/-!
# Adjugation of two-by-two matrices

The adjugate of a two-by-two matrix is linear over any commutative ring, including in
characteristic two. It is the unique function reversing products for which every matrix plus its
image is scalar; linearity is not needed for this characterization. These facts identify Clifford
reversal with adjugation in the two-by-two matrix model of Spin(3).

For complex matrices, composing adjugation with conjugate transpose gives a real-algebra
endomorphism. This packages the multiplicative map used by real low-rank matrix models.
-/

public section

namespace Matrix

variable {K : Type*} [CommRing K]

/-- The adjugate of a two-by-two matrix is its trace times the identity minus itself. -/
@[simp]
theorem adjugate_fin_two_eq_trace_smul_one_sub (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix.adjugate A = Matrix.trace A • 1 - A := by
  rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The adjugate as a linear map on `2 × 2` matrices over a commutative ring. -/
noncomputable def adjugateFinTwoLinearMap :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  (Matrix.traceLinearMap (Fin 2) K K).smulRight (1 : Matrix (Fin 2) (Fin 2) K) -
    LinearMap.id

/-- Applying `adjugateFinTwoLinearMap` computes the ordinary matrix adjugate. -/
@[simp] theorem adjugateFinTwoLinearMap_apply (A : Matrix (Fin 2) (Fin 2) K) :
    adjugateFinTwoLinearMap A = Matrix.adjugate A := by
  simp [adjugateFinTwoLinearMap, adjugate_fin_two_eq_trace_smul_one_sub]

/-- Adjugation followed by conjugate transpose, as a real-algebra endomorphism of complex
`2 × 2` matrices. -/
noncomputable def starAdjugateFinTwoAlgHom :
    Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun A := star (Matrix.adjugate A)
  map_zero' := by
    rw [← Matrix.adjugateFinTwoLinearMap_apply, map_zero, star_zero]
  map_add' A B := by
    rw [← Matrix.adjugateFinTwoLinearMap_apply, map_add,
      Matrix.adjugateFinTwoLinearMap_apply, Matrix.adjugateFinTwoLinearMap_apply, star_add]
  map_one' := by simp
  map_mul' A B := by simp [Matrix.adjugate_mul_distrib, star_mul]
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.algebraMap_eq_smul_one] <;> ring

/-- Applying `starAdjugateFinTwoAlgHom` computes the conjugate transpose of the adjugate. -/
theorem starAdjugateFinTwoAlgHom_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    starAdjugateFinTwoAlgHom A = star (Matrix.adjugate A) := by rfl

/-- An anti-multiplicative function with scalar translates sends an off-diagonal unit
to its negative. -/
private theorem map_single_eq_neg_of_ne {R : Type*} [NonAssocRing R]
    (f : Matrix (Fin 2) (Fin 2) R → Matrix (Fin 2) (Fin 2) R)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : R, A + f A = r • 1)
    (i j : Fin 2) (hij : i ≠ j) :
    f (Matrix.single i j 1) = -(Matrix.single i j 1) := by
  obtain ⟨r, hr⟩ := hscalar (Matrix.single i j 1)
  obtain ⟨s, hs⟩ := hscalar (Matrix.single j i 1)
  obtain ⟨t, ht⟩ := hscalar (Matrix.single i i 1)
  have hf := eq_sub_of_add_eq' hr
  have hg := eq_sub_of_add_eq' hs
  have hd := eq_sub_of_add_eq' ht
  have hp := hmul (Matrix.single i j 1) (Matrix.single j i 1)
  simp only [single_mul_single_same, mul_one] at hp
  rw [hf, hg, hd] at hp
  have hr0 : r = 0 := by
    have h := congrArg (fun A => A j i) hp
    simpa [sub_mul, mul_sub, smul_one_eq_diagonal, hij, Ne.symm hij] using h
  simp [hf, hr0, smul_one_eq_diagonal]

/-- An anti-multiplicative function for which every matrix plus its image is scalar
is adjugation. No additivity or homogeneity assumption is needed. -/
theorem eq_adjugate_of_antimultiplicative_of_exists_add_eq_smul_one
    (f : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1)
    (A : Matrix (Fin 2) (Fin 2) K) : f A = adjugate A := by
  obtain ⟨r, hr⟩ := hscalar A
  have hf := eq_sub_of_add_eq' hr
  obtain ⟨s, hs⟩ := hscalar (A * Matrix.single 0 1 1)
  have hp := hmul A (Matrix.single 0 1 1)
  rw [map_single_eq_neg_of_ne f hmul hscalar 0 1 (by decide),
    eq_sub_of_add_eq' hs, hf] at hp
  have h : -A 0 0 = -r + A 1 1 := by
    simpa [neg_mul, mul_sub] using congrArg (fun B => B 0 1) hp
  have hr : r = trace A := by
    rw [trace_fin_two]
    apply neg_injective
    simpa [neg_add, sub_eq_add_neg, add_assoc, add_comm] using
      (congrArg (· - A 1 1) h).symm
  rw [hf, hr, adjugate_fin_two_eq_trace_smul_one_sub]

end Matrix
