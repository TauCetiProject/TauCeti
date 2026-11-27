/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.Module

/-!
# Strictly accretive complex matrices

A complex square matrix is strictly accretive if `A + Aᴴ` is positive definite. Such a matrix
is invertible and is congruent to a diagonal matrix with entries in the open right half-plane.

The definition, invertibility and congruence arguments adapt the formalization in grh-lean,
`src/Lib/General/Analysis/GaussianIntegral.lean` (see
`TauCeti.Analysis.SpecialFunctions.Gaussian.Accretive.Basic` for provenance).
-/

public section

open Complex CStarAlgebra
open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {ι : Type*} {A : Matrix ι ι ℂ}

/-- A complex square matrix `A` is strictly accretive if `A + Aᴴ` is positive definite. -/
def IsStrictlyAccretive (A : Matrix ι ι ℂ) : Prop := (A + Aᴴ).PosDef

/-- Strict accretivity is equivalent to positive definiteness of `A + Aᴴ`. -/
theorem isStrictlyAccretive_iff_posDef : A.IsStrictlyAccretive ↔ (A + Aᴴ).PosDef := Iff.rfl

/-- Every positive definite complex matrix is strictly accretive. -/
theorem PosDef.isStrictlyAccretive (hA : A.PosDef) : A.IsStrictlyAccretive :=
  isStrictlyAccretive_iff_posDef.mpr (hA.add hA.conjTranspose)

/-- Every strictly accretive matrix has nonzero determinant. -/
theorem IsStrictlyAccretive.det_ne_zero [Fintype ι] [DecidableEq ι] (hA : A.IsStrictlyAccretive) :
    A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv_ne, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A)).mpr hdet
  have hpos : 0 < star v ⬝ᵥ (A + Aᴴ) *ᵥ v :=
    (isStrictlyAccretive_iff_posDef.mp hA).dotProduct_mulVec_pos hv_ne
  have hzero : star v ⬝ᵥ (A + Aᴴ) *ᵥ v = 0 := by
    rw [add_mulVec, dotProduct_add, hv, dotProduct_zero, zero_add, mulVec_conjTranspose,
      dotProduct_star, ← dotProduct_mulVec, star_star, hv, dotProduct_zero, star_zero]
  exact hpos.ne' hzero

/-- A strictly accretive matrix `A` is congruent to a diagonal matrix whose entries have strictly
positive real part. -/
theorem IsStrictlyAccretive.exists_eq_conjTranspose_mul_diagonal_mul [Fintype ι] [DecidableEq ι]
    (hA : A.IsStrictlyAccretive) :
    ∃ (p : GL ι ℂ) (d : ι → ℂ),
      A = (p : Matrix ι ι ℂ)ᴴ * diagonal d * (p : Matrix ι ι ℂ) ∧ ∀ i : ι, 0 < (d i).re := by
  obtain ⟨b, hb_unit, hb : A + Aᴴ = star b * b⟩ :=
    isStrictlyPositive_iff_eq_star_mul_self.mp
      (isStrictlyAccretive_iff_posDef.mp hA).isStrictlyPositive
  lift b to GL ι ℂ using hb_unit with B
  set H : Matrix ι ι ℂ := star (B : Matrix ι ι ℂ)⁻¹ * imaginaryPart A * (B : Matrix ι ι ℂ)⁻¹
  have hH : H.IsHermitian := ((imaginaryPart A).prop.conjugate' B⁻¹).isHermitian
  set U : Matrix ι ι ℂ := ↑hH.eigenvectorUnitary
  have h_spectral : U * diagonal (ofReal ∘ hH.eigenvalues) * star U = H := by
    simpa using hH.spectral_theorem.symm
  let d : ι → ℂ := fun i ↦ I * hH.eigenvalues i + 2⁻¹
  have hd : diagonal d = I • diagonal (ofReal ∘ hH.eigenvalues) + (2⁻¹ : ℂ) • 1 := by
    simp [smul_one_eq_diagonal, ← diagonal_smul, d]
  refine ⟨Unitary.toUnits hH.eigenvectorUnitary⁻¹ * B, d, ?_, by simp [d]⟩
  calc
    A = I • (imaginaryPart A : Matrix ι ι ℂ) + (2⁻¹ : ℂ) • (A + Aᴴ) := by
      rw [imaginaryPart_apply_coe, smul_smul, mul_neg, I_mul_I, neg_neg, star_eq_conjTranspose]
      module
    _ = star (B : Matrix ι ι ℂ) * (I • H + (2⁻¹ : ℂ) • 1) * B := by
      simp [mul_add, add_mul, hb, H, ← mul_assoc, ← star_mul]
    _ = star (B : Matrix ι ι ℂ) * (U * diagonal d * star U) * B := by
      simp [hd, mul_add, add_mul, h_spectral, U]
    _ = _ := by simp [U, star_eq_conjTranspose, mul_assoc]

end Matrix
