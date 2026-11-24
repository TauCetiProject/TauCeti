/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Real determinants of complex and real-linear maps

The real determinant of a real-linear endomorphism of the complex plane is the two-by-two
determinant of its values at `1` and `I` in the basis `(1,I)`.

The real determinant of a complex-linear endomorphism of a complex module is the squared modulus
of its complex determinant (`LinearMap.det_restrictScalars_eq_normSq`). In particular it is
nonnegative, and positive for complex-linear automorphisms; this is why complex-linear maps
preserve real orientations. On a finite-dimensional complex vector space it is positive exactly
for the injective complex-linear endomorphisms
(`LinearMap.det_restrictScalars_pos_iff_injective`).
-/

public section

namespace LinearMap

/-- The real determinant of a map on the complex plane, expressed in the basis `(1,I)`. -/
theorem det_complex (L : ℂ →ₗ[ℝ] ℂ) :
    L.det = (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]

/-- The real determinant of a complex-linear endomorphism is the squared modulus of its complex
determinant. -/
theorem det_restrictScalars_eq_normSq (f : E →ₗ[ℂ] E) :
    (f.restrictScalars ℝ).det = Complex.normSq f.det := by
  rw [det_restrictScalars, Algebra.norm_complex_apply]

/-- The real determinant of a complex-linear endomorphism is nonnegative. -/
theorem det_restrictScalars_nonneg (f : E →ₗ[ℂ] E) : 0 ≤ (f.restrictScalars ℝ).det := by
  rw [det_restrictScalars_eq_normSq]
  exact Complex.normSq_nonneg _

/-- A complex-linear endomorphism with nonzero complex determinant has positive real
determinant. -/
theorem det_restrictScalars_pos {f : E →ₗ[ℂ] E} (hf : f.det ≠ 0) :
    0 < (f.restrictScalars ℝ).det := by
  rw [det_restrictScalars_eq_normSq]
  exact Complex.normSq_pos.mpr hf

/-- A complex-linear endomorphism of a finite-dimensional complex vector space has positive real
determinant exactly when it is injective. -/
theorem det_restrictScalars_pos_iff_injective [Module.Finite ℂ E] {f : E →ₗ[ℂ] E} :
    0 < (f.restrictScalars ℝ).det ↔ Function.Injective f := by
  rw [det_restrictScalars_eq_normSq, Complex.normSq_pos, ne_eq, det_eq_zero_iff_ker_ne_bot,
    not_not, ker_eq_bot]

/-- Negating a real-linear endomorphism of a complex module does not change its real
determinant, because the real dimension is even. -/
theorem det_neg_of_complex (f : E →ₗ[ℝ] E) : (-f).det = f.det := by
  rw [← neg_one_smul ℝ f, det_smul, TauCeti.finrank_real_eq_two_mul_finrank_complex,
    (even_two_mul _).neg_one_pow, one_mul]

end LinearMap

namespace LinearEquiv

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]

/-- A complex-linear automorphism has positive real determinant. -/
theorem det_restrictScalars_pos (f : E ≃ₗ[ℂ] E) :
    0 < LinearMap.det (f.restrictScalars ℝ : E →ₗ[ℝ] E) :=
  LinearMap.det_restrictScalars_pos (f := (f : E →ₗ[ℂ] E)) f.isUnit_det'.ne_zero

end LinearEquiv
