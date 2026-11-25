/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Cuntz.Projection

/-!
# Checks for Cuntz subequivalence of projections in `M₂(ℂ)`

In `M₂(ℂ)` the matrix unit `v = e₂₁` has `v⋆v = e₁₁ = diag(1, 0)` and `vv⋆ = e₂₂ = diag(0, 1)`,
so `diag(1, 0) ≼ diag(0, 1)` by the flip, and the two projections are mutually Cuntz
subequivalent (CStarClassification CL4.1, Checks).
-/

public section

open scoped ComplexOrder

namespace TauCeti.CuntzProjectionExample

/-- The matrix unit `eᵢⱼ` of `M₂(ℂ)`. -/
noncomputable abbrev e (i j : Fin 2) : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix (Matrix.single i j 1)

theorem star_e (i j : Fin 2) : star (e i j) = e j i := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [e, CStarMatrix.star_apply]

theorem e_mul_e (i j k : Fin 2) : e i j * e j k = e i k := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [e, CStarMatrix.mul_apply, Matrix.single_apply]

theorem isStarProjection_e (i : Fin 2) : IsStarProjection (e i i) :=
  ⟨(e_mul_e i i i), star_e i i⟩

/-- `diag(1, 0) ≼ diag(0, 1)` in `M₂(ℂ)`, by the flip `v = e₂₁`. -/
theorem cuntzLE_e₁₁_e₂₂ :
    CuntzLE ⟨e 0 0, (isStarProjection_e 0).nonneg⟩ ⟨e 1 1, (isStarProjection_e 1).nonneg⟩ :=
  cuntzLE_of_star_mul_self_eq_of_mul_star_self_le (isStarProjection_e 0) (isStarProjection_e 1)
    (v := e 1 0) (by rw [star_e, e_mul_e]) (by rw [star_e, e_mul_e])

/-- `diag(1, 0)` and `diag(0, 1)` are mutually Cuntz subequivalent in `M₂(ℂ)`. -/
theorem antisymmRel_cuntzLE_e₁₁_e₂₂ :
    AntisymmRel CuntzLE (⟨e 0 0, (isStarProjection_e 0).nonneg⟩ :
      {a : CStarMatrix (Fin 2) (Fin 2) ℂ // 0 ≤ a}) ⟨e 1 1, (isStarProjection_e 1).nonneg⟩ :=
  antisymmRel_cuntzLE_of_star_mul_self_eq_of_mul_star_self_eq (isStarProjection_e 0)
    (isStarProjection_e 1) (v := e 1 0) (by rw [star_e, e_mul_e]) (by rw [star_e, e_mul_e])

end TauCeti.CuntzProjectionExample
