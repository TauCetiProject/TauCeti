/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import TauCeti.Analysis.CStarAlgebra.Cuntz.Projection

/-!
# Checks for Cuntz subequivalence of projections in `M₂(ℂ)`

In `M₂(ℂ)` the matrix unit `v = e₂₁` has `v⋆v = e₁₁ = diag(1, 0)` and `vv⋆ = e₂₂ = diag(0, 1)`,
so `diag(1, 0) ≼ diag(0, 1)` by the flip, and the two projections are mutually Cuntz
subequivalent.
-/

public section

open scoped ComplexOrder

open CStarMatrix

namespace TauCeti.CuntzProjectionExample

/-- `diag(1, 0) ≼ diag(0, 1)` in `M₂(ℂ)`, by the flip `v = e₂₁`. -/
theorem cuntzLE_e₁₁_e₂₂ :
    CuntzLE ⟨matrixUnit (0 : Fin 2) 0, (isStarProjection_matrixUnit 0).nonneg⟩
      ⟨matrixUnit (1 : Fin 2) 1, (isStarProjection_matrixUnit 1).nonneg⟩ :=
  cuntzLE_of_star_mul_self_eq_of_mul_star_self_le (isStarProjection_matrixUnit 0)
    (isStarProjection_matrixUnit 1) (v := matrixUnit 1 0) (by simp) (by simp)

/-- `diag(1, 0)` and `diag(0, 1)` are mutually Cuntz subequivalent in `M₂(ℂ)`. -/
theorem antisymmRel_cuntzLE_e₁₁_e₂₂ :
    AntisymmRel CuntzLE ⟨matrixUnit (0 : Fin 2) 0, (isStarProjection_matrixUnit 0).nonneg⟩
      ⟨matrixUnit (1 : Fin 2) 1, (isStarProjection_matrixUnit 1).nonneg⟩ :=
  antisymmRel_cuntzLE_of_star_mul_self_eq_of_mul_star_self_eq (isStarProjection_matrixUnit 0)
    (isStarProjection_matrixUnit 1) (v := matrixUnit 1 0) (by simp) (by simp)

end TauCeti.CuntzProjectionExample
