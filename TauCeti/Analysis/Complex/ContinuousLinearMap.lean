/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Conformal

/-!
# Complex-linear maps from real-linear maps

A continuous real-linear map between complex normed spaces is complex-linear if it commutes
with multiplication by `I`. This generalizes `ContinuousLinearMap.complexOfReal` from
`Mathlib.Analysis.Complex.Conformal` to arbitrary complex normed domains. The proof applies
the real and imaginary decomposition of a complex scalar, as in Mathlib's
`real_linearMap_map_smul_complex`, without needing norms or continuity for the algebraic step.
-/

public section

open Complex

namespace LinearMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E] [AddCommGroup F] [Module ℝ F] [Module ℂ F]
  [IsScalarTower ℝ ℂ F]

/-- A real-linear map commuting with multiplication by `I` commutes with every complex scalar. -/
theorem map_smul_complex_of_map_I_smul (L : E →ₗ[ℝ] F)
    (h : ∀ v, L (I • v) = I • L v) (c : ℂ) (v : E) : L (c • v) = c • L v := by
  have hc : c = algebraMap ℝ ℂ c.re + algebraMap ℝ ℂ c.im * I := (re_add_im c).symm
  rw [hc]
  simp only [add_smul, mul_smul, IsScalarTower.algebraMap_smul, L.map_add, L.map_smul, h]

end LinearMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Regard a continuous real-linear map commuting with multiplication by `I` as complex-linear. -/
def complexOfRealOfMapISmul (L : E →L[ℝ] F)
    (h : ∀ v, L (I • v) = I • L v) : E →L[ℂ] F where
  __ := L
  map_smul' := L.toLinearMap.map_smul_complex_of_map_I_smul h

/-- Changing the scalar field leaves the underlying function unchanged. -/
@[simp]
theorem coe_complexOfRealOfMapISmul (L : E →L[ℝ] F) (h) :
    ⇑(L.complexOfRealOfMapISmul h) = L := (rfl)

/-- Restricting the constructed complex-linear map back to real scalars recovers the input. -/
@[simp]
theorem restrictScalars_complexOfRealOfMapISmul (L : E →L[ℝ] F) (h) :
    (L.complexOfRealOfMapISmul h).restrictScalars ℝ = L := (rfl)

/-- Reconstructing a complex-linear map from its real scalar restriction recovers it. -/
@[simp]
theorem complexOfRealOfMapISmul_restrictScalars (L : E →L[ℂ] F) :
    (L.restrictScalars ℝ).complexOfRealOfMapISmul (fun v ↦ L.map_smul I v) = L := by
  ext v
  exact congrFun (coe_complexOfRealOfMapISmul (L.restrictScalars ℝ)
    (fun v ↦ L.map_smul I v)) v

end ContinuousLinearMap
