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
Mathlib's `real_linearMap_map_smul_complex` on each complex line.
-/

public section

open Complex

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A real-linear map commuting with multiplication by `I` commutes with every complex scalar. -/
theorem map_smul_complex_of_map_I_smul (L : E →L[ℝ] F)
    (h : ∀ v, L (I • v) = I • L v) (c : ℂ) (v : E) : L (c • v) = c • L v := by
  let l : ℂ →ₗ[ℝ] F := L.toLinearMap.comp
    ((LinearMap.toSpanSingleton ℂ E v).restrictScalars ℝ)
  have hl : l I = I • l 1 := by simpa [l] using h v
  simpa [l] using real_linearMap_map_smul_complex hl c 1

/-- Regard a continuous real-linear map commuting with multiplication by `I` as complex-linear. -/
def complexOfRealOfMapISmul (L : E →L[ℝ] F)
    (h : ∀ v, L (I • v) = I • L v) : E →L[ℂ] F where
  __ := L
  map_smul' := L.map_smul_complex_of_map_I_smul h

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
