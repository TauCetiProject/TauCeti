/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Postcomposition on `Lᵖ` by continuous linear equivalences

Mathlib's `ContinuousLinearMap.compLpL` postcomposes `Lp E p μ` classes with a continuous linear
map. For a continuous linear equivalence `e : E ≃L[𝕜] F`, postcomposition with `e` and with
`e.symm` are mutually inverse, which gives the continuous linear equivalence
`ContinuousLinearEquiv.compLpL e p μ : Lp E p μ ≃L[𝕜] Lp F p μ`. It is the counterpart for
continuous linear equivalences of `LinearIsometryEquiv.compLpₗᵢ`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ContinuousLinearEquiv

variable {α 𝕜 E F : Type*} {_ : MeasurableSpace α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (e : E ≃L[𝕜] F) (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)

/-- Postcomposing `Lᵖ` classes with a continuous linear equivalence `e : E ≃L[𝕜] F`, bundled as a
continuous linear equivalence `Lp E p μ ≃L[𝕜] Lp F p μ` with inverse postcomposition with
`e.symm`. -/
def compLpL : Lp E p μ ≃L[𝕜] Lp F p μ :=
  .ofContinuousLinearMap ((e : E →L[𝕜] F).compLpL p μ) ((e.symm : F →L[𝕜] E).compLpL p μ)
    (by rw [ContinuousLinearMap.compLpL_comp_compLpL, e.coe_comp_coe_symm,
      ContinuousLinearMap.id_compLpL])
    (by rw [ContinuousLinearMap.compLpL_comp_compLpL, e.coe_symm_comp_coe,
      ContinuousLinearMap.id_compLpL])

/-- As a continuous linear map, `e.compLpL p μ` is `ContinuousLinearMap.compLpL` of `e`. -/
@[simp]
theorem coe_compLpL : (e.compLpL p μ : Lp E p μ →L[𝕜] Lp F p μ) = (e : E →L[𝕜] F).compLpL p μ :=
  (rfl)

/-- Applied to `u`, `e.compLpL p μ` is `ContinuousLinearMap.compLpL` of `e` applied to `u`. -/
@[simp]
theorem compLpL_apply (u : Lp E p μ) : e.compLpL p μ u = (e : E →L[𝕜] F).compLpL p μ u :=
  (rfl)

/-- The inverse of `e.compLpL p μ` is postcomposition with `e.symm`. -/
@[simp]
theorem symm_compLpL : (e.compLpL p μ).symm = e.symm.compLpL p μ :=
  (rfl)

variable {e p μ}

/-- `e.compLpL p μ u` is almost everywhere `e ∘ u`. -/
theorem coeFn_compLpL (u : Lp E p μ) : e.compLpL p μ u =ᵐ[μ] fun a ↦ e (u a) :=
  (e : E →L[𝕜] F).coeFn_compLpL u

end ContinuousLinearEquiv
