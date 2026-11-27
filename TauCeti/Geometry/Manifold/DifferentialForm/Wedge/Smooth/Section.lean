/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating.Wedge

/-!
# Wedge product under the smooth-form/section equivalence

This file relates `SmoothForm.wedge` to `ContMDiffSection.wedge` across
`TauCeti.SmoothForm.contMDiffSectionEquiv`.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  {k l : ℕ}

/-- `SmoothForm.contMDiffSectionEquiv.symm` intertwines `ContMDiffSection.wedge` with
`SmoothForm.wedge`. -/
@[simp]
theorem contMDiffSectionEquiv_symm_wedge
    (φ : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^∞⟮I; E [⋀^Fin l]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    contMDiffSectionEquiv.symm (φ.wedge ψ) =
      wedge (contMDiffSectionEquiv.symm φ) (contMDiffSectionEquiv.symm ψ) := by
  refine toContMDiffSection_injective ?_
  ext x v
  simp only [toContMDiffSection_apply, contMDiffSectionEquiv_symm_apply,
    ContMDiffSection.wedge_apply, coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply']

end TauCeti.SmoothForm
