/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.TwoFormHermitianForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Tangent.CoordChange
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.CoordChange

/-!
# Continuity of the Hermitian form of a continuous two-form

Let `X` be a complex manifold modelled on `𝓘(ℂ, E)` and `α` a continuous real two-form on `X`.
The Hermitian forms `H_α(x)` (`TauCeti.twoFormHermitianForm`) act on different tangent spaces, so
to compare them near `x₀` we read them in the chart at `x₀`, through the tangent coordinate change
`B x` from the chart at `x₀` to the chart at `x`. In these coordinates `H_α(x)` is continuous at
`x₀`: `H_α(x)(B x u, B x v) → H_α(x₀)(u, v)`
(`TauCeti.IsSmoothForm.tendsto_twoFormHermitianForm_tangentCoordChange`). This follows from
continuity of `α` evaluated along converging tangent vectors (`TauCeti.IsSmoothForm.tendsto_apply`,
`TangentBundle.tendsto_mk_tangentCoordChange`), since the real and complex tangent coordinate
changes agree on chart overlaps.
-/

public section

open Complex Filter Topology Bundle
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) 1 X]

/-- **The Hermitian form of a continuous two-form, read in the chart at `x₀`, is continuous at
`x₀`**: `H_α(x)(B x u, B x v) → H_α(x₀)(u, v)`. -/
theorem IsSmoothForm.tendsto_twoFormHermitianForm_tangentCoordChange
    {α : RoughForm 𝓘(ℝ, E) X ℝ 2} (hα : IsSmoothForm 𝓘(ℝ, E) 0 α) (x₀ : X) (u v : E) :
    Tendsto (fun x ↦ twoFormHermitianForm E α x (tangentCoordChange 𝓘(ℂ, E) x₀ x x u)
      (tangentCoordChange 𝓘(ℂ, E) x₀ x x v)) (𝓝 x₀) (𝓝 (twoFormHermitianForm E α x₀ u v)) := by
  have hvec (w w' : E) : ∀ j, Tendsto (fun x ↦ (⟨x, ![tangentCoordChange 𝓘(ℂ, E) x₀ x x w,
      tangentCoordChange 𝓘(ℂ, E) x₀ x x w'] j⟩ : TangentBundle 𝓘(ℝ, E) X)) (𝓝 x₀)
      (𝓝 ⟨x₀, ![w, w'] j⟩) := by
    -- The real and complex tangent coordinate changes agree on the chart at `x₀`.
    have hB (w : E) : Tendsto (fun x ↦ (⟨x, tangentCoordChange 𝓘(ℂ, E) x₀ x x w⟩ :
        TangentBundle 𝓘(ℝ, E) X)) (𝓝 x₀) (𝓝 ⟨x₀, w⟩) := by
      refine (TangentBundle.tendsto_mk_tangentCoordChange x₀ w).congr' ?_
      filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with x hx
      rw [tangentCoordChange_modelWithCornersSelf_restrictScalars_apply ℝ (𝕜' := ℂ)
        ⟨hx, mem_chart_source E x⟩]
    intro j
    fin_cases j
    · exact hB w
    · exact hB w'
  have hre := hα.tendsto_apply tendsto_id (hvec u (I • v))
  have him := hα.tendsto_apply tendsto_id (hvec u v)
  simp only [map_smul, id] at hre
  simp only [twoFormHermitianForm_def, Complex.mk_eq_add_mul_I]
  exact ((continuous_ofReal.tendsto _).comp hre).add
    (((continuous_ofReal.tendsto _).comp him).mul_const I)

end TauCeti
