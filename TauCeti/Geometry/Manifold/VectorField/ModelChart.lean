/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Vector fields read in the charts of a manifold modelled on its own model space

Let `M` be a manifold modelled on a real normed space `E` with the trivial model `𝓘(ℝ, E)`. A vector
field `V` on `E` pulls back by a chart `e` of the maximal atlas to the field
`VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V` on the source of `e`. This file computes the chart
derivative of the pullback and the derivative of a function along it, and shows that it is smooth
when `V` is. The pullbacks of constant fields in the preferred chart give, near any regular point
of a smooth function, a smooth field along which the function strictly decreases.

## Main declarations

* `TauCeti.mfderiv_mpullback_apply`, `TauCeti.mvfderiv_mpullback_apply`,
  `TauCeti.contMDiffOn_mpullback`: the pullback of a vector field by a chart.
* `TauCeti.chartConstField`: a constant field in the preferred chart at a point, on the manifold.
* `TauCeti.exists_mem_nhds_mvfderiv_chartConstField_lt_zero`: near a regular point of a smooth
  function, some constant field in the preferred chart is a direction of strict decrease.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

section Pullback

variable {e : OpenPartialHomeomorph M E} {h : E → ℝ}

/-- The pullback `de_y⁻¹ (V (e y))` of a vector field `V` on the model space by a chart `e`. -/
theorem mfderiv_mpullback_apply (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (V : (z : E) → TangentSpace 𝓘(ℝ, E) z) {y : M} (hy : y ∈ e.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) = V (e y) := by
  rw [VectorField.mpullback_apply]
  exact (isInvertible_mfderiv_chart he hy).self_apply_inverse _

/-- The derivative of `f` along the pullback of a vector field `V` by a chart `e`, where
`f = h ∘ e` on the source of `e`. -/
theorem mvfderiv_mpullback_apply (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hfh : EqOn f (h ∘ e) e.source) (V : (z : E) → TangentSpace 𝓘(ℝ, E) z) {y : M}
    (hy : y ∈ e.source)
    (hh : DifferentiableAt ℝ h (e y)) :
    mvfderiv 𝓘(ℝ, E) f y (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) =
      fderiv ℝ h (e y) (V (e y)) := by
  -- `mvfderiv` composes `mfderiv` with `NormedSpace.fromTangentSpace`, which is the identity of
  -- `ℝ`, so the two agree definitionally; Mathlib has no rewrite lemma between them.
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) = _
  rw [mfderiv_eq_fderiv_comp_of_eqOn he hfh hy hh]
  exact congrArg (fderiv ℝ h (e y)) (mfderiv_mpullback_apply he V hy)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The pullback of a smooth vector field on the model space by a chart of the maximal atlas is
smooth on the source of the chart. -/
theorem contMDiffOn_mpullback (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {V : (z : E) → TangentSpace 𝓘(ℝ, E) z}
    (hV : ContDiffOn ℝ ∞ V e.target) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y⟩ : TangentBundle 𝓘(ℝ, E) M))
      e.source := by
  intro y hy
  have hVy : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun z ↦ (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) E)) (e y) :=
    contMDiffAt_vectorSpace_iff_contDiffAt.2
      ((hV (e y) (e.map_source hy)).contDiffAt (e.open_target.mem_nhds (e.map_source hy)))
  exact (ContMDiffAt.mpullback_vectorField_preimage hVy (contMDiffAt_of_mem_maximalAtlas he hy)
    (isInvertible_mfderiv_chart he hy) (by simp)).contMDiffWithinAt

end Pullback

section ConstField

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The constant vector field with value `v` on the model space. -/
noncomputable def constVectorField (v : E) : (z : E) → TangentSpace 𝓘(ℝ, E) z := fun _ ↦ v

variable (E) in
/-- The constant vector field with value `v` in the preferred chart at `p`, pulled back to the
manifold. -/
noncomputable def chartConstField (p : M) (v : E) : (y : M) → TangentSpace 𝓘(ℝ, E) y :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p) (constVectorField v)

omit [FiniteDimensional ℝ E] in
/-- A constant field in a chart is smooth on the source of the chart. -/
theorem contMDiffOn_chartConstField [FiniteDimensional ℝ E] (p : M) (v : E) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, chartConstField E p v y⟩ : TangentBundle 𝓘(ℝ, E) M)) (chartAt E p).source :=
  contMDiffOn_mpullback (IsManifold.chart_mem_maximalAtlas p) contDiffOn_const

omit [FiniteDimensional ℝ E] in
/-- Near a regular point of `f`, some constant field in the preferred chart is a direction of
strict decrease of `f`. -/
theorem exists_mem_nhds_mvfderiv_chartConstField_lt_zero (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    {y₀ : M} (hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0) :
    ∃ v : E, ∃ U ∈ 𝓝 y₀, U ⊆ (chartAt E y₀).source ∧
      ∀ y ∈ U, mvfderiv 𝓘(ℝ, E) f y (chartConstField E y₀ v y) < 0 := by
  set c := chartAt E y₀
  set h := f ∘ c.symm
  have hmem : y₀ ∈ c.source := mem_chart_source E y₀
  have hdiff : ∀ y ∈ c.source, DifferentiableAt ℝ h (c y) := fun y hy ↦
    ((contDiffOn_comp_chartAt_symm hf y₀).contDiffAt (c.open_target.mem_nhds
      (c.map_source hy))).differentiableAt (by simp)
  have hL : fderiv ℝ h (c y₀) ≠ 0 := fun h0 ↦ hcrit
    ((mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas y₀)
      (eqOn_comp_chartAt_symm y₀) hmem (hdiff y₀ hmem)).2 h0)
  obtain ⟨w, hw⟩ : ∃ w, fderiv ℝ h (c y₀) w ≠ 0 := by
    by_contra hno
    simp only [ne_eq, not_exists, not_not] at hno
    exact hL (ContinuousLinearMap.ext hno)
  obtain ⟨v, hv⟩ : ∃ v, fderiv ℝ h (c y₀) v < 0 := by
    rcases hw.lt_or_gt with hlt | hgt
    · exact ⟨w, hlt⟩
    · exact ⟨-w, by rw [map_neg]; linarith⟩
  have hcont : ContinuousAt (fun z ↦ fderiv ℝ h z v) (c y₀) :=
    (((contDiffOn_comp_chartAt_symm hf y₀).continuousOn_fderiv_of_isOpen c.open_target
      (by simp)).continuousAt (c.open_target.mem_nhds (c.map_source hmem))).clm_apply
      continuousAt_const
  have hev : ∀ᶠ y in 𝓝 y₀, fderiv ℝ h (c y) v < 0 :=
    (hcont.comp (c.continuousAt hmem)).eventually (gt_mem_nhds hv)
  refine ⟨v, {y | y ∈ c.source ∧ fderiv ℝ h (c y) v < 0},
    Filter.inter_mem (c.open_source.mem_nhds hmem) hev, fun y hy ↦ hy.1, fun y hy ↦ ?_⟩
  rw [chartConstField, mvfderiv_mpullback_apply (IsManifold.chart_mem_maximalAtlas y₀)
    (eqOn_comp_chartAt_symm y₀) _ hy.1 (hdiff y hy.1)]
  exact hy.2

end ConstField

end TauCeti
