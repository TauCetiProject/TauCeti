/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

/-!
# Change of chart for rough differential forms

The coordinate expression of a rough form in two overlapping preferred charts is related by the
pullback along the coordinate change.  This is the chart-independence bridge for the manifold
exterior derivative: Mathlib's flat pullback theorem then transports `extDerivWithin` between the
expressions.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace RoughForm

/-- On an overlap of two preferred charts, a rough form read in the first chart is the pullback of
its expression in the second chart by the coordinate change. -/
theorem inChartAt_eq_compContinuousLinearMap [IsManifold I 1 M]
    (φ : RoughForm I M F k) {x₀ x : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) :
    φ.inChartAt x₀ z =
      (φ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z))).compContinuousLinearMap
        (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) := by
  let y : M := (extChartAt I x₀).symm z
  let q : E := extChartAt I x y
  have hq : q ∈ (extChartAt I x).target := (extChartAt I x).map_source hx
  have hpre : (extChartAt I x₀).symm ⁻¹' (extChartAt I x).source ∈ 𝓝[range I] z := by
    exact (continuousAt_extChartAt_symm'' hz).continuousWithinAt.preimage_mem_nhdsWithin
      (extChartAt_source_mem_nhds' hx)
  have hcoord :
      ((extChartAt I x).symm ∘
        (extChartAt I x ∘ (extChartAt I x₀).symm)) =ᶠ[𝓝[range I] z]
        (extChartAt I x₀).symm := by
    filter_upwards [hpre] with a ha
    exact (extChartAt I x).left_inv ha
  have hcomp :
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x).symm ∘
        (extChartAt I x ∘ (extChartAt I x₀).symm)) (range I) z =
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) q).comp
          (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
            (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) := by
    apply mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
      (I' := 𝓘(ℝ, E)) (I'' := I) (u := range I) z
    · exact mdifferentiableWithinAt_extChartAt_symm hq
    · exact ((contDiffWithinAt_ext_coord_change (𝕜 := ℝ) (n := 1) x x₀ (by
        rw [PartialEquiv.trans_source]
        exact ⟨by simpa only [PartialEquiv.symm_source] using hz, hx⟩)).differentiableWithinAt
          (by simp)).mdifferentiableWithinAt
    · filter_upwards [hpre] with a ha
      exact extChartAt_target_subset_range x ((extChartAt I x).map_source ha)
    · exact I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range x₀ hz)
        |>.uniqueMDiffWithinAt
    -- The composition sends `z` to the chart point `q` by the definition of `q`.
    · rfl
  have hderiv :
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) q).comp
          (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) =
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z := by
    have hcomp' := hcomp
    have hpoint :
        ((extChartAt I x).symm ∘
          (extChartAt I x ∘ (extChartAt I x₀).symm)) z =
          (extChartAt I x₀).symm z := by
      -- `left_inv` is stated for the partial equivalence, so expose the composition.
      change (extChartAt I x).symm ((extChartAt I x) ((extChartAt I x₀).symm z)) =
        (extChartAt I x₀).symm z
      exact (extChartAt I x).left_inv hx
    rw [hcoord.mfderivWithin_eq hpoint] at hcomp'
    rw [mfderivWithin_eq_fderivWithin] at hcomp'
    -- The model-space tangent identifications are canonical but not definitionally transparent.
    change _ = _ at hcomp'
    exact hcomp'.symm
  ext v
  rw [inChartAt_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    inChartAt_apply]
  have hxy :
      (extChartAt I x).symm ((extChartAt I x) ((extChartAt I x₀).symm z)) =
        (extChartAt I x₀).symm z :=
    (extChartAt I x).left_inv hx
  rw [hxy]
  congr 1
  funext i
  exact congrArg (fun L ↦ L (v i)) hderiv.symm

/-- The exterior derivative of a rough form's coordinate expression is transported by a change of
preferred chart.  This is the chart-independence statement behind `mextDerivWithin`. -/
theorem extDerivWithin_inChartAt_eq [IsManifold I 2 M]
    (φ : RoughForm I M F k) {x₀ x : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source)
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x) (range I)
      (extChartAt I x ((extChartAt I x₀).symm z))) :
    extDerivWithin (φ.inChartAt x₀) (range I) z =
      (extDerivWithin (φ.inChartAt x) (range I)
        (extChartAt I x ((extChartAt I x₀).symm z))).compContinuousLinearMap
          (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) := by
  have hzr : z ∈ range I := extChartAt_target_subset_range x₀ hz
  have heq : φ.inChartAt x₀ =ᶠ[𝓝[range I] z] fun ζ ↦
      (φ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm ζ))).compContinuousLinearMap
        (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) ζ) := by
    have h₁ : (extChartAt I x₀).target ∈ 𝓝[range I] z :=
      extChartAt_target_mem_nhdsWithin_of_mem hz
    have h₂ : (extChartAt I x₀).symm ⁻¹' (extChartAt I x).source ∈ 𝓝[range I] z :=
      (continuousAt_extChartAt_symm'' hz).continuousWithinAt.preimage_mem_nhdsWithin
        (extChartAt_source_mem_nhds' hx)
    filter_upwards [h₁, h₂] with ζ hζ hζx
    exact φ.inChartAt_eq_compContinuousLinearMap hζ hζx
  rw [heq.extDerivWithin_eq (heq.self_of_nhdsWithin hzr)]
  refine extDerivWithin_pullback (r := 2) hφ
    (contDiffWithinAt_ext_coord_change x x₀ ?_) (by simp) I.uniqueDiffOn
      (I.range_subset_closure_interior hzr) hzr ?_
  · rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨by simpa only [PartialEquiv.symm_source] using hz, hx⟩
  · intro ζ hζ
    exact ⟨chartAt H x ((extChartAt I x₀).symm ζ), rfl⟩

end RoughForm

end TauCeti
