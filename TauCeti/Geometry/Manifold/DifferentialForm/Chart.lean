/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import TauCeti.Analysis.Calculus.DifferentialForm.Pullback
public import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential

/-!
# Change of chart for rough differential forms

The coordinate expression of a rough form in two overlapping preferred charts is related by the
pullback along the coordinate change. Exterior differentiation within a manifold subset obeys
the same transport law, provided the subset has unique derivatives and accumulates from its
interior at the point. Consequently, reading `mextDerivWithin` in any preferred chart gives the
flat exterior derivative of the coordinate expression. These identities allow naturality and
iteration of the exterior derivative to be checked in a fixed chart, including at boundary and
corner points. The unrestricted results are the specializations to the whole manifold.

The transport uses Mathlib's `extDerivWithin_pullback`, localized to the chart overlap.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
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

/-- Evaluating a chart expression at a chart image transports each argument through the
actual tangent coordinate change. -/
theorem inChartAt_chart_apply [IsManifold I 1 M]
    (φ : RoughForm I M F k) (α : M) {x : M}
    (hx : x ∈ (extChartAt I α).source) (v : Fin k → E) :
    φ.inChartAt α (extChartAt I α x) v =
      φ x (fun i ↦ tangentCoordChange I α x x (v i)) := by
  rw [RoughForm.inChartAt_apply]
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  rw [← TangentBundle.symmL_trivializationAt hx', TangentBundle.symmL_trivializationAt_eq_core hx']
  rw [(extChartAt I α).left_inv hx]
  rfl

/-- Two rough forms have the same coordinate expression at the chart image of a point of the
chart source exactly when they agree at that point. -/
theorem inChartAt_chart_eq_iff [IsManifold I 1 M] {φ η : RoughForm I M F k} {α x : M}
    (hx : x ∈ (extChartAt I α).source) :
    φ.inChartAt α (extChartAt I α x) = η.inChartAt α (extChartAt I α x) ↔ φ x = η x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hinv (w : E) : tangentCoordChange I α x x (tangentCoordChange I x α x w) = w := by
      rw [tangentCoordChange_comp ⟨⟨mem_extChartAt_source x, hx⟩, mem_extChartAt_source x⟩,
        tangentCoordChange_self (mem_extChartAt_source x)]
    ext v
    have hv := congrArg (fun A ↦ A fun i ↦ tangentCoordChange I x α x (v i)) h
    rw [inChartAt_chart_apply _ _ hx, inChartAt_chart_apply _ _ hx] at hv
    rwa [show (fun i ↦ tangentCoordChange I α x x (tangentCoordChange I x α x (v i))) = v from
      funext fun i ↦ hinv (v i)] at hv
  · ext v
    rw [inChartAt_chart_apply _ _ hx, inChartAt_chart_apply _ _ hx, h]

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

/-- Change of preferred chart for exterior differentiation within a manifold subset. The subset
has unique derivatives and accumulates from its interior at the point; it need not be open.
The derivative of the coordinate change is taken within the full model range. -/
theorem extDerivWithin_inChartAt_set_eq [IsManifold I 2 M]
    (φ : RoughForm I M F k) {s : Set M} (hs : UniqueMDiffOn I s) {x₀ x : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source)
    (hys : (extChartAt I x₀).symm z ∈ s)
    (hyc : (extChartAt I x₀).symm z ∈ closure (interior s))
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x)
      ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x ((extChartAt I x₀).symm z))) :
    extDerivWithin (φ.inChartAt x₀) ((extChartAt I x₀).symm ⁻¹' s ∩ range I) z =
      (extDerivWithin (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        (extChartAt I x ((extChartAt I x₀).symm z))).compContinuousLinearMap
          (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) := by
  -- Restrict to the chart target to obtain unique derivatives at every point of the set.
  -- The chart overlap is then imposed only as a neighbourhood condition at `z`.
  let a : Set E := (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' s
  let f : E → E := extChartAt I x ∘ (extChartAt I x₀).symm
  have ha : UniqueDiffOn ℝ a := hs.uniqueDiffOn_target_inter x₀
  have hza : z ∈ a := ⟨hz, hys⟩
  have hac : z ∈ closure (interior a) := by
    simpa only [a, inter_comm, (extChartAt I x₀).right_inv hz] using
      extChartAt_mem_closure_interior hyc ((extChartAt I x₀).map_target hz)
  have hcoord {ζ : E} (hζ : ζ ∈ (extChartAt I x₀).target)
      (hζx : (extChartAt I x₀).symm ζ ∈ (extChartAt I x).source) :
      ContDiffWithinAt ℝ 2 f (range I) ζ := by
    apply contDiffWithinAt_ext_coord_change x x₀
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨hζ, hζx⟩
  have hsource : (extChartAt I x₀).symm ⁻¹' (extChartAt I x).source ∈ 𝓝 z :=
    (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds (extChartAt_source_mem_nhds' hx)
  have hst : f ⁻¹' ((extChartAt I x).symm ⁻¹' s ∩ range I) ∈ 𝓝[a] z := by
    filter_upwards [nhdsWithin_le_nhds hsource, self_mem_nhdsWithin] with ζ hζx hζa
    exact ⟨by simpa only [f, mem_preimage, Function.comp_apply,
      (extChartAt I x).left_inv hζx] using hζa.2,
      extChartAt_target_subset_range x ((extChartAt I x).map_source hζx)⟩
  have hderiv {ζ : E} (hζ : ζ ∈ a)
      (hζx : (extChartAt I x₀).symm ζ ∈ (extChartAt I x).source) :
      fderivWithin ℝ f a ζ = fderivWithin ℝ f (range I) ζ :=
    fderivWithin_subset (fun _ h ↦ extChartAt_target_subset_range x₀ h.1) (ha ζ hζ)
      ((hcoord hζ.1 hζx).differentiableWithinAt (by norm_num))
  have hpull : φ.inChartAt x₀ =ᶠ[𝓝[a] z] fun ζ ↦
      (φ.inChartAt x (f ζ)).compContinuousLinearMap (fderivWithin ℝ f a ζ) := by
    filter_upwards [nhdsWithin_le_nhds hsource, self_mem_nhdsWithin] with ζ hζx hζa
    rw [hderiv hζa hζx]
    exact φ.inChartAt_eq_compContinuousLinearMap hζa.1 hζx
  have hset : a =ᶠ[𝓝 z] ((extChartAt I x₀).symm ⁻¹' s ∩ range I) := by
    filter_upwards [extChartAt_target_eventuallyEqSet_of_mem hz] with ζ hζ
    simp only [a, mem_inter_iff, hζ, and_comm]
  rw [← extDerivWithin_congr_set hset,
    hpull.extDerivWithin_eq (hpull.self_of_nhdsWithin hza)]
  rw [extDerivWithin_pullback_of_preimage_mem_nhdsWithin (f := f) (s := a) (x := z) hφ
    ((hcoord hz hx).mono (fun _ h ↦ extChartAt_target_subset_range x₀ h.1))
    (by norm_num) ha hac hza hst, hderiv hza hx]
  rfl

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
  simpa only [preimage_univ, univ_inter] using
    φ.extDerivWithin_inChartAt_set_eq (s := univ) (uniqueMDiffOn_univ (I := I)) hz hx
      (mem_univ _) (by simp) (by simpa only [preimage_univ, univ_inter] using hφ)

/-- Reading the manifold exterior derivative within a subset in any preferred chart gives the
flat exterior derivative of the coordinate expression within the corresponding coordinate set.
Only differentiability in the chart centred at the point is needed. -/
theorem inChartAt_mextDerivWithin [IsManifold I 2 M]
    (φ : RoughForm I M F k) {s : Set M} (hs : UniqueMDiffOn I s) {x₀ : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hys : (extChartAt I x₀).symm z ∈ s)
    (hyc : (extChartAt I x₀).symm z ∈ closure (interior s))
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt ((extChartAt I x₀).symm z))
      ((extChartAt I ((extChartAt I x₀).symm z)).symm ⁻¹' s ∩ range I)
      (extChartAt I ((extChartAt I x₀).symm z) ((extChartAt I x₀).symm z))) :
    RoughForm.inChartAt (I := I) (mextDerivWithin φ s) x₀ z =
      extDerivWithin (φ.inChartAt x₀) ((extChartAt I x₀).symm ⁻¹' s ∩ range I) z := by
  rw [inChartAt_eq_compContinuousLinearMap _ hz (mem_extChartAt_source _),
    inChartAt_extChartAt_self, mextDerivWithin_def]
  exact (φ.extDerivWithin_inChartAt_set_eq hs hz (mem_extChartAt_source _) hys hyc hφ).symm

/-- Reading the exterior derivative in any preferred chart gives the flat exterior derivative
within the model range. This includes boundary and corner chart points. -/
theorem inChartAt_mextDeriv [IsManifold I 2 M]
    (φ : RoughForm I M F k) {x₀ : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt ((extChartAt I x₀).symm z)) (range I)
      (extChartAt I ((extChartAt I x₀).symm z) ((extChartAt I x₀).symm z))) :
    (mextDeriv φ).inChartAt x₀ z = extDerivWithin (φ.inChartAt x₀) (range I) z := by
  simpa only [preimage_univ, univ_inter, mextDerivWithin_univ] using
    φ.inChartAt_mextDerivWithin (s := univ) (uniqueMDiffOn_univ (I := I)) hz (mem_univ _)
      (by simp) (by simpa only [preimage_univ, univ_inter] using hφ)

/-- The scalar coefficient of a manifold top form transforms by the signed Jacobian between
preferred charts, including derivatives taken within the model range at the boundary. -/
theorem inChartAt_apply_basis_eq_det_mul [IsManifold I 1 M] (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) {x₀ x : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) :
    φ.inChartAt x₀ z b =
      (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z).toLinearMap.det *
        φ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z)) b := by
  rw [φ.inChartAt_eq_compContinuousLinearMap hz hx,
    ContinuousAlternatingMap.compContinuousLinearMap_apply_basis]

end RoughForm

end TauCeti
