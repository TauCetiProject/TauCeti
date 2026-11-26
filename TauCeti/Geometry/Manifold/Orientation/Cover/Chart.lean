/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Cover.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Orientations read through a chart

Let `e` be a chart of the `C¹` maximal atlas of a manifold `M` modelled on a finite-dimensional
real space `E`. Its derivative identifies each tangent space `T_y M`, for `y` in the source of
`e`, with `E`. This file shows that a family of orientations of the tangent spaces which all read
as one fixed orientation `O` of `E` through these derivatives is continuous as a map into the
orientation double cover of `M`
(`TauCeti.Manifold.OrientationCover.continuous_mk_of_map_mfderiv_eq`). Such a family is the
orientation of `M` that the chart pulls back from `O`, restricted to a subset of the source, so it
is a local section of the cover.

The family is the orientation of the bases obtained by pushing a fixed basis of `E` through the
derivative of the inverse chart, up to the deck involution. The derivative of the inverse chart is
continuous in the tangent bundle, since the inverse chart is `C¹`, so these bases vary
continuously and their orientations form a continuous map to the cover
(`TauCeti.VectorBundleOrientationCover.continuous_mk_basis_orientation`).

This is how continuity of orientations defined by a geometric construction, such as the
orientations of the tangent spaces along the unstable manifold of a critical point given by a
frame and its normal coordinates, is checked: one reads them in a chart in which the construction
becomes constant.

## Main results

* `TauCeti.Manifold.OrientationCover.continuous_mk_of_map_mfderiv_eq`: orientations read as a
  fixed orientation through a chart form a continuous map to the orientation double cover.
-/

public section

open Bundle Set Topology Module
open scoped Manifold ContDiff

namespace TauCeti.Manifold.OrientationCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {e : OpenPartialHomeomorph M E}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) 1 M] in
/-- The derivative of the inverse of a chart of the `C¹` maximal atlas, at the image of a point
of the source, inverts the derivative of the chart. -/
private theorem mfderiv_symm_apply_eq (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) {y : M}
    (hy : y ∈ e.source) (L : TangentSpace 𝓘(ℝ, E) y ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (e y))
    (hL : (L : TangentSpace 𝓘(ℝ, E) y →L[ℝ] _) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y)
    (v : TangentSpace 𝓘(ℝ, E) (e y)) :
    L.symm v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e y) v := by
  have h := e.mfderiv_symm_apply_mfderiv_apply hy
    ((contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero |>.mdifferentiableAt
      (e.open_source.mem_nhds hy))
    ((contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero |>.mdifferentiableAt
      (e.open_target.mem_nhds (e.map_source hy))) (L.symm v)
  rw [← hL, ContinuousLinearEquiv.coe_coe, L.apply_symm_apply] at h
  exact h.symm

omit [FiniteDimensional ℝ E] in
/-- Along the source of a chart of the `C¹` maximal atlas, the vector of `T_y M` which the chart
reads as a fixed vector `v` of `E` varies continuously in the tangent bundle. -/
private theorem continuousOn_mk_mfderiv_symm (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    (v : E) :
    ContinuousOn (fun y ↦ (⟨y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e y) v⟩ : TangentBundle 𝓘(ℝ, E) M))
      e.source := by
  -- The derivative of the inverse chart is continuous over its open target.
  have hT : ContinuousOn (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm)
      (π E (TangentSpace 𝓘(ℝ, E)) ⁻¹' e.target) := by
    refine (ContMDiffOn.continuousOn_tangentMapWithin (contMDiffOn_symm_of_mem_maximalAtlas he)
      le_rfl e.open_target.uniqueMDiffOn).congr fun p hp ↦ ?_
    exact (tangentMapWithin_eq_tangentMap (e.open_target.uniqueMDiffOn _ hp)
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero
        |>.mdifferentiableAt (e.open_target.mem_nhds hp))).symm
  have hin : ContinuousOn (fun y ↦ (⟨e y, v⟩ : TangentBundle 𝓘(ℝ, E) E)) e.source :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.comp_continuousOn
      (e.continuousOn.prodMk continuousOn_const)
  refine (hT.comp hin fun y hy ↦ e.map_source hy).congr fun y hy ↦ ?_
  simp only [Function.comp_apply, tangentMap]
  exact TotalSpace.ext (e.left_inv hy).symm (by rw [e.left_inv hy])

/-- **Orientations read through a chart.** Let `e` be a chart of the `C¹` maximal atlas, `S` a
subset of its source and `o y` an orientation of `T_y M` for each `y ∈ S`. If the derivative of
`e` at every `y ∈ S` carries `o y` to one fixed orientation `O` of the model space, then
`y ↦ (y, o y)` is continuous as a map from `S` to the orientation double cover. -/
theorem continuous_mk_of_map_mfderiv_eq (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    {S : Set M} (hS : S ⊆ e.source) (O : _root_.Orientation ℝ E (Fin (finrank ℝ E)))
    (o : ∀ y : S, _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, E) (y : M)) (Fin (finrank ℝ E)))
    (ho : ∀ (y : S) (L : TangentSpace 𝓘(ℝ, E) (y : M) ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (e y)),
      (L : TangentSpace 𝓘(ℝ, E) (y : M) →L[ℝ] _) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y →
        Orientation.map _ (L.toLinearEquiv : TangentSpace 𝓘(ℝ, E) (y : M) ≃ₗ[ℝ] E) (o y) = O) :
    Continuous fun y : S ↦ (⟨y, o y⟩ : OrientationCover 𝓘(ℝ, E) M) := by
  have hL (y : S) := isInvertible_mfderiv_chart he (hS y.property)
  let L (y : S) := (hL y).choose
  have hLc (y : S) : (L y : TangentSpace 𝓘(ℝ, E) (y : M) →L[ℝ] TangentSpace 𝓘(ℝ, E) (e y)) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y :=
    (hL y).choose_spec
  let b := Module.finBasis ℝ E
  -- The basis of `T_y M` read as `b` through the chart.
  let v (y : S) : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace 𝓘(ℝ, E) (y : M)) :=
    b.map (L y).symm.toLinearEquiv
  have hv : Continuous fun y : S ↦
      (⟨y, (v y).orientation⟩ : OrientationCover 𝓘(ℝ, E) M) := by
    refine VectorBundleOrientationCover.continuous_mk_basis_orientation continuous_subtypeVal v
      fun i ↦ ?_
    refine ((continuousOn_mk_mfderiv_symm he (b i)).mono hS).domRestrict.congr fun y ↦ ?_
    simp only [v, domRestrict_apply]
    exact congrArg _ (mfderiv_symm_apply_eq he (hS y.property) (L y) (hLc y) (b i)).symm
  -- The orientation `o y` is `O` pulled back through the chart, and `O = ± b.orientation`.
  have ho' (y : S) : o y = Orientation.map _ (L y).symm.toLinearEquiv O := by
    rw [← ho y (L y) (hLc y), ← Orientation.map_trans]
    simp
  have hvo (y : S) : (v y).orientation = Orientation.map _ (L y).symm.toLinearEquiv b.orientation :=
    Basis.orientation_map _ _
  rcases O.eq_or_eq_neg b.orientation (by simp) with hO | hO
  · refine hv.congr fun y ↦ ?_
    rw [hvo, ho', hO]
  · refine (VectorBundleOrientationCover.deck.continuous.comp hv).congr fun y ↦ ?_
    simp only [Function.comp_apply, VectorBundleOrientationCover.deck_apply]
    rw [hvo, ho', hO]
    exact congrArg (fun o ↦ (⟨y, o⟩ : OrientationCover 𝓘(ℝ, E) M)) (Orientation.map_neg _ _).symm

end TauCeti.Manifold.OrientationCover
