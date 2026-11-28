/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Cover.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

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
* `TauCeti.Manifold.OrientationCover.continuous_mk_of_forall_exists_map_mfderiv_eq`: the same
  when each point has a neighbourhood with such a chart.
-/

public section

open Bundle Set Topology Module
open scoped Manifold ContDiff

namespace TauCeti.Manifold.OrientationCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {e : OpenPartialHomeomorph M E}

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
    refine ((continuousOn_mk_mfderiv_chart_symm he (b i)).mono hS).domRestrict.congr fun y ↦ ?_
    simp only [v, domRestrict_apply]
    exact congrArg _ (mfderiv_chart_symm_apply_eq_symm_apply he (hS y.property) (L y) (hLc y) (b i))
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

/-- **Orientations read locally through charts.** Let `o y` be an orientation of `T_y M` for each
`y ∈ S`. If every point of `S` has a neighbourhood `U` and a chart `e` of the `C¹` maximal atlas,
defined on `S ∩ U`, whose derivative carries `o y` to one fixed orientation of the model space for
all `y ∈ S ∩ U`, then `y ↦ (y, o y)` is continuous as a map from `S` to the orientation double
cover. -/
theorem continuous_mk_of_forall_exists_map_mfderiv_eq {S : Set M}
    (o : ∀ y : S, _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, E) (y : M)) (Fin (finrank ℝ E)))
    (ho : ∀ y₀ : S, ∃ U ∈ 𝓝 (y₀ : M), ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M,
      S ∩ U ⊆ e.source ∧ ∃ O : _root_.Orientation ℝ E (Fin (finrank ℝ E)), ∀ y : S, (y : M) ∈ U →
        ∀ L : TangentSpace 𝓘(ℝ, E) (y : M) ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (e y),
          (L : TangentSpace 𝓘(ℝ, E) (y : M) →L[ℝ] _) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y →
            Orientation.map _ (L.toLinearEquiv : TangentSpace 𝓘(ℝ, E) (y : M) ≃ₗ[ℝ] E) (o y) =
              O) :
    Continuous fun y : S ↦ (⟨y, o y⟩ : OrientationCover 𝓘(ℝ, E) M) := by
  refine continuous_iff_continuousAt.2 fun y₀ ↦ ?_
  obtain ⟨U, hU, e, he, hS, O, hO⟩ := ho y₀
  obtain ⟨V, hVU, hV, hy₀V⟩ := mem_nhds_iff.1 hU
  -- On the open set `S ∩ V` the chart `e` reads `o` as the fixed orientation `O`.
  have hG := continuous_mk_of_map_mfderiv_eq he (S := S ∩ V)
    (fun z hz ↦ hS ⟨hz.1, hVU hz.2⟩) O (fun z ↦ o ⟨z, z.property.1⟩)
    fun z ↦ hO ⟨z, z.property.1⟩ (hVU z.property.2)
  refine ContinuousOn.continuousAt ?_ ((hV.preimage continuous_subtypeVal).mem_nhds hy₀V)
  rw [continuousOn_iff_continuous_domRestrict]
  exact hG.comp (f := fun y : {y : S | (y : M) ∈ V} ↦
    (⟨y.val.val, y.val.property, y.property⟩ : (S ∩ V : Set M))) (by fun_prop)

end TauCeti.Manifold.OrientationCover
