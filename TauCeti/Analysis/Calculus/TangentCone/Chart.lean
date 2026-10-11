/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Analysis.Calculus.TangentCone.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Tangent cones of sets flattened by a differentiable chart

A set `S` that some chart `e` flattens onto a closed linear subspace `L` (in the sense of
`TauCeti.IsSliceChart`) has, at each of its points `y`, a tangent cone which is a linear
subspace: it is the preimage of `L` under the derivative of `e` at `y`. This identifies Mathlib's
intrinsic `tangentConeAt` with the tangent space read off any flattening chart, so a condition
stated with tangent cones, such as the transversality of two submanifolds, does not depend on the
charts used to verify it.

## Main results

* `OpenPartialHomeomorph.isInvertible_fderiv`: a chart that is
  differentiable at a point, with inverse differentiable at the image point, has an invertible
  derivative there.
* `TauCeti.IsSliceChart.tangentConeAt_eq_preimage`: the tangent cone of a set flattened onto a
  closed subspace is the preimage of that subspace under the derivative of the chart.
* `TauCeti.IsSliceChart.span_tangentConeAt_eq_comap`: hence the span of the tangent cone is that
  preimage, viewed as a subspace, and it has the dimension of the model subspace
  (`TauCeti.IsSliceChart.finrank_span_tangentConeAt`).
-/

public section

open Filter Set Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace OpenPartialHomeomorph

/-- A chart which is differentiable at a point of its source, and whose inverse is differentiable
at the image point, has an invertible derivative there. -/
theorem isInvertible_fderiv (e : OpenPartialHomeomorph E F) {y : E} (hy : y ∈ e.source)
    (he : DifferentiableAt 𝕜 e y) (hes : DifferentiableAt 𝕜 e.symm (e y)) :
    (fderiv 𝕜 e y).IsInvertible := by
  have hleft : (fderiv 𝕜 e.symm (e y)).comp (fderiv 𝕜 e y) = ContinuousLinearMap.id 𝕜 E :=
    (hes.hasFDerivAt.comp y he.hasFDerivAt).unique <|
      (hasFDerivAt_id y).congr_of_eventuallyEq (e.eventually_left_inverse hy)
  have hright : (fderiv 𝕜 e y).comp (fderiv 𝕜 e.symm (e y)) = ContinuousLinearMap.id 𝕜 F := by
    have hes' : HasFDerivAt e.symm (fderiv 𝕜 e.symm (e y)) (e y) := hes.hasFDerivAt
    have he' : HasFDerivAt e (fderiv 𝕜 e y) (e.symm (e y)) := by
      rw [e.left_inv hy]; exact he.hasFDerivAt
    exact (he'.comp (e y) hes').unique <|
      (hasFDerivAt_id (e y)).congr_of_eventuallyEq (e.eventually_right_inverse (e.map_source hy))
  exact _root_.ContinuousLinearMap.IsInvertible.of_inverse hright hleft

/-- A chart which is differentiable at a point of its source, and whose inverse is differentiable
at the image point, has a derivative represented by a continuous linear equivalence. -/
theorem exists_hasFDerivAt_of_chart (e : OpenPartialHomeomorph E F) {y : E} (hy : y ∈ e.source)
    (he : DifferentiableAt 𝕜 e y) (hes : DifferentiableAt 𝕜 e.symm (e y)) :
    ∃ A : E ≃L[𝕜] F, HasFDerivAt e (A : E →L[𝕜] F) y := by
  obtain ⟨A, hA⟩ := e.isInvertible_fderiv hy he hes
  exact ⟨A, hA ▸ he.hasFDerivAt⟩

end OpenPartialHomeomorph

namespace TauCeti

namespace IsSliceChart

variable {e : OpenPartialHomeomorph E F} {L : Submodule 𝕜 F} {S : Set E} {y : E}
  {A : E ≃L[𝕜] F}

/-- **The tangent cone of a flattened set.** If the chart `e` flattens `S` onto a closed linear
subspace `L` and has invertible derivative `A` at a point `y` of `S`, then the tangent cone of `S`
at `y` is `A⁻¹ L`. -/
theorem tangentConeAt_eq_preimage (h : IsSliceChart e (L : Set F) S) (hL : IsClosed (L : Set F))
    (hy : y ∈ e.source) (hyS : y ∈ S) (hA : HasFDerivAt e (A : E →L[𝕜] F) y) :
    tangentConeAt 𝕜 S y = A ⁻¹' L := by
  have hey : e y ∈ L := (h.mem_iff hy).1 hyS
  refine Subset.antisymm (fun v hv ↦ ?_) fun v hv ↦ ?_
  · rw [← tangentConeAt_inter_nhds (e.open_source.mem_nhds hy)] at hv
    have hmaps := hA.hasFDerivWithinAt.mapsTo_tangent_cone hv
    rw [← L.tangentConeAt_eq hL hey]
    refine tangentConeAt_mono ?_ hmaps
    rintro _ ⟨z, ⟨hzS, hz⟩, rfl⟩
    exact (h.mem_iff hz).1 hzS
  · have hyt : e y ∈ e.target := e.map_source hy
    have hAs : HasFDerivAt e.symm (A.symm : F →L[𝕜] E) (e y) :=
      e.hasFDerivAt_symm hyt (by rwa [e.left_inv hy])
    have hv' : A v ∈ tangentConeAt 𝕜 ((L : Set F) ∩ e.target) (e y) := by
      rw [tangentConeAt_inter_nhds (e.open_target.mem_nhds hyt), L.tangentConeAt_eq hL hey]
      exact hv
    have hmaps := hAs.hasFDerivWithinAt.mapsTo_tangent_cone hv'
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      e.left_inv hy] at hmaps
    refine tangentConeAt_mono ?_ hmaps
    rintro _ ⟨w, ⟨hwL, hw⟩, rfl⟩
    rw [h.mem_iff (e.map_target hw), e.right_inv hw]
    exact hwL

/-- The span of the tangent cone of a set flattened onto a closed subspace `L`, at a point where
the chart has invertible derivative `A`, is the subspace `A⁻¹ L`. -/
theorem span_tangentConeAt_eq_comap (h : IsSliceChart e (L : Set F) S)
    (hL : IsClosed (L : Set F)) (hy : y ∈ e.source) (hyS : y ∈ S)
    (hA : HasFDerivAt e (A : E →L[𝕜] F) y) :
    Submodule.span 𝕜 (tangentConeAt 𝕜 S y) = L.comap (A : E →ₗ[𝕜] F) := by
  rw [h.tangentConeAt_eq_preimage hL hy hyS hA]
  exact Submodule.span_eq (L.comap (A : E →ₗ[𝕜] F))

/-- The tangent space of a set flattened onto a closed subspace `L`, at a point where the chart has
invertible derivative, has the dimension of `L`. -/
theorem finrank_span_tangentConeAt (h : IsSliceChart e (L : Set F) S)
    (hL : IsClosed (L : Set F)) (hy : y ∈ e.source) (hyS : y ∈ S)
    (hA : HasFDerivAt e (A : E →L[𝕜] F) y) :
    Module.finrank 𝕜 (Submodule.span 𝕜 (tangentConeAt 𝕜 S y)) = Module.finrank 𝕜 L := by
  rw [h.span_tangentConeAt_eq_comap hL hy hyS hA]
  exact (Submodule.comap_equiv_eq_map_symm A.toLinearEquiv L) ▸
    LinearEquiv.finrank_map_eq A.symm.toLinearEquiv L

end IsSliceChart

end TauCeti
