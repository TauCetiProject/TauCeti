/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The derivative of a vector field in a chart

Let `V` be a vector field on a manifold `M` modelled on `E`. Read in the extended chart `φ` at
`x`, it becomes the coordinate field `mpullback 𝓘(𝕜, E) I φ.symm V : E → E`, which on a
boundaryless manifold sends `φ p` to the image `dφ_p (V p)` of `V p` under the derivative of the
chart (`VectorField.mpullback_extChartAt_symm_apply_eq_mfderiv`). The *chart derivative* of `V` at
`x` (`TauCeti.vectorFieldChartDerivative`) is the Fréchet derivative of this coordinate field at
`φ x`, an endomorphism of `E`.

The coordinate fields `U` and `W` of `V` in two charts `φ` and `ψ` are related by
`W (ψ p) = T p (U (φ p))`, where `T p` is the derivative at `φ p` of the transition map
`ψ ∘ φ.symm` (`TauCeti.mpullback_extChartAt_symm_apply_eq_tangentCoordChange`). Away from the zeros
of `V` the derivatives of `U` and `W` are not conjugate, because the derivative of the right side
also involves the variation of `T` applied to `U (φ p)`. At a zero of `V` that term vanishes, so
the derivatives of `U` and `W` at the zero are conjugate by `T`
(`TauCeti.fderiv_mpullback_extChartAt_symm_of_eq_zero`); only the continuity of `T`, that is `C¹`
transition maps, is needed. In particular the determinant of the chart derivative at a zero, and
hence over `ℝ` its sign, the local index of a nondegenerate zero in the Poincaré–Hopf theorem, does
not depend on the chart (`TauCeti.det_fderiv_mpullback_extChartAt_symm_of_eq_zero`). These results
assume the manifold boundaryless, so that coordinate fields are differentiable on a neighbourhood
of the zero rather than only within the range of the model.

On a model space, with its trivial chart, the chart derivative is the Fréchet derivative of the
field (`TauCeti.vectorFieldChartDerivative_modelSpace`). For instance, on `ℝ` the fields `x ↦ x`
and `x ↦ -x` have chart derivatives `1` and `-1` at their zero, while `x ↦ x²` has chart
derivative `0`, so its isolated zero is degenerate.

## Main definitions

* `TauCeti.vectorFieldChartDerivative I V x`: the derivative at the chart image of `x` of the
  coordinate field of `V` in the extended chart at `x`.

## Main results

* `TauCeti.mpullback_extChartAt_symm_apply_eq_tangentCoordChange`: the coordinate fields in two
  charts are related by the derivative of the transition map.
* `TauCeti.hasFDerivAt_mpullback_extChartAt_symm_of_eq_zero`,
  `TauCeti.fderiv_mpullback_extChartAt_symm_of_eq_zero`: at a zero of `V`, the derivative of the
  coordinate field in another chart is the chart derivative conjugated by the derivative of the
  transition map.
* `TauCeti.det_fderiv_mpullback_extChartAt_symm_of_eq_zero`: at a zero of `V`, the determinant of
  the derivative of the coordinate field does not depend on the chart.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §6 (the index of a zero of a vector field and its independence of the chart).
-/

public section

open Set Filter VectorField
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]

variable (I) in
/-- The **chart derivative** of a vector field `V` at `x`: the Fréchet derivative, at the chart
image of `x`, of the coordinate field of `V` in the extended chart at `x`. At a zero of a field
differentiable there, on a boundaryless `C¹` manifold, its determinant does not depend on the
chart (`TauCeti.det_fderiv_mpullback_extChartAt_symm_of_eq_zero`). -/
noncomputable def vectorFieldChartDerivative (V : (x : M) → TangentSpace I x) (x : M) :
    E →ₗ[𝕜] E :=
  (fderiv 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V) (extChartAt I x x)).toLinearMap

/-- The chart derivative of `V` at `x` is the derivative of its coordinate field in the extended
chart at `x`. -/
theorem vectorFieldChartDerivative_def (V : (x : M) → TangentSpace I x) (x : M) :
    vectorFieldChartDerivative I V x =
      (fderiv 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V) (extChartAt I x x)).toLinearMap :=
  (rfl)

/-- On a model space, with its trivial chart, the chart derivative of a vector field is its
Fréchet derivative. -/
@[simp]
theorem vectorFieldChartDerivative_modelSpace (V : (x : E) → TangentSpace 𝓘(𝕜, E) x) (x : E) :
    vectorFieldChartDerivative 𝓘(𝕜, E) V x = (fderiv 𝕜 V x).toLinearMap := by
  rw [vectorFieldChartDerivative_def, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, mpullback_id, id_eq]

section Boundaryless

variable [IsManifold I 1 M] [I.Boundaryless]

/-- **The transformation law of coordinate fields.** On the overlap of the extended charts at `x₁`
and `x₂`, the coordinate field of `V` in the chart at `x₂` is the coordinate field in the chart at
`x₁` transported by the derivative of the transition map. -/
theorem mpullback_extChartAt_symm_apply_eq_tangentCoordChange (V : (x : M) → TangentSpace I x)
    {x₁ x₂ p : M} (h₁ : p ∈ (extChartAt I x₁).source) (h₂ : p ∈ (extChartAt I x₂).source) :
    mpullback 𝓘(𝕜, E) I (extChartAt I x₂).symm V (extChartAt I x₂ p) =
      tangentCoordChange I x₁ x₂ p
        (mpullback 𝓘(𝕜, E) I (extChartAt I x₁).symm V (extChartAt I x₁ p)) := by
  have h₁' : p ∈ (chartAt H x₁).source := by rwa [← extChartAt_source I]
  have h₂' : p ∈ (chartAt H x₂).source := by rwa [← extChartAt_source I]
  rw [mpullback_extChartAt_symm_apply_eq_mfderiv V h₁,
    mpullback_extChartAt_symm_apply_eq_mfderiv V h₂,
    (hasMFDerivAt_extChartAt h₁').mfderiv, (hasMFDerivAt_extChartAt h₂').mfderiv,
    mfderiv_chartAt_eq_tangentCoordChange h₁', mfderiv_chartAt_eq_tangentCoordChange h₂']
  exact (tangentCoordChange_comp ⟨⟨mem_extChartAt_source p, h₁⟩, h₂⟩).symm

variable {V : (x : M) → TangentSpace I x} {x x' : M}

/-- **Chart change at a zero of a vector field.** Let `V` be differentiable at a zero `x`, and let
`ψ` be the extended chart at `x'`, whose source contains `x`. Then the coordinate field of `V` in
`ψ` has, at `ψ x`, the derivative of the coordinate field in the chart at `x` conjugated by the
derivative of the transition map. -/
theorem hasFDerivAt_mpullback_extChartAt_symm_of_eq_zero
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x) (hV₀ : V x = 0)
    (hx : x ∈ (extChartAt I x').source) :
    HasFDerivAt (mpullback 𝓘(𝕜, E) I (extChartAt I x').symm V)
      (tangentCoordChange I x x' x ∘L
        fderiv 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V) (extChartAt I x x) ∘L
          tangentCoordChange I x' x x)
      (extChartAt I x' x) := by
  have hx' : x ∈ (chartAt H x').source := by rwa [← extChartAt_source I]
  -- The coordinate field in the chart at `x` is differentiable at the chart image of `x`, where it
  -- vanishes.
  have hU : DifferentiableAt 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V)
      (extChartAt I x x) := by
    have h := MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_extChartAt_symm
      (s := univ) hV.mdifferentiableWithinAt
    rw [I.range_eq_univ, mpullbackWithin_univ, preimage_univ, inter_univ] at h
    exact h.differentiableAt univ_mem
  have hU₀ : mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V (extChartAt I x x) = 0 := by
    rw [mpullback_extChartAt_symm_apply_eq_mfderiv V (mem_extChartAt_source x), hV₀]
    exact map_zero _
  -- The transition map to the chart at `x'` is `C¹` near the chart image of `x`, so its derivative
  -- is continuous there.
  have hB : ContinuousAt (fderiv 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm))
      (extChartAt I x x) := by
    have hmem : extChartAt I x x ∈ ((extChartAt I x).symm ≫ extChartAt I x').source := by
      simp [PartialEquiv.trans_source, hx']
    have h := contDiffWithinAt_ext_coord_change (n := 1) x' x hmem
    rw [I.range_eq_univ, contDiffWithinAt_univ] at h
    exact (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hBx : fderiv 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm) (extChartAt I x x) =
      tangentCoordChange I x x' x := by
    rw [tangentCoordChange_def, I.range_eq_univ, fderivWithin_univ]
  -- The transition map back to the chart at `x` has derivative `tangentCoordChange I x' x x`.
  have hg : HasFDerivAt (extChartAt I x ∘ (extChartAt I x').symm) (tangentCoordChange I x' x x)
      (extChartAt I x' x) := by
    have h := hasFDerivWithinAt_tangentCoordChange (I := I) (x := x') (y := x) (z := x)
      ⟨hx, mem_extChartAt_source x⟩
    rwa [I.range_eq_univ, hasFDerivWithinAt_univ] at h
  have hgx : (extChartAt I x ∘ (extChartAt I x').symm) (extChartAt I x' x) = extChartAt I x x := by
    rw [Function.comp_apply, (extChartAt I x').left_inv hx]
  -- Differentiating `y ↦ B y (U y)` at a zero of `U` kills the second-derivative term.
  have h₁ := (HasFDerivWithinAt.clm_apply_of_eq_zero hB.continuousWithinAt
    hU.hasFDerivAt.hasFDerivWithinAt hU₀).hasFDerivAt univ_mem
  rw [hBx, ← hgx] at h₁
  have h₂ := h₁.comp (extChartAt I x' x) hg
  rw [hgx] at h₂
  -- Near the chart image of `x`, the coordinate field in the chart at `x'` is the coordinate field
  -- in the chart at `x` transported by the derivative of the transition map.
  refine h₂.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_target_mem_nhds' (I := I) ((extChartAt I x').map_source hx),
    extChartAt_preimage_mem_nhds' hx (extChartAt_source_mem_nhds (I := I) x)] with z hz' hz
  obtain ⟨p, hp', rfl⟩ : ∃ p ∈ (extChartAt I x').source, extChartAt I x' p = z :=
    ⟨_, (extChartAt I x').map_target hz', (extChartAt I x').right_inv hz'⟩
  have hp : p ∈ (extChartAt I x).source := by
    simpa only [mem_preimage, (extChartAt I x').left_inv hp'] using hz
  have hBp : fderiv 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm) (extChartAt I x p) =
      tangentCoordChange I x x' p := by
    rw [tangentCoordChange_def, I.range_eq_univ, fderivWithin_univ]
  rw [Function.comp_apply, Function.comp_apply, (extChartAt I x').left_inv hp',
    mpullback_extChartAt_symm_apply_eq_tangentCoordChange V hp hp']
  simp only [hBp]

/-- **Chart change at a zero of a vector field.** At a zero `x` of a vector field `V`
differentiable at `x`, the derivative of the coordinate field of `V` in the extended chart at `x'`
is the derivative of the coordinate field in the chart at `x` conjugated by the derivative of the
transition map. -/
theorem fderiv_mpullback_extChartAt_symm_of_eq_zero
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x) (hV₀ : V x = 0)
    (hx : x ∈ (extChartAt I x').source) :
    fderiv 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I x').symm V) (extChartAt I x' x) =
      tangentCoordChange I x x' x ∘L
        fderiv 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V) (extChartAt I x x) ∘L
          tangentCoordChange I x' x x :=
  (hasFDerivAt_mpullback_extChartAt_symm_of_eq_zero hV hV₀ hx).fderiv

/-- **The determinant of the chart derivative at a zero is intrinsic.** At a zero `x` of a vector
field `V` differentiable at `x`, the derivative of the coordinate field of `V` in any extended chart
whose source contains `x` has the same determinant as the chart derivative of `V` at `x`. Over `ℝ`,
the sign of this determinant is the index of a nondegenerate zero. -/
theorem det_fderiv_mpullback_extChartAt_symm_of_eq_zero
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x) (hV₀ : V x = 0)
    (hx : x ∈ (extChartAt I x').source) :
    LinearMap.det
        (fderiv 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I x').symm V) (extChartAt I x' x) :
          E →ₗ[𝕜] E) =
      LinearMap.det (vectorFieldChartDerivative I V x) := by
  have hmem : x ∈ (extChartAt I x').source ∩ (extChartAt I x).source ∩ (extChartAt I x').source :=
    ⟨⟨hx, mem_extChartAt_source x⟩, hx⟩
  have hmem' : x ∈ (extChartAt I x).source ∩ (extChartAt I x').source ∩ (extChartAt I x).source :=
    ⟨⟨mem_extChartAt_source x, hx⟩, mem_extChartAt_source x⟩
  -- The derivatives of the two transition maps at `x` are mutually inverse.
  let e : E ≃ₗ[𝕜] E := LinearEquiv.ofLinearMap (f := (tangentCoordChange I x x' x : E →ₗ[𝕜] E))
    (g := (tangentCoordChange I x' x x : E →ₗ[𝕜] E))
    (LinearMap.ext fun v ↦ (tangentCoordChange_comp hmem).trans (tangentCoordChange_self hx))
    (LinearMap.ext fun v ↦ (tangentCoordChange_comp hmem').trans
      (tangentCoordChange_self (mem_extChartAt_source x)))
  rw [fderiv_mpullback_extChartAt_symm_of_eq_zero hV hV₀ hx, vectorFieldChartDerivative_def]
  exact LinearMap.det_conj _ e

end Boundaryless

end TauCeti
