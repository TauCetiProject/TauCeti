/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Manifold derivatives of continuous-linear-map applications

This file records local-calculus facts for continuous-linear-map-valued maps on manifolds.

At a zero of a vector-valued map `u`, the derivative of a varying continuous linear map `c`
applied to `u` has no contribution from the varying operator. Since that contribution is
multiplied by `u = 0`, the operator `c` need only be continuous, not differentiable. On a normed
space, the imported theorem `HasFDerivWithinAt.clm_apply_of_eq_zero` is a variant of
`HasFDerivWithinAt.clm_apply` needing only continuity of `c`. The manifold formula
`mvfderiv_eq_comp_of_eventuallyEq_clm_apply` is its counterpart in charts, specialized to
the case used when differentiating changes of fiber coordinates at the zero of a bundle section.
It is stated for any map agreeing with `y ↦ c y (u y)` near the point, which is how fiber
coordinates in two trivializations are related.

It also records the manifold derivative of evaluating a differentiable family of continuous linear
maps at a fixed vector (`TauCeti.mvfderiv_clm_apply_const_apply`) and of evaluating a
differentiable family of bilinear maps at two fixed vectors
(`TauCeti.mvfderiv_clm_apply_const_apply₂`).

For maps on a normed space, it also records how `mvfderiv` acts on vectors given in the
model space through `NormedSpace.fromTangentSpace`: there it is the Fréchet derivative.
The precomposing continuous linear map may have any module equipped with a topology as its source.
-/

public section

open Asymptotics Filter Set
open scoped Manifold Topology

variable {𝕜 E H M F F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {x : M}

namespace TauCeti

/-- At a zero of `u`, a map agreeing near `x` with `y ↦ c y (u y)` has derivative `c x` composed
with the derivative of `u`: the variation of `c` is multiplied by `u x = 0`, so `c` need only be
continuous at `x`. -/
theorem mvfderiv_eq_comp_of_eventuallyEq_clm_apply {f : M → F'} {c : M → F →L[𝕜] F'}
    {u : M → F} (hf : (fun y ↦ c y (u y)) =ᶠ[𝓝 x] f) (hc : ContinuousAt c x)
    (hu : MDifferentiableAt I 𝓘(𝕜, F) u x) (hu0 : u x = 0) :
    mvfderiv I f x = (c x).comp (mvfderiv I u x) := by
  have hsymm : Tendsto (extChartAt I x).symm (𝓝[range I] extChartAt I x x) (𝓝 x) :=
    (map_extChartAt_symm_nhdsWithin_range x).le
  have hu' : HasFDerivWithinAt (fun z ↦ u ((extChartAt I x).symm z))
      (fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, F) x u) (range I) (extChartAt I x x))
      (range I) (extChartAt I x x) := by
    simpa [writtenInExtChartAt, extChartAt, chartAt_self_eq, Function.comp_def] using
      hu.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt
  have hc' : ContinuousWithinAt (fun z ↦ c ((extChartAt I x).symm z)) (range I)
      (extChartAt I x x) := by
    rw [ContinuousWithinAt, extChartAt_to_inv]
    exact hc.tendsto.comp hsymm
  have hD := hu'.clm_apply_of_eq_zero hc' (by rwa [extChartAt_to_inv])
  rw [extChartAt_to_inv] at hD
  have hfD : HasFDerivWithinAt (writtenInExtChartAt I 𝓘(𝕜, F') x f)
      ((c x).comp (fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, F) x u) (range I)
        (extChartAt I x x))) (range I) (extChartAt I x x) := by
    refine hD.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hsymm.eventually hf] with z hz
      simp only [writtenInExtChartAt, extChartAt, chartAt_self_eq] at hz ⊢
      simpa using hz.symm
    · simp [writtenInExtChartAt, extChartAt, chartAt_self_eq, hf.eq_of_nhds]
  have hmf : MDifferentiableAt I 𝓘(𝕜, F') f x :=
    (mdifferentiableAt_iff f x).2
      ⟨(hc.clm_apply hu.continuousAt).congr hf, hfD.differentiableWithinAt⟩
  rw [hmf.mvfderiv, hfD.fderivWithin I.uniqueDiffWithinAt_image]
  -- Both sides now read the derivative of `u` in the chart at `x`; Mathlib's
  -- `MDifferentiableAt.mvfderiv` is the identification of that chart derivative with `mvfderiv`.
  exact congrArg (c x).comp hu.mvfderiv.symm

/-- Differentiating `y ↦ c y v` on a manifold for a fixed vector `v` along a tangent vector `u`
gives the derivative of `c` along `u`, applied to `v`. -/
theorem mvfderiv_clm_apply_const_apply {c : M → F →L[𝕜] F'}
    (hc : MDifferentiableAt I 𝓘(𝕜, F →L[𝕜] F') c x) (v : F) (u : TangentSpace I x) :
    mvfderiv I (fun y ↦ c y v) x u = mvfderiv I c x u v := by
  have h := mvfderiv_comp_apply_of_differentiableAt
    (ContinuousLinearMap.apply 𝕜 F' v).differentiableAt hc u
  simpa only [Function.comp_def, ContinuousLinearMap.fderiv, ContinuousLinearMap.apply_apply]
    using h

/-- Differentiating `y ↦ c y v w` on a manifold for a field `c` of bilinear maps and fixed vectors
`v` and `w` along a tangent vector `u` gives the derivative of `c` along `u`, applied to `v` and
`w`. -/
theorem mvfderiv_clm_apply_const_apply₂ {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
    {c : M → F →L[𝕜] F' →L[𝕜] F''}
    (hc : MDifferentiableAt I 𝓘(𝕜, F →L[𝕜] F' →L[𝕜] F'') c x)
    (v : F) (w : F') (u : TangentSpace I x) :
    mvfderiv I (fun y ↦ c y v w) x u = mvfderiv I c x u v w := by
  rw [mvfderiv_clm_apply_const_apply (hc.clm_apply mdifferentiableAt_const),
    mvfderiv_clm_apply_const_apply hc]

/-- On a normed space, the vector-valued manifold derivative applied to model-space vectors
`L v`, viewed as tangent vectors via `NormedSpace.fromTangentSpace`, is the Fréchet derivative
applied to `L v`. No norm is required on the source of `L`. -/
theorem _root_.ContinuousLinearMap.mvfderiv_comp_fromTangentSpace_symm_comp {G : Type*}
    [TopologicalSpace G] [AddCommMonoid G] [Module 𝕜 G] {f : E → F} {z : E} (L : G →L[𝕜] E) :
    (mvfderiv 𝓘(𝕜, E) f z).comp
        ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) z).symm.toContinuousLinearMap.comp L) =
      (fderiv 𝕜 f z).comp L := by
  ext v
  simp

end TauCeti

end
