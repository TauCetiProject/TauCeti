/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Manifold derivatives of continuous-linear-map applications

This file records a local-calculus fact for vector-valued maps on manifolds: at a zero of a
vector-valued map `u`, the derivative of a varying continuous linear map `c` applied to `u` has
no contribution from the varying operator. Since that contribution is multiplied by `u = 0`, the
operator `c` need only be continuous, not differentiable.

The zero-value formula is the manifold counterpart of `HasFDerivAt.clm_apply`, specialized to
the case used when differentiating changes of fiber coordinates at the zero of a bundle section.
It is stated for any map agreeing with `y ↦ c y (u y)` near the point, which is how fiber
coordinates in two trivializations are related.
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

/-- The normed-space form of the zero-value rule: at a zero of `u`, the variation of `c` is
multiplied by `u y = O(y - z)`, so it contributes nothing to the derivative. -/
private theorem hasFDerivWithinAt_clm_apply_of_eq_zero {c : E → F →L[𝕜] F'} {u : E → F}
    {u' : E →L[𝕜] F} {s : Set E} {z : E}
    (hc : ContinuousWithinAt c s z) (hu : HasFDerivWithinAt u u' s z) (hu0 : u z = 0) :
    HasFDerivWithinAt (fun y ↦ c y (u y)) ((c z).comp u') s z := by
  have hrem : HasFDerivWithinAt (fun y ↦ (c y - c z) (u y)) (0 : E →L[𝕜] F') s z := by
    refine .of_isLittleO ?_
    simp only [hu0, map_zero, sub_self, sub_zero, zero_apply]
    refine (isBoundedBilinearMap_apply (𝕜 := 𝕜) (E := F) (F := F')).isBigO_comp.trans_isLittleO ?_
    have hc' : (fun y ↦ ‖c y - c z‖) =o[𝓝[s] z] (fun _ ↦ (1 : ℝ)) :=
      ((isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 hc)).norm_left
    have hu' : (fun y ↦ ‖u y‖) =O[𝓝[s] z] (fun y ↦ ‖y - z‖) := by
      simpa only [hu0, sub_zero] using hu.isBigO_sub.norm_norm
    exact isLittleO_norm_right.1 (by simpa only [one_mul] using hc'.mul_isBigO hu')
  convert ((c z).hasFDerivAt.comp_hasFDerivWithinAt z hu).add hrem using 1
  · funext y
    simp
  · simp

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
  have hD := hasFDerivWithinAt_clm_apply_of_eq_zero hc' hu' (by rwa [extChartAt_to_inv])
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

end TauCeti

end
