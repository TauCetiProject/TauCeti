/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Manifold derivatives of continuous-linear-map applications

This file records a local-calculus fact for vector-valued maps on manifolds: at a zero of a
vector-valued map, the derivative of a varying continuous linear map applied to that map has no
contribution from the varying operator.

The zero-value formula is the manifold counterpart of `HasFDerivAt.clm_apply`, specialized to
the case used when differentiating changes of fiber coordinates at the zero of a bundle section.
-/

public section

open Set
open scoped Manifold

variable {𝕜 E H M F F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {x : M}

namespace TauCeti

/-- At a zero of `u`, differentiating `y ↦ c y (u y)` only differentiates `u`; the derivative
of the varying continuous linear map `c` is multiplied by `u x = 0`. -/
theorem mvfderiv_clm_apply_of_eq_zero {c : M → F →L[𝕜] F'} {u : M → F}
    (hc : MDifferentiableAt I 𝓘(𝕜, F →L[𝕜] F') c x)
    (hu : MDifferentiableAt I 𝓘(𝕜, F) u x) (hu0 : u x = 0) :
    mvfderiv I (fun y ↦ c y (u y)) x = (c x).comp (mvfderiv I u x) := by
  rw [(hc.clm_apply hu).mvfderiv]
  apply ContinuousLinearMap.ext
  intro v
  have hfun : writtenInExtChartAt I 𝓘(𝕜, F') x (fun y ↦ c y (u y)) =
      fun z ↦ (writtenInExtChartAt I 𝓘(𝕜, F →L[𝕜] F') x c z)
        (writtenInExtChartAt I 𝓘(𝕜, F) x u z) := by
    funext z
    simp [writtenInExtChartAt, extChartAt, chartAt_self_eq]
  rw [hfun, fderivWithin_clm_apply]
  · have hcval :
        writtenInExtChartAt I 𝓘(𝕜, F →L[𝕜] F') x c (extChartAt I x x) = c x := by
      simp [writtenInExtChartAt, extChartAt, chartAt_self_eq]
    have huval : writtenInExtChartAt I 𝓘(𝕜, F) x u (extChartAt I x x) = u x := by
      simp [writtenInExtChartAt, extChartAt, chartAt_self_eq]
    rw [hcval, huval, hu0]
    simp only [map_zero, add_zero]
    rw [hu.mvfderiv]
    -- `MDifferentiableAt.mvfderiv` states the chart formula with the derivative's domain
    -- `TangentSpace I x` read as the model space `E`; Mathlib implements this identification
    -- definitionally (see the TODO before that lemma), so the two sides agree by `rfl`.
    rfl
  · exact I.uniqueDiffWithinAt_image
  · exact hc.differentiableWithinAt_writtenInExtChartAt
  · exact hu.differentiableWithinAt_writtenInExtChartAt

end TauCeti

end
