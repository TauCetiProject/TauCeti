/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Derivatives of continuous-linear-map applications

This file records a zero-value rule for differentiating the pointwise application of a varying
continuous linear map. At a zero of the vector-valued argument, the variation of the operator
contributes nothing to the derivative, so the operator-valued map need only be continuous. It also
records the derivative of the application of a varying continuous linear map to a fixed vector.

## Main declarations

* `HasFDerivWithinAt.clm_apply_of_eq_zero`: the derivative of `y ↦ c y (u y)` at a zero of
  `u`, assuming only continuity of `c`.
* `TauCeti.fderiv_clm_apply_const_apply`: the derivative of `y ↦ c y v` in the direction `w` is
  `Dc(w) v`.
-/

public section

open Asymptotics Filter Set
open scoped Topology

variable {𝕜 E F F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

namespace TauCeti

/-- At a zero of `u`, the variation of `c` is multiplied by `u y = O(y - z)`, so it contributes
nothing to the derivative. -/
theorem _root_.HasFDerivWithinAt.clm_apply_of_eq_zero {c : E → F →L[𝕜] F'} {u : E → F}
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

/-- Differentiating `y ↦ c y v` for a fixed vector `v` in the direction `w` gives the derivative
of `c` in the direction `w`, applied to `v`. -/
theorem fderiv_clm_apply_const_apply {c : E → F →L[𝕜] F'} {x : E} (hc : DifferentiableAt 𝕜 c x)
    (v : F) (w : E) :
    fderiv 𝕜 (fun y ↦ c y v) x w = fderiv 𝕜 c x w v := by
  rw [fderiv_clm_apply hc (differentiableAt_const v)]
  simp

end TauCeti

end
