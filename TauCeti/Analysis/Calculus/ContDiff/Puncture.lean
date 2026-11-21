/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# `C¹` regularity across a puncture

A function that is `C¹` on a punctured neighbourhood of a point, has a derivative at the point,
and whose derivative converges to it along the punctured neighbourhoods, is `C¹` at the point
(`TauCeti.contDiffAt_one_of_tendsto_fderiv`).

A map between normed spaces vanishing at `0` which is `O(‖x‖ ^ p)` on a punctured
neighbourhood of `0`, for some `p > 1`, is differentiable at `0` with derivative `0`
(`TauCeti.hasFDerivAt_zero_of_isBigO_rpow`), in particular under a global bound
`‖f x‖ ≤ C ‖x‖ ^ p` (`TauCeti.hasFDerivAt_zero_of_norm_rpow_bound`).
-/

public section

open Filter Topology Asymptotics

namespace TauCeti

section General

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {f' : E →L[𝕜] F} {x : E}

/-- A function that is `C¹` at every point of a punctured neighbourhood of `x`, has derivative
`f'` at `x`, and whose derivative tends to `f'` along the punctured neighbourhoods of `x`, is `C¹`
at `x`. -/
theorem contDiffAt_one_of_tendsto_fderiv (hf : ∀ᶠ y in 𝓝[≠] x, ContDiffAt 𝕜 1 f y)
    (hx : HasFDerivAt f f' x) (hlim : Tendsto (fderiv 𝕜 f) (𝓝[≠] x) (𝓝 f')) :
    ContDiffAt 𝕜 1 f x := by
  obtain ⟨u, hu, hfu⟩ := (eventually_nhdsWithin_iff.1 hf).exists_mem
  refine contDiffAt_one_iff.2 ⟨fderiv 𝕜 f, u, hu, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · rcases eq_or_ne y x with rfl | hyx
    · refine (continuousWithinAt_compl_self.1 ?_).continuousWithinAt
      rwa [ContinuousWithinAt, hx.fderiv]
    · exact ((hfu y hy hyx).fderiv_right (m := 0) le_rfl).continuousAt.continuousWithinAt
  · rcases eq_or_ne y x with rfl | hyx
    · rwa [hx.fderiv]
    · exact ((hfu y hy hyx).differentiableAt one_ne_zero).hasFDerivAt

/-- A map vanishing at zero which is `O(‖x‖ ^ p)` on a punctured neighbourhood of zero, for some
`p > 1`, has zero derivative there. Neither the source nor the target needs finite dimensionality
or completeness. -/
theorem hasFDerivAt_zero_of_isBigO_rpow {p : ℝ} (h0 : f 0 = 0)
    (hf : f =O[𝓝[≠] 0] fun x ↦ ‖x‖ ^ p) (hp : 1 < p) :
    HasFDerivAt f (0 : E →L[𝕜] F) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, h0, sub_zero, zero_apply]
  rw [← nhdsNE_sup_pure]
  refine IsLittleO.sup ?_ (isLittleO_pure.2 h0)
  -- `‖x‖ ^ p = ‖x‖ ^ (p - 1) * ‖x‖`, with `‖x‖ ^ (p - 1) → 0` and `‖x‖ = O(x)`
  have hsmall : (fun x : E ↦ ‖x‖ ^ (p - 1)) =o[𝓝[≠] 0] fun _ ↦ (1 : ℝ) := by
    refine (isLittleO_one_iff ℝ).2 ?_
    have hc : ContinuousAt (fun x : E ↦ ‖x‖ ^ (p - 1)) 0 :=
      continuousAt_id.norm.rpow_const (Or.inr (sub_pos.2 hp).le)
    simpa [Real.zero_rpow (sub_pos.2 hp).ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hsmall.mul_isBigO (isBigO_refl (fun x : E ↦ ‖x‖) (𝓝[≠] 0))
  refine hf.trans_isLittleO (hmul.congr' ?_ (Eventually.of_forall fun x ↦ one_mul _)
    |>.trans_isBigO (isBigO_norm_left.2 (isBigO_refl _ _)))
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [Real.rpow_sub_one hx'.ne', div_mul_cancel₀ _ hx'.ne']

/-- A map vanishing at zero with a norm bound of degree greater than one has zero derivative
there. Neither the source nor the target needs finite dimensionality or completeness. -/
theorem hasFDerivAt_zero_of_norm_rpow_bound {p C : ℝ} (h0 : f 0 = 0)
    (hb : ∀ x ≠ 0, ‖f x‖ ≤ C * ‖x‖ ^ p) (hp : 1 < p) :
    HasFDerivAt f (0 : E →L[𝕜] F) 0 :=
  hasFDerivAt_zero_of_isBigO_rpow h0 (IsBigO.of_bound C (eventually_nhdsWithin_of_forall
    fun x hx ↦ by rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) p)]; exact hb x hx))
    hp

end General

end TauCeti
