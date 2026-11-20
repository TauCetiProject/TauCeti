/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Complex limits at infinity

For any `c : ℂ`, the reciprocal `((t : ℂ) * c)⁻¹` tends to zero as `t → ∞`. The unit direction
`z / |z|` is asymptotically invariant under a fixed translation: the ratio of `(z + a) / |z + a|`
to `z / |z|` tends to one at infinity.

Limits at infinity that hold in any normed ring or field are in
`TauCeti.Analysis.Normed.Field.AtInfinity`.
-/

public section

open Bornology Filter Topology

namespace Complex

/-- For any `c : ℂ`, the reciprocal `((t : ℂ) * c)⁻¹` tends to `0` as `t → +∞`. -/
theorem tendsto_inv_ofReal_mul_atTop_zero (c : ℂ) :
    Tendsto (fun t : ℝ => ((t : ℂ) * c)⁻¹) atTop (𝓝 0) := by
  simpa using tendsto_inv_atTop_zero.ofReal.const_mul c⁻¹

/-- The unit direction `z / |z|` changes by a factor tending to one under a fixed translation:
`((z + a) / |z + a|) / (z / |z|) → 1` as `z` tends to infinity. -/
theorem tendsto_add_div_norm_add_div_div_norm (a : ℂ) :
    Tendsto (fun z : ℂ ↦ (z + a) / (‖z + a‖ : ℂ) / (z / (‖z‖ : ℂ))) (cobounded ℂ) (𝓝 1) := by
  -- The ratio is `g / |g|` for `g z = (z + a) / z = 1 + a z⁻¹`, which tends to one.
  have hg : Tendsto (fun z : ℂ ↦ 1 + a * z⁻¹) (cobounded ℂ) (𝓝 1) := by
    simpa using (tendsto_inv₀_cobounded.const_mul a).const_add 1
  have hcont : ContinuousAt (fun w : ℂ ↦ w / (‖w‖ : ℂ)) 1 :=
    continuousAt_id.div (continuous_ofReal.comp continuous_norm).continuousAt (by simp)
  have hlim := hcont.tendsto.comp hg
  simp only [norm_one, ofReal_one, div_one, Function.comp_def] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_cobounded 0] with z hz0
  have hsum : 1 + a * z⁻¹ = (z + a) / z := by field_simp
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz0
  rw [hsum, norm_div, ofReal_div]
  field_simp

end Complex

end
