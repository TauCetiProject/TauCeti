/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# Complex limits at infinity

For any `c : ℂ`, the reciprocal `((t : ℂ) * c)⁻¹` tends to zero as `t → ∞`.
If `z * ψ z` has a finite limit along a filter approaching infinity, then `ψ z` tends to zero.
If `ζ` tends to infinity, then so does the normalized coordinate `(ζ - c) / b`, for `b ≠ 0`; in
particular so does `(q + g⁻¹ - c) / b` when `g` tends to `0` without vanishing. The unit
direction `z / |z|` is asymptotically invariant under a fixed translation: the ratio of
`(z + a) / |z + a|` to `z / |z|` tends to one at infinity.
-/

public section

open Bornology Complex Filter Topology

namespace Complex

/-- For any `c : ℂ`, the reciprocal `((t : ℂ) * c)⁻¹` tends to `0` as `t → +∞`. -/
theorem tendsto_inv_ofReal_mul_atTop_zero (c : ℂ) :
    Tendsto (fun t : ℝ => ((t : ℂ) * c)⁻¹) atTop (𝓝 0) := by
  simpa using tendsto_inv_atTop_zero.ofReal.const_mul c⁻¹

end Complex

namespace TauCeti

/-- If `z * ψ z` has a finite limit at infinity, then `ψ z` tends to zero. -/
theorem tendsto_zero_of_tendsto_mul_cobounded {l : Filter ℂ} (hl : l ≤ cobounded ℂ)
    {ψ : ℂ → ℂ} {c : ℂ} (h : Tendsto (fun z => z * ψ z) l (𝓝 c)) :
    Tendsto ψ l (𝓝 0) := by
  have ht := h.mul ((tendsto_inv₀_cobounded (α := ℂ)).mono_left hl)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [(tendsto_inv₀_cobounded' (α := ℂ)).mono_left hl |>.eventually
    self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  field_simp

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
  filter_upwards [isBounded_singleton (x := (0 : ℂ))] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  have hsum : 1 + a * z⁻¹ = (z + a) / z := by field_simp
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz0
  rw [hsum, norm_div, ofReal_div]
  field_simp

/-- If `ζ` tends to infinity, then so does the normalized coordinate `(ζ - c) / b`, for `b ≠ 0`. -/
theorem tendsto_sub_div_of_tendsto_cobounded {α : Type*} {l : Filter α} {ζ : α → ℂ} {c b : ℂ}
    (hb : b ≠ 0) (hζ : Tendsto ζ l (cobounded ℂ)) :
    Tendsto (fun a => (ζ a - c) / b) l (cobounded ℂ) := by
  simpa [div_eq_mul_inv, Function.comp_def] using
    (tendsto_mul_right_cobounded (inv_ne_zero hb)).comp ((tendsto_sub_const_cobounded c).comp hζ)

/-- If `g` tends to `0` without vanishing, the normalized coordinate `(q + g⁻¹ - c) / b` of the
inverted point `q + g⁻¹` tends to infinity, for `b ≠ 0`. -/
theorem tendsto_cobounded_div_of_tendsto_nhdsNE_zero {α : Type*} {l : Filter α} {g : α → ℂ}
    {q c b : ℂ} (hb : b ≠ 0) (hg : Tendsto g l (𝓝[≠] 0)) :
    Tendsto (fun a => (q + (g a)⁻¹ - c) / b) l (cobounded ℂ) :=
  tendsto_sub_div_of_tendsto_cobounded hb
    ((tendsto_const_add_cobounded q).comp (tendsto_inv₀_nhdsNE_zero.comp hg))

end TauCeti

end
