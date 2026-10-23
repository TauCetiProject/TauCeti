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

If `z * ψ z` has a finite limit along a filter approaching infinity, then `ψ z` tends to zero.
If `ζ` tends to infinity, then so does the normalized coordinate `(ζ - c) / b`, for `b ≠ 0`; in
particular so does `(q + g⁻¹ - c) / b` when `g` tends to `0` without vanishing.
-/

public section

open Bornology Complex Filter Topology

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
