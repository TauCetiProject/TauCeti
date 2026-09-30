/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Complex limits at infinity

If `z * ψ z` has a finite limit along a filter approaching infinity, then `ψ z` tends to zero.
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

end TauCeti

end
