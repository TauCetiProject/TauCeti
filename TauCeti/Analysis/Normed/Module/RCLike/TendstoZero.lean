/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Factoring a null family over `ℝ` or `ℂ`

A family tending to zero in a normed space over `𝕜 = ℝ` or `ℂ` is the product of a scalar family
and a vector family that both tend to zero. Taking square roots of the norms splits the decay
evenly between the two factors.

## Main statements

* `TauCeti.exists_smul_eq_of_tendsto_zero`: a null family is a null scalar family times a null
  vector family.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A family tending to zero is the product of a scalar family and a vector family that both
tend to zero. -/
theorem exists_smul_eq_of_tendsto_zero {ι : Type*} {l : Filter ι} {x : ι → E}
    (hx : Tendsto x l (𝓝 0)) :
    ∃ r : ι → 𝕜, Tendsto r l (𝓝 0) ∧ ∃ w : ι → E, Tendsto w l (𝓝 0) ∧ ∀ i, r i • w i = x i := by
  -- Take `r i = √‖x i‖` and `w i = (r i)⁻¹ • x i`; both have norm `√‖x i‖`.
  have hsqrt : Tendsto (fun i ↦ √‖x i‖) l (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_zero_iff_norm_tendsto_zero.mp hx)
    rwa [Real.sqrt_zero] at this
  have hnorm (i : ι) : ‖((√‖x i‖ : ℝ) : 𝕜)⁻¹ • x i‖ = √‖x i‖ := by
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_mul_eq_div, Real.div_sqrt]
  refine ⟨fun i ↦ ((√‖x i‖ : ℝ) : 𝕜), ?_, fun i ↦ ((√‖x i‖ : ℝ) : 𝕜)⁻¹ • x i, ?_, fun i ↦ ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hnorm] using hsqrt
  · rcases eq_or_ne (√‖x i‖) 0 with h | h
    · simp_all
    · exact smul_inv_smul₀ (RCLike.ofReal_ne_zero.mpr h) _

end TauCeti
