/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Multipliers bounded by one in `L²`

Multiplying a function by a scalar factor of norm at most one almost everywhere does not increase
its squared `L²` norm: `∫ ‖f • ξ‖² ≤ ∫ ‖ξ‖²` (`TauCeti.integral_norm_smul_sq_le`). Applied to the
restriction of a measure to a set, this bounds the squared `L²` norm of a cut-off function `χ ξ`
on that set by that of `ξ`, for a cutoff `χ` with values in `[0, 1]`.
-/

public section

open MeasureTheory

namespace TauCeti

/-- A scalar factor of norm at most one almost everywhere does not increase the squared `L²`
norm: `∫ ‖f • ξ‖² ≤ ∫ ‖ξ‖²` whenever `‖ξ‖²` is integrable. -/
theorem integral_norm_smul_sq_le {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : α → 𝕜} {ξ : α → E}
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1) (hξ : Integrable (fun x ↦ ‖ξ x‖ ^ 2) μ) :
    ∫ x, ‖f x • ξ x‖ ^ 2 ∂μ ≤ ∫ x, ‖ξ x‖ ^ 2 ∂μ :=
  integral_mono_of_nonneg (.of_forall fun _ ↦ sq_nonneg _) hξ (hf.mono fun x hx ↦ by
    simp only [norm_smul, mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hx))

end TauCeti
