/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The strict Cauchy–Schwarz inequality

In an inner product space over `ℝ` or `ℂ`, the Cauchy–Schwarz inequality `‖⟪a, b⟫‖ ≤ ‖a‖ ‖b‖` is
strict exactly when `a` is nonzero and `b` is not a multiple of `a`
(`TauCeti.norm_inner_lt_norm_iff`; for real inner products in terms of the absolute value,
`TauCeti.abs_real_inner_lt_norm_iff`).
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {a b : E}

/-- **Strict Cauchy–Schwarz.** `‖⟪a, b⟫‖ < ‖a‖ ‖b‖` exactly when `a` is nonzero and `b` is not a
multiple of `a`. -/
theorem norm_inner_lt_norm_iff :
    ‖inner 𝕜 a b‖ < ‖a‖ * ‖b‖ ↔ a ≠ 0 ∧ ∀ c : 𝕜, b ≠ c • a := by
  have h : ‖inner 𝕜 a b‖ = ‖a‖ * ‖b‖ ↔ a = 0 ∨ ∃ c : 𝕜, b = c • a :=
    (norm_inner_eq_norm_tfae 𝕜 a b).out 1 3
  rw [(norm_inner_le_norm a b).lt_iff_ne, ne_eq, h, not_or, not_exists]

end RCLike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {a b : E}

/-- **Strict Cauchy–Schwarz** for a real inner product: `|⟪a, b⟫| < ‖a‖ ‖b‖` exactly when `a` is
nonzero and `b` is not a multiple of `a`. -/
theorem abs_real_inner_lt_norm_iff :
    |⟪a, b⟫| < ‖a‖ * ‖b‖ ↔ a ≠ 0 ∧ ∀ c : ℝ, b ≠ c • a := by
  rw [← Real.norm_eq_abs, norm_inner_lt_norm_iff]

end TauCeti
