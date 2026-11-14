/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The strict Cauchy–Schwarz inequality

In a real inner product space, the Cauchy–Schwarz inequality `|⟪a, b⟫| ≤ ‖a‖ ‖b‖` is strict
exactly when `b` is not a multiple of the nonzero vector `a`
(`abs_real_inner_lt_norm_mul_norm_iff`).
-/

public section

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {a b : E}

/-- **Strict Cauchy–Schwarz.** For a nonzero vector `a`, `|⟪a, b⟫| < ‖a‖ ‖b‖` exactly when `b` is
not a multiple of `a`. -/
theorem abs_real_inner_lt_norm_mul_norm_iff (ha : a ≠ 0) :
    |⟪a, b⟫| < ‖a‖ * ‖b‖ ↔ ∀ c : ℝ, b ≠ c • a := by
  refine ⟨fun h c hc ↦ ?_, fun h ↦ ?_⟩
  · subst hc
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, abs_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖a‖)] at h
    exact (h.trans_eq (by ring)).false
  · have hb : b ≠ 0 := by simpa using h 0
    refine (abs_real_inner_le_norm a b).lt_of_ne fun heq ↦ ?_
    rw [← Real.norm_eq_abs] at heq
    obtain ⟨c, -, hc⟩ := (norm_inner_eq_norm_iff ha hb).1 heq
    exact h c hc
