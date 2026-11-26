/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Monotone additive endomorphisms of `ℝ`

A monotone additive endomorphism `f : ℝ →+ ℝ` is `ℝ`-linear: `f r = r * f 1`
(`AddMonoidHom.real_eq_mul_one`).
-/

public section

/-- A monotone additive map `ℝ →+ ℝ` is linear: `f r = r * f 1`. -/
theorem AddMonoidHom.real_eq_mul_one (f : ℝ →+ ℝ) (hf : Monotone f) (r : ℝ) :
    f r = r * f 1 := by
  have hrat (q : ℚ) : f q = (q : ℝ) * f 1 := by
    simpa [smul_eq_mul] using map_ratCast_smul f ℝ ℝ q (1 : ℝ)
  rcases (by simpa using hf zero_le_one : 0 ≤ f 1).eq_or_lt with h0 | hf1
  · obtain ⟨q₁, hq₁⟩ := exists_rat_lt r; obtain ⟨q₂, hq₂⟩ := exists_rat_gt r
    have h1 := hf hq₁.le; have h2 := hf hq₂.le; rw [hrat, ← h0, mul_zero] at h1 h2
    rw [← h0, mul_zero]; exact le_antisymm h2 h1
  · refine le_antisymm (le_of_not_gt fun hlt ↦ ?_) (le_of_not_gt fun hlt ↦ ?_)
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((lt_div_iff₀ hf1).mpr hlt)
      linarith [hf hq1.le, (lt_div_iff₀ hf1).mp hq2, hrat q]
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((div_lt_iff₀ hf1).mpr hlt)
      linarith [hf hq2.le, (div_lt_iff₀ hf1).mp hq1, hrat q]
